from z3 import *
import numpy as np
from complex import Complex, I
from ComplexVector import ComplexVector
import cmath
from QuantumReferencer import QuantumReferencer
import QuantumOps as qo


# Should move elsewhere
def oracle(N, f):
    mat = []
    for i in range(N):
        f_z = []
        for j in range(N):
            if j == i: f_z.append(1- 2*f(i))
            else: f_z.append(0)
        mat.append(f_z)
    return np.array(mat)

# TODO: Handling classical variables - new class?
# TODO: Add measurement or check highest prob
# TODO: Precondition/postcondition addition
# TODO: Handle 2-qubit gates/ops - quantum if-statements?
# TODO: Handle terms in functions e.g. phase(r+a)
# TODO: Handle reverse procedure
# TODO: Add checks/exceptions across the board

# Verification of:
# classical - functions that only have classical parameters
# const - preserves parameter ("read" only)
# lifted - fairly simple, classical operations only
# lifted = qfree + const params (almost classical, use for some oracles)
# qfree - no superpositions introduced, manipulation of variable definitions only - can act on superpositioned states?
# mfree - no measurement
# All qfree functions are mfree, {qfree functions} in {mfree functions} => measurement not qfree

# Measurement - needed?
# Restrict to a subset of Silq - no measurement
# Just read the "amplitude" and check which is highest
# State measurement in pre-/post-conditions
# SQIR-like - unitary version and measurement version

class QuantumChecker:
    def __init__(self, solver):
        self.solver = solver
        self.t = 0
        self.q_ref = QuantumReferencer()
        self.qs = []
        self.N = 0
        
    def state_token(self, time):
        return 't' + str(time) + '_qstate'

    def is_var(self, name):
        return self.q_ref(name)
        
# Quantum Operation and Handling
#     Initialises a new register
    def init_new_qreg(self, name, size, val=0):
        s = self.solver
        self.q_ref.add(name, size)
        new_N = 2**self.q_ref.get_total_size()

#         If no qubits are stored create some new ones and don't change the timer
        if self.qs == []:
            self.qs = self.qs + ComplexVector(self.state_token(self.t), 2**size)
            for i in range(2**size):
                q = self.qs[i]
                s.add(q == 0 + 0*I) if not(i == val) else s.add(q == 1 + 0*I)
#         If there are already qubits, need to change assignment to handle the value assignment
        else:
            old_N = self.N
            old_qs = self.qs
            
            new_qs = ComplexVector(self.state_token(self.t + 1), new_N)

            for i in range(new_N):
                q = new_qs[i]
#                 Check bit is same as bit in value
                if not((i >> self.q_ref.get_loc(name)) ^ (val)):
#                     Need to remove binary format characters and then the actual binary value
                    loc = int(bin(i)[2:].zfill(self.q_ref.get_total_size())[size:], 2)
                    old_q = self.qs[loc]
                    s.add(q.r == old_q.r)
                    s.add(q.i == old_q.i)
                else:
                    s.add(q == 0 + 0*I)
            self.t += 1
            self.qs = new_qs
        
        self.N = new_N
            
    def dup_qreg(self, dup_name, orig_name):
        s = self.solver
        size = self.q_ref.get_size(orig_name)
        self.q_ref.add(dup_name, size)
        
        new_N = 2**self.q_ref.get_total_size()
        old_N = self.N
        old_qs = self.qs

        new_qs = ComplexVector(self.state_token(self.t + 1), new_N)

        for i in range(new_N):
            q = new_qs[i]
#             Get bitstrings and compare
            i_str = bin(i)[2:].zfill(self.q_ref.get_total_size())
            orig_bitstr = i_str[len(i_str)-self.q_ref.get_loc(orig_name)-size:len(i_str)-self.q_ref.get_loc(orig_name)]
            dup_bitstr = i_str[:size]
            
            if orig_bitstr == dup_bitstr:
#                 Get location and map to appropriate bit
                loc = int(i_str[size:], 2)
                old_q = self.qs[loc]
                s.add(q.r == old_q.r)
                s.add(q.i == old_q.i)
            else:
                s.add(q == 0 + 0*I)
        self.t += 1
        self.qs = new_qs
            
    def apply_sing_op(self, U, name, i):
        q_loc = self.q_ref.get_loc(name, i)
        U_kron = np.identity(2) if not (q_loc == 0) else U
        for i in range(1, self.q_ref.get_total_size()):
            U_kron = np.kron(np.identity(2), U_kron) if not(i == q_loc) else np.kron(U, U_kron)
        self.apply_op(U_kron)
        
#     Need to check ctrl_q not >= size(name)-1
    def apply_cnot_to_reg(self, name, ctrl_i):
        if (ctrl_i >= self.q_ref.get_size(name) - 1):
            raise ValueError("Referenced address must be before final address")
        loc = self.q_ref.get_loc(name, ctrl_i)
        i = 1
        if not(loc == 0):
            U_kron = np.identity(2)
        else: 
            U_kron = qo.cnot
            i += 1

        while i < self.q_ref.get_total_size():
            if not (i == loc):
                U_kron = np.kron(np.identity(2), U_kron)
            else:
                U_kron = np.kron(qo.cnot, U_kron)
                i += 1
            i += 1
            
        self.apply_op(U_kron)
    
    def apply_ctrl(self, U, ctrl_name, ctrl_i, tgt_name, tgt_i, ctrl_state=1):
        ctrl_loc = self.q_ref.get_loc(ctrl_name, ctrl_i)
        tgt_loc = self.q_ref.get_loc(tgt_name, tgt_i)
        op_size = 2**self.q_ref.get_total_size()
        ctrl_op = np.identity(op_size, dtype=complex)
        N = 2**(ctrl_loc)
        M = 2**(tgt_loc)
        
        for row in range(0, op_size):
            if (ctrl_state and (row & (1 << ctrl_loc))) or (not (ctrl_state) and not (row & (1 << ctrl_loc))):
                if (row & (1<<tgt_loc)):
                    ctrl_op[row][row - M] = U[1][0]
                    ctrl_op[row][row] = U[1][1]
                else:
                    ctrl_op[row][row] = U[0][0]
                    ctrl_op[row][row + M] = U[0][1]
        self.apply_op(ctrl_op)
        
    def apply_H(self, name, i):
        sqrt2 = Real('sqrt2')
        self.solver.add([sqrt2**2 == 2, sqrt2 > 0])
        H = np.array([[1/sqrt2,1/sqrt2], [1/sqrt2,-1/sqrt2]])
        self.apply_sing_op(H, name, i)
        
    def apply_phase(self, phase, name, i):
        U = np.array([[np.exp(phase), 0], [0, np.exp(phase)]])
        self.apply_sing_op(U, name, i)        

    def apply_swap(self, name1, i1, name2, i2):
        loc1 = self.q_ref.get_loc(name1, i1)
        loc2 = self.q_ref.get_loc(name2, i2)
        
        s = self.solver
        
        new_qs = ComplexVector(self.state_token(self.t + 1), self.N)
        
        for state in range(self.N):
            qr = new_qs[state].r
            qi = new_qs[state].i
            if (bool(state  & (1 << loc1)) ^ bool(state & (1 << loc2))):
#                 Get swap state number
                set1 =  (state >> loc1) & 1
                set2 =  (state >> loc2) & 1
                xor = (set1 ^ set2)
                xor = (xor << loc1) | (xor << loc2)
                swap_state = state ^ xor

#                 Make new qubit state the current swapped one
                s.add(qr == self.qs[swap_state].r)
                s.add(qi == self.qs[swap_state].i)
            else:
                s.add(qr == self.qs[state].r)
                s.add(qi == self.qs[state].i)
        self.t += 1
        self.qs = new_qs
            
#     Applies an operator to the entire qubit state    
    def apply_op(self, U):
        if (U.shape[0] != self.N or U.shape[1] != self.N):
            print(U.shape, self.N)
            raise Exception('Error: U not right shape, expected (' + str(self.N) + ',' + str(self.N) + '), but received ' + str(U.shape))
        s = self.solver
        
        new_qs = ComplexVector(self.state_token(self.t + 1), self.N)
        
        for num in range(self.N):
            qr = new_qs[num].r
            qi = new_qs[num].i
            
            s.add(qr == Sum([U.real[num][j] * self.qs[j].r - U.imag[num][j] * self.qs[j].i 
                             for j in range(self.N)]))
            s.add(qi == Sum([U.imag[num][j] * self.qs[j].r + U.real[num][j] * self.qs[j].i
                             for j in range(self.N)]))
        
        self.t += 1
        self.qs = new_qs
        
    def add_oracle(self, conds):
        self.oracle = Function('f', IntSort(), IntSort())
        self.solver.add(conds(self.oracle))
        
    def apply_oracle(self, name):
        var_N = 2**self.q_ref.get_size(name)
        self.apply_op(oracle(var_N, self.oracle))
        
        
    def measure(self, name):
        return False