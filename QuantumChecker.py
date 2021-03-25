from z3 import *
import numpy as np
from complex import Complex, I
from ComplexVector import ComplexVector
import cmath
from QuantumReferencer import QuantumReferencer


# TODO: Add checks/exceptions across the board
# TODO: Add measurement or check highest prob
# TODO: Handle Hadamard?
# TODO: Initialisation to a specific state/number
# TODO: Handling classical variables - new class?
# TODO: Handle 2-qubit gates/ops - quantum if-statements
# TODO: Adding extra constraints - done?

class QuantumChecker:
    def __init__(self):
#     Initialise a solver
        self.solver = Solver()
#     Set the step tracker to 0
        self.t = 0
        self.q_ref = QuantumReferencer()
        self.qs = []
        self.N = 0
        
    def check_solver(self):
        return self.solver.check()
    
    def print_solver(self):
        print(self.solver)
    
    def print_model(self):
        c = self.solver.check()
        if c == sat:
            m = self.solver.model()
            print(m)
        else:
            print("No model to print. Solver returned: " + str(c))
            
    def get_model(self):
        return self.solver.model()
    
    def add_constraint(self, conds):
        self.solver.add(conds)
                
#     Initialises a new register to 0
    def init_new_qreg(self, name, n):
        s = self.solver
        self.q_ref.add(name, n)
        if self.qs == []:
            self.qs = self.qs + ComplexVector('t' + str(self.t) + '_q', 2**n)
            for i in range(0, 2**n):
                q = self.qs[i]
                s.add(q == 0 + 0*I) if not(i == 0) else s.add(q == 1 + 0*I)
        else:
            old_N = self.N # self.q_ref.get_loc(name)
            v = ComplexVector('t' + str(self.t) + '_q', 2**(self.q_ref.get_total_size()) - old_N, offset = old_N)
            self.qs = self.qs + v

            for i in range(old_N, old_N * (2**n)):
                q = self.qs[i]
                s.add(q == 0 + 0*I)
        
        self.N = 2**(self.q_ref.get_total_size())
            
            
    def apply_sing_op(self, U, name, i):
        q_loc = self.q_ref.get_loc(name) + i
        U_kron = np.identity(2) if not (q_loc == 0) else U
        for i in range(1, self.q_ref.get_total_size()):
            U_kron = np.kron(np.identity(2), U_kron) if not(i == q_loc) else np.kron(U, U_kron)
        self.apply_op(U_kron)
            
#     Applies an operator to the entire qubit state    
    def apply_op(self, U):
        if (U.shape[0] != self.N or U.shape[1] != self.N):
            print(U.shape, self.N)
            raise Exception('Error: U not right shape, expected (' + str(self.N) + ',' + str(self.N) + '), but received ' + str(U.shape))
        s = self.solver
        
        next_stamp = 't' + str(self.t + 1) + '_q'
        new_qs = ComplexVector(next_stamp, self.N)
        
        for num in range(self.N):
            qr = new_qs[num].r
            qi = new_qs[num].i
            
            s.add(qr == Sum([U.real[num][j] * self.qs[j].r - U.imag[num][j] * self.qs[j].i 
                             for j in range(self.N)]))
            s.add(qi == Sum([U.imag[num][j] * self.qs[j].r + U.real[num][j] * self.qs[j].i
                             for j in range(self.N)]))
        
        self.t += 1
        self.qs = new_qs
        
#     Return all valid models
    def get_all_models():
        return False