from math import floor
from z3 import *
from ClassicalMemory import ClassicalMemory
from Instruction import *
from Process import ClassicalProcess, QuantumProcess
from QuantumMemory import QuantumMemory
from complex import *
from ComplexVector import *
from silspeq.SilSpeqZ3Interpreter import Equiv
from utils import *
from QuantumOps import *
from MeasureOptions import MEASURE_OPTION, HIGH_PROB, CERTAINTY, SPECIFIC_VALUE

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs
# TODO: Handle return statements differently based on quantum or classical

class ObilgationGenerator:
    def __init__(self, config = {}):
        self.__config = config
    
    def make_classical_process_obligation(self, c_process : ClassicalProcess, prev_mem : ClassicalMemory, control : list) -> list[BoolRef]:
        instruction = c_process.instruction
        if isinstance(instruction, CMEAS):
            return self.cmeas_obligation(instruction, prev_mem, c_process.end_memory)
        if isinstance(instruction, RETURN):
            # TODO: fetch return variables differently depending on what is being returned
            to_return = Int(prev_mem.get_obligation_variable(instruction.value_refs[0].variable))
            return_z3var = Int(instruction.function_name + "_ret")
            return [return_z3var == to_return]
        raise Exception("GenerationError: Unable to make obligation for instruction " +  repr(instruction))
    
    def cmeas_obligation(self, instruction: CMEAS, prev_memory : ClassicalMemory, end_memory : ClassicalMemory):
        meas = Int('meas_' + instruction.quantum_ref.variable)
        value = Int(end_memory.get_obligation_variable(instruction.classical_ref.variable))
        return [value == meas]

    # Adding bounds ot the lhs make it harder to find sat instances 
    def make_quantum_process_obligation(self, q_process : QuantumProcess, prev_mem : QuantumMemory, controls : list) -> list[BoolRef]:
        instruction = q_process.instruction
        lhs = self.quantum_memory_to_literals(q_process.end_memory)
        obs = []
        if isinstance(instruction, QINIT):
            rhs = self.qinit_obligation(instruction, prev_mem)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QOP):
            rhs = self.qop_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QPHASE):
            rhs = self.qphase_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QMEAS):
            return self.obligation_quantum_measurement(q_process, prev_mem, self.__config[MEASURE_OPTION])
        if isinstance(instruction, QFORGET):
            # return [True]
            return self.obligation_quantum_forget(q_process, prev_mem)
        if isinstance(instruction, RETURN):
            return [True]
        raise Exception("GenerationError: Unable to make obligation for instruction " +  repr(instruction))
    
    def quantum_memory_to_literals(self, memory : QuantumMemory):
        return [Complex(string) for string in memory.get_obligation_variables()]
    
    def qinit_obligation(self, instruction : QINIT, prev_mem : QuantumMemory):
        if prev_mem.is_empty():
            return self.obligation_quantum_literal(instruction.size, instruction.value)
        lits = self.quantum_memory_to_literals(prev_mem)
        obligations = []
        for i in range(2**(prev_mem.get_total_size())):
            obligations += [0 if i != instruction.value else lits[j] for j in range(2**instruction.size)]
        return obligations
    
    def make_quantum_memory_initial_obligations(self, initial_memory : QuantumMemory):
        lits = self.quantum_memory_to_literals(initial_memory)
        if lits == []: return []
        sum_of_sqrs = 0
        for i in range(2**(initial_memory.get_total_size())):
            sum_of_sqrs += lits[i].len_sqr()
        obligations = [sum_of_sqrs == 1]
        return obligations
    
    def qop_obligation(self, instruction : QOP, prev_mem : QuantumMemory, controls : list):
        # TODO: Handle non-standard operations
        # TODO: Handle multiple controls
        loc = prev_mem.get_loc(instruction.arg.variable, instruction.arg.index)
        matrix = self.matrix_from_string(instruction.operation)
        if controls == []:
            op = self.make_qubit_operation(matrix, loc, prev_mem.get_total_size())
        if len(controls) == 1:
            control = controls[0]
            if isinstance(control, QOP):
                if prev_mem.is_stored(control.arg.variable):
                    control_loc = prev_mem.get_loc(control.arg.variable)
                    op = self.make_qubit_control_operation(matrix, prev_mem.get_total_size(), control.operation, control_loc)
                    if control_loc == 0:
                        op = dot(dot(SWAP, op), SWAP)
                        op = [[simplify(el) for el in r] for r in op]
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
    
    def qphase_obligation(self, instruction : QPHASE, prev_mem : QuantumMemory, controls : list):
        # TODO: Handle non-standard operations
        # TODO: Handle more boolops (make general)
        phase = PHASE(instruction.phase)
        op = [[phase if i == j else 0 for j in range(2**prev_mem.get_total_size())] for i in range(2**prev_mem.get_total_size())]
        for control in controls:
            if isinstance(control, QOP):
                if prev_mem.is_stored(control.arg.variable):
                    control_loc = prev_mem.get_loc(control.arg.variable)
                    op = self.make_qphase_control_operation(op, prev_mem.get_total_size(), control.operation, control_loc)
            if isinstance(control, BOOLOP):
                if prev_mem.is_stored(control.left.variable):
                    control_loc = prev_mem.get_loc(control.left.variable)
                    control_op = lambda l: control.comparitor(l, control.right)
                    op = self.make_qphase_control_operation(op, prev_mem.get_total_size(), control_op, control_loc)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
        
    def make_qubit_operation(self, op, q_loc, size):
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(size - 1 - q_loc == i) else kronecker(out, op)
        return out

    # TODO: Check process
    def make_qubit_control_operation(self, op, size, cond, control_loc):
        mat = []
        for y in range(size):
            t = [[delta(i,j) + cond(y) * (op[i-y*size][j - y*size] - delta(i,j)) for j in range(2)] for i in range(2)]
            t = kronecker([[1 if x == y else 0 for x in range(size)]], t)
            mat += t
        return mat
    
    # TODO: Check with deutsch_anc
    def make_qphase_control_operation(self, op, size, cond, control_loc):
        return [[delta(i,j) + cond(floor(i//2**control_loc))*(op[i][j] - delta(i,j)) if i==j else 0 for j in range(2**size)] for i in range(2**size)]

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs):
            raise Exception("LengthError: lengths of lists don't match")
        return [simplify(lhs[i] == rhs[i]) for i in range(len(lhs))]

    def obligation_quantum_literal(self, size, literal = 0):
        return [1 if i == literal else 0 for i in range(0, 2**size)]
            
    # TODO: Add state after measurement calculated
    # TODO: Correct probabilities from previous memory
    def obligation_quantum_measurement(self, q_process : QuantumProcess, prev_memory : QuantumMemory, measure_option=HIGH_PROB):
        instruction : QMEAS = q_process.instruction
        quantum_ref = instruction.quantum_ref
        variable = quantum_ref.variable
        index = quantum_ref.index
        
        # Set up labels for probabilities
        loc = prev_memory.get_loc(variable, index)
        size = prev_memory.get_size(variable)
        prob_strs = ["Pr_" + prev_memory.get_reg_string(variable) + "_" + str(i) 
                 for i in range(2**size)]
        probs_z3_vars = [Real(p) for p in prob_strs]

        # Obligations for probabilities
        obligations = []
        obligations.append(And([And(p <= 1, p >= 0) for p in probs_z3_vars]))
        probs_sum = Real("Pr_" + prev_memory.get_reg_string(variable) + "_sum")
        obligations.append(probs_sum == Sum(probs_z3_vars))
        obligations.append(probs_sum == 1)
        
        # Calculate probabilities based on amplitudes of memory
        memory_obligation_variables = [Complex(memory_str) for memory_str in prev_memory.get_obligation_variables()]
        for meas_value in range(len(probs_z3_vars)):
            mem_locs = [x for x in range(2**prev_memory.get_total_size()) 
                        if (x & (2**(size)- 1<<loc) == (meas_value) << loc)]
            s = [memory_obligation_variables[l].len_sqr() for l in mem_locs]
            obligations.append(probs_z3_vars[meas_value] == Sum(s))
            
        # Measurement options
        classical_value = Int('meas_' + variable)
        meas_obligations = []
        if measure_option == HIGH_PROB:
            meas_obligations = self.obligation_qmeas_with_high_prob(variable, probs_z3_vars, classical_value)
        if measure_option == CERTAINTY:
            meas_obligations = self.obligation_qmeas_with_certainty(variable, probs_z3_vars, classical_value)
        if measure_option == SPECIFIC_VALUE:
            meas_obligations = self.obligation_qmeas_with_specific_value(variable, probs_z3_vars, classical_value)
            
        # State after measurement
        # TODO: handle non-certainty instances (include 1//Sqrt(probs_z3_vars[meas_value]))
        post_memory = q_process.end_memory
        if not(post_memory.is_empty()):
            post_z3_vars = [Complex(obl_var) for obl_var in post_memory.get_obligation_variables()]
            post_state_obligations = []
            for meas_value in range(2**size):
                mem_locs = [memory_obligation_variables[j] for j in range(len(memory_obligation_variables)) if not((j & 1 << loc) ^ (meas_value << loc))]
                post_prev_eq = And([post_var == prev_var for (post_var, prev_var) in zip(post_z3_vars, mem_locs)])
                post_state_obligations.append(Implies(classical_value == meas_value, post_prev_eq))
        else:
            post_state_obligations = []

        return obligations + meas_obligations + post_state_obligations
    
    def obligation_qmeas_with_specific_value(self, var, probs_z3_vars, value):
        # raise Exception("ObligationError: function not implemented yet")
        a = Int('a')
        max_prob = Real('hprob_' + var)
        obligations = [And([max_prob >= p for p in probs_z3_vars])]
        obligations += [Equiv(max_prob == probs_z3_vars[i], a == i)
                        for i in range(len(probs_z3_vars))]
        obligations.append(value == a)
        return obligations

    def obligation_qmeas_with_certainty(self, var, probs_z3_vars, value):
        meas_cert = Bool('meas_cert')
        obligations = [Equiv(Or([p == 1 for p in probs_z3_vars]), meas_cert == True)]
        obligations += [Equiv(1 == probs_z3_vars[i], value == i)
                        for i in range(len(probs_z3_vars))]
        return obligations
    
    # TODO: Allow user to specify value for high probability (2/3, 1/2, 9/10...)
    def obligation_qmeas_with_high_prob(self, var, probs_z3_vars, value):
        obligations = [Equiv(2/3 <= probs_z3_vars[i], value == i)
                        for i in range(len(probs_z3_vars))]
        return obligations
    
    def obligation_quantum_forget(self, q_process : QuantumProcess, prev_mem : QuantumMemory):
        instruction : QFORGET = q_process.instruction
        prev_vars = self.quantum_memory_to_literals(prev_mem)
        new_vars = self.quantum_memory_to_literals(q_process.end_memory)
        loc = prev_mem.get_loc_from_VarRef(instruction.variable)
        
        obligations = []
        
        # Check probability of value is 1
        prev_vars_at_value = [prev_vars[i] for i in range(len(prev_vars)) if i >> loc == instruction.value]
        s = simplify(Sum([q.len_sqr() for q in prev_vars_at_value]))
        # Z3 BUG: Summation is causing major slow down
        # forget_sum = Real("forget_" + instruction.variable.variable)
        # obligations = [s == forget_sum, forget_sum == 1]
        
        # Set new state based on prev. variables
        if new_vars != []:
            obligations += [new == prev for (new, prev) in zip(new_vars, prev_vars_at_value)]
        return obligations
    
    def obligation_operation(self, operation, obligations):
        out_obligations = []
        for row in operation:
            out_obligations.append(Sum([to_complex(row[col]) * obligations[col] for col in range(len(row))]))
        return out_obligations
    
    def matrix_from_string(self, op):
        if op == 'X': return X
        if op == 'Y': return Y
        if op == 'Z\'': return Z
        if op == 'H': return H
        raise Exception("ConversionError: no matrix for " + op)