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
    
    def make_quantum_process_obligation(self, q_process : QuantumProcess, prev_mem : QuantumMemory, controls : list) -> list[BoolRef]:
        instruction = q_process.instruction
        if isinstance(instruction, QINIT):
            lhs = self.quantum_memory_to_literals(q_process.end_memory)
            rhs = self.qinit_obligation(instruction, prev_mem)
            return self.obligation_quantum_assignment(lhs, rhs)
        if isinstance(instruction, QOP):
            lhs = self.quantum_memory_to_literals(q_process.end_memory)
            rhs = self.qop_obligation(instruction, prev_mem, controls)
            return self.obligation_quantum_assignment(lhs, rhs)
        if isinstance(instruction, QPHASE):
            lhs = self.quantum_memory_to_literals(q_process.end_memory)
            rhs = self.qphase_obligation(instruction, prev_mem, controls)
            return self.obligation_quantum_assignment(lhs, rhs)
        if isinstance(instruction, QMEAS):
            return self.obligation_quantum_measurement(instruction, prev_mem, self.__config[MEASURE_OPTION])
        if isinstance(instruction, QFORGET):
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
    
    def qop_obligation(self, instruction : QOP, prev_mem : QuantumMemory, controls : list):
        # BUG: Control doesn't produce right one for CNOT
        # TODO: Handle non-standard operations
        # TODO: Handle multiple controls
        loc = prev_mem.get_loc(instruction.arg.variable, instruction.arg.index)
        matrix = self.matrix_from_string(instruction.operation)
        op = self.make_qubit_operation(matrix, loc, prev_mem.get_total_size())
        for control in controls:
            if isinstance(control, QOP):
                if prev_mem.is_stored(control.arg.variable):
                    control_loc = prev_mem.get_loc(control.arg.variable)
                    op = self.make_qubit_control_operation(op, prev_mem.get_total_size(), control.operation, control_loc)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
    
    def qphase_obligation(self, instruction : QPHASE, prev_mem : QuantumMemory, controls : list):
        # TODO: Handle non-standard operations
        phase = PHASE(instruction.phase)
        op = [[phase if i == j else 0 for j in range(2**prev_mem.get_total_size())] for i in range(2**prev_mem.get_total_size())]
        for control in controls:
            if isinstance(control, QOP):
                if prev_mem.is_stored(control.arg.variable):
                    control_loc = prev_mem.get_loc(control.arg.variable)
                    op = self.make_qubit_control_operation(op, prev_mem.get_total_size(), control.operation, control_loc)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
        
    def make_qubit_operation(self, op, q_loc, size):
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(size - 1 - q_loc == i) else kronecker(out, op)
        return out

    # TODO: Check process
    def make_qubit_control_operation(self, op, size, cond, control_loc):
        return [[delta(i,j) + cond(floor(i/2**control_loc))*(op[i][j] - delta(i,j)) for j in range(2**size)] for i in range(2**size)]

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs):
            raise Exception("LengthError: lengths of lists don't match")
        return [lhs[i] == rhs[i] for i in range(len(lhs))]

    def obligation_quantum_literal(self, size, literal = 0):
        return [1 if i == literal else 0 for i in range(0, 2**size)]
            
    # TODO: Handle measurement differently
    def obligation_quantum_measurement(self, instruction : QMEAS, prev_memory : QuantumMemory, measure_option=HIGH_PROB):
        quantum_ref = instruction.quantum_ref
        variable = quantum_ref.variable
        index = quantum_ref.index
        
        loc = prev_memory.get_loc(variable, index)
        size = prev_memory.get_size(variable)
        prob_strs = ["Pr_" + prev_memory.get_reg_string(variable) + "_" + str(i) 
                 for i in range(2**size)]
        probs_z3_vars = [Real(p) for p in prob_strs]

        obligations = []
        obligations.append(And([And(p <= 1, p >= 0) for p in probs_z3_vars]))
        obligations.append(Sum(probs_z3_vars) == 1)
        
        # Calculate probabilities based on amplitudes of memory
        memory_obligation_variables = [Complex(memory_str) for memory_str in prev_memory.get_obligation_variables()]
        for i in range(len(probs_z3_vars)):
            mem_locs = [x for x in range(2**prev_memory.get_total_size()) if not(x^(i<<loc))]
            s = [memory_obligation_variables[i].len_sqr() for i in mem_locs]
            obligations.append(probs_z3_vars[i] == Sum(s))
            
        if measure_option == HIGH_PROB:
            meas_obligations = self.obligation_qmeas_with_high_prob(variable, probs_z3_vars)
        if measure_option == CERTAINTY:
            meas_obligations = self.obligation_qmeas_with_certainty(variable, probs_z3_vars)
        if measure_option == SPECIFIC_VALUE:
            meas_obligations = self.obligation_qmeas_with_specific_value(variable, probs_z3_vars)
            
        return obligations + meas_obligations
    
    def obligation_qmeas_with_specific_value(self, var, probs_z3_vars):
        raise Exception("ObligationError: function not implemented yet")
    
    def obligation_qmeas_with_certainty(self, var, probs_z3_vars):
        meas_cert = Bool('meas_cert')
        value = Int('meas_' + var)
        obligations = [Equiv(Or([p == 1 for p in probs_z3_vars]), meas_cert == True)]
        obligations += [Implies(1 == probs_z3_vars[i], value == i)
                        for i in range(len(probs_z3_vars))]

        return obligations
    
    # TODO: unsat on 50/50 chance, need a way to handle this just in case
    def obligation_qmeas_with_high_prob(self, var, probs_z3_vars):
        max_prob = Real('hprob_' + var)
        value = Int('meas_' + var)
        obligations = [Or([max_prob == p for p in probs_z3_vars])]
        obligations.append(And([max_prob >= p for p in probs_z3_vars]))
        obligations += [Implies(max_prob == probs_z3_vars[i], value == i)
                        for i in range(len(probs_z3_vars))]
        
        return obligations
    
    def obligation_quantum_forget(self, q_process : QuantumProcess, prev_mem : QuantumMemory):
        instruction : QFORGET = q_process.instruction
        prev_vars = self.quantum_memory_to_literals(prev_mem)
        new_vars = self.quantum_memory_to_literals(q_process.end_memory)
        loc = prev_mem.get_loc_from_VarRef(instruction.variable)
        
        prev_vars_at_value = []
        for i in range(len(prev_vars)):
            if i >> loc == instruction.value:
                prev_vars_at_value += [prev_vars[i]]

        s = simplify(Sum([q.len_sqr() for q in prev_vars_at_value]))
        obligations = [Implies(s != 1, False)]
        if new_vars != []:
            for i in range(len(new_vars)):
                obligations += [new_vars[i] == prev_vars_at_value[i]]
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