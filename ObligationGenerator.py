from z3 import *
from Instruction import *
from Process import QuantumProcess
from QuantumMemory import QuantumMemory
from complex import *
from ComplexVector import *
from utils import *
from QuantumOps import *

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    def __init__(self):
        pass
    
    def make_quantum_process_obligation(self, q_process : QuantumProcess, prev_mem : QuantumMemory):
        instruction = q_process.command.instruction
        if isinstance(instruction, QINIT):
            lhs = self.quantum_memory_to_literals(q_process.end_memory)
            rhs = self.qinit_obligation(instruction, prev_mem)
            return self.obligation_quantum_assignment(lhs, rhs)
        if isinstance(instruction, QOP):
            lhs = self.quantum_memory_to_literals(q_process.end_memory)
            rhs = self.qop_obligation(instruction, prev_mem)
            return self.obligation_quantum_assignment(lhs, rhs)
        if isinstance(instruction, RETURN):
            # TODO: Correctly handle return statements (might need more from SilVer)
            return [True]
        raise Exception("GenerationError: Unable to make obligation for instruction ", instruction)
    
    def quantum_memory_to_literals(self, memory : QuantumMemory):
        return [Complex(string) for string in memory.get_obligation_variables()]
    
    def qinit_obligation(self, instruction : QINIT, prev_mem : QuantumMemory):
        if prev_mem.is_empty():
            return self.obligation_quantum_literal(instruction.size, instruction.value)
        lits = self.quantum_memory_to_literals(prev_mem)
        obs = []
        for i in range(2**(prev_mem.get_total_size())):
            obs += [0 if i != instruction.value else lits[j] for j in range(2**instruction.size)]
        return obs
    
    def qop_obligation(self, instruction : QOP, prev_mem : QuantumMemory):
        # TODO: Handle non-standard operations
        loc = prev_mem.get_loc(instruction.arg.variable, instruction.arg.index)
        matrix = self.matrix_from_string(instruction.operation)
        op = self.make_qubit_operation(matrix, loc, prev_mem.get_total_size())
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
        
    def make_qubit_operation(self, op, q_loc, size):
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(size - 1 - q_loc == i) else kronecker(out, op)
        return out
    
    def make_phase_op(self, cond, phase, size = 1):
        return [[to_complex(1 - cond(i)) + phase * cond(i) if i == j 
                else 0 for j in range(2**size)] for i in range(2**size)]

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs):
            raise Exception("LengthError: lengths of lists don't match")
        return [lhs[i] == rhs[i] for i in range(len(lhs))]

    def obligation_quantum_literal(self, size, literal = 0):
        return [1 if i == literal else 0 for i in range(0, 2**size)]
            
    # TODO: Handle measurement differently
    def obligation_quantum_measurement(self, var, with_certainty = False, with_hp = False):
        pass
    
    def obligation_qmeas_with_cert(self, var, obligations, probs):
        pass
    
    # TODO: unsat on 50/50 chance, need a way to handle this just in case
    def obligation_qmeas_whp(self, var, obligations, probs):
        pass
    
    def obligation_operation(self, operation, obligations):
        obs = []
        [obs.append(Sum([to_complex(row[col]) * obligations[col] for col in range(len(row))])) for row in operation]
        return obs
    
    def matrix_from_string(self, op):
        if op == 'X': return X
        if op == 'Y': return Y
        if op == 'Z\'': return Z
        if op == 'H': return H
        raise Exception("ConversionError: no matrix for " + op)