from z3 import *
from QuantumMemory import QuantumMemory
from complex import *
from ComplexVector import *
from utils import *
from QuantumOps import ID

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    def __init__(self):
        pass
        
    def make_qstate(self):
        pass
    
    def make_qubit_operation(self, op, q_loc, size):
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(size - 1 - q_loc == i) else kronecker(out, op)
        pass
    
    def make_phase_op(self, cond, phase, size = 1):
        return [[to_complex(1 - cond(i)) + phase * cond(i) if i == j 
                else 0 for j in range(2**size)] for i in range(2**size)]

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs):
            raise Exception("LengthError: lengths of lists don't match")
        return [lhs[i] == rhs[i] for i in range(len(lhs))]

    def obligation_quantum_literal(self, q_data, size, type, literal = 0):
        var = q_data[0]
        lit_vec = [1 if i == literal else 0 for i in range(0, 2**size)]
        pass
            
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
        for row in operation:
            obs.append(Sum([row[col] * obligations[col] for col in range(len(row))]))
        pass