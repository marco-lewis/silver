from z3 import *
from QuantumReferencer import QuantumReferencer
from complex import *
from ComplexVector import *


# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    quantum_referencer = QuantumReferencer()

    def __init__(self):
        pass

    def make_qstate(self, names):
        return [Complex(name) for name in names]

    def obligation_quantum_assignment(self, lhs, rhs):
        return [lhs[i] == rhs[i] for i in range(0, len(lhs))]

    def obligation_quantum_literal(self, literal = 0, var_name = ""):
        if self.quantum_referencer.is_empty():
            pass
        else:
            return [1 if i == literal else 0 for i in range(0, 2**self.quantum_referencer.get_total_size())]

    def obligation_operation(self, operation, obligations):
        obs = []
        for row in operation:
            obs.append(Sum([row[col] * obligations[col] for col in range(0, len(row))]))
        return obs