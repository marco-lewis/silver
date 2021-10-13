from z3 import *
from QuantumReferencer import QuantumReferencer
import complex, ComplexVector

class ObilgationGenerator:

    quantum_referencer = QuantumReferencer()

    def __init__(self):
        pass

    def make_token(self, variable):
        pass

    def obligation_quantum_assignment(self, lhs, rhs):
        return (lhs[i] == rhs[i] for i in range(0, len(lhs)))

    def obligation_quantum_literal(self, literal = 0):
        if self.quantum_referencer.is_empty():
            return (1 if i == literal else 0 for i in range(0, self.quantum_referencer.get_total_size()))
        pass

    def obligation_operation(self, operation):
        pass