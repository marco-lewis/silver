from z3 import *
from QuantumReferencer import QuantumReferencer
from complex import *
from ComplexVector import *
import numpy as np

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    quantum_referencer = QuantumReferencer()
    __prev_quantum_mem = []

    def __init__(self):
        pass

    def make_qstate(self, names):
        self.__prev_quantum_mem = [Complex(name) for name in names]
        return self.__prev_quantum_mem

    def make_qubit_operation(self, op, var):
        q_loc = self.quantum_referencer.get_loc(var)
        size = self.quantum_referencer.get_total_size()
        out = 1
        for i in range(0, 2**size):
            out = np.kron(np.identity(2), out) if not(q_loc == i) else np.kron(op, out)
        return np.ndarray.tolist(out)

    def obligation_quantum_assignment(self, lhs, rhs):
        return [lhs[i] == rhs[i] for i in range(0, len(lhs))]

    def obligation_quantum_literal(self, literal = 0, var_name = ""):
        if self.quantum_referencer.is_empty():
            pass
        elif self.quantum_referencer.is_single():
            return [1 if i == literal else 0 for i in range(0, 2**self.quantum_referencer.get_total_size())]
        else:
            out = []
            j = 0
            for i in range(0, 2**self.quantum_referencer.get_total_size()):
                if i % 2 == literal:
                    out.append(self.__prev_quantum_mem[j])
                    j += 1
                else:
                    out.append(0)
            return out
            pass

    def obligation_operation(self, operation, obligations):
        obs = []
        for row in operation:
            print(row[0] , obligations[0])
            obs.append(Sum([row[col] * obligations[col] for col in range(0, len(row))]))
        return obs