from z3 import *
from QuantumReferencer import QuantumReferencer
from complex import *
from ComplexVector import *
from utils import *
from QuantumOps import ID

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    quantum_referencer = QuantumReferencer()
    __prev_quantum_mem = []

    def __init__(self):
        pass
    
    def get_prev_quantum_mem(self):
        return self.__prev_quantum_mem
    
    def get_and_update_q_mem(self, var, old_var = None):
        qstate = self.make_qstate()
        self.update_quantum_memory(var, old_var)
        return qstate
    
    def handle_type(self, type):
        # TODO: Find arbitrary value
        if self.__single_type(type):
            pass
        if isinstance(type, dict):
            if type[TYPEOBJ] == "uint":
                size = type["size"]
                while isinstance(size, dict):
                    size = size["value"]
                self.quantum_referencer.ammend_size(size)
        pass
    
    def __single_type(self, type):
        return type == "B" or type == "𝔹"
    
    def make_qstate(self):
        names = self.quantum_referencer.get_obligation_variables()
        return [Complex(name) for name in names]
    
    def update_quantum_memory(self, var, old_var = None):
        if not(old_var == None) and not(var == old_var):
            self.quantum_referencer.ammend_name(old_var, var)
        self.quantum_referencer.iterate_var(var)
        names = self.quantum_referencer.get_obligation_variables()
        self.__prev_quantum_mem = [Complex(name) for name in names]

    def make_qubit_operation(self, op, var):
        q_loc = self.quantum_referencer.get_loc(var)
        size = self.quantum_referencer.get_total_size()
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(q_loc == i) else kronecker(out, op)
        return out

    def obligation_quantum_assignment(self, lhs, rhs):
        return [lhs[i] == rhs[i] for i in range(len(lhs))]

    def obligation_quantum_literal(self, var, type, literal = 0):
        if not(self.quantum_referencer.is_stored(var)):
            self.quantum_referencer.append(var, 1)
            self.handle_type(type)

        loc = self.quantum_referencer.get_loc(var)
        if self.quantum_referencer.is_empty():
            raise Exception('OblError: qstate is empty')
        elif self.quantum_referencer.is_single():
            return [1 if i == literal else 0 for i in range(0, 2**self.quantum_referencer.get_total_size())]
        else:
            out = []
            mem_point = 0
            for i in range(2**self.quantum_referencer.get_total_size()):
                if i % 2**loc == literal:
                    out.append(self.__prev_quantum_mem[mem_point])
                    mem_point += 1
                else:
                    out.append(0)
            return out

    def obligation_operation(self, operation, obligations):
        obs = []
        for row in operation:
            obs.append(Sum([row[col] * obligations[col] for col in range(len(row))]))
        return obs

    def obligation_value(self, value):
        if isinstance(value, list):
            return [Int(v + "_ret") for v in value]
        else:
            return value