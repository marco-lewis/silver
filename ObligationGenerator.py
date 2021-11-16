from z3 import *
from QuantumMemory import QuantumMemory
from complex import *
from ComplexVector import *
from utils import *
from QuantumOps import ID

# Currently handles single variable, want to change to handle multiple variables
# TODO: Checks for valid sizes of inputs

class ObilgationGenerator:
    q_memory = QuantumMemory()
    __prev_quantum_mem = []
    __cvars = {}

    def __init__(self):
        pass
    
    def get_prev_quantum_mem(self):
        return self.__prev_quantum_mem
    
    def get_and_update_q_mem(self, var, old_var = None):
        qstate = self.make_qstate()
        self.update_quantum_memory(var, old_var)
        return qstate
    
    def handle_type(self, reg, type):
        # TODO: Find arbitrary value
        if self.__single_type(type):
            pass
        if isinstance(type, dict):
            if type[TYPEOBJ] == "uint":
                size = type["size"]
                while isinstance(size, dict):
                    size = size["value"]
                self.q_memory.ammend_size(reg, size)
        pass
    
    def __single_type(self, type):
        return type == "B" or type == "𝔹"
    
    def make_qstate(self):
        names = self.q_memory.get_obligation_variables()
        return [Complex(name) for name in names]
    
    def update_quantum_memory(self, var, old_var = None):
        if not(old_var == None) and not(var == old_var):
            self.q_memory.update_reg(old_var, var)
        self.q_memory.iterate_var(var)
        names = self.q_memory.get_obligation_variables()
        self.__prev_quantum_mem = [Complex(name) for name in names]

    def new_cvar(self, var):
        self.__cvars[var] = Int(var + "_0")
        return self.__cvars[var]
    
    def get_cvar(self, var):
        return self.__cvars[var]
    
    def make_qubit_operation(self, op, var):
        q_loc = self.q_memory.get_loc(var)
        size = self.q_memory.get_total_size()
        out = [[1]]
        for i in range(size):
            out = kronecker(out, ID) if not(q_loc == i) else kronecker(out, op)
        return out

    def obligation_quantum_assignment(self, lhs, rhs):
        return [lhs[i] == rhs[i] for i in range(len(lhs))]

    def obligation_quantum_literal(self, var, type, literal = 0):
        if not(self.q_memory.is_stored(var)):
            self.q_memory.append(var, 1)
            self.handle_type(var, type)

        loc = self.q_memory.get_loc(var)
        self.update_quantum_memory(var)
        if self.q_memory.is_empty():
            raise Exception('OblError: qstate is empty')
        elif self.q_memory.is_single():
            return [1 if i == literal else 0 for i in range(0, 2**self.q_memory.get_total_size())]
        else:
            out = []
            mem_point = 0
            for i in range(2**self.q_memory.get_total_size()):
                if i % 2**loc == literal:
                    out.append(self.__prev_quantum_mem[mem_point])
                    mem_point += 1
                else:
                    out.append(0)
            return out
        
    # TODO: Handle measurement differently
    def obligation_quantum_measurement(self, var, with_certainty = False, with_hp = False):
        size = self.q_memory.get_size(var)
        loc = self.q_memory.get_loc(var)
        prev_mem = self.get_prev_quantum_mem()
        probs = ["Pr_" + self.q_memory.get_reg_string(var) + "_" + str(i) 
                 for i in range(2**size)]
        probs = [Real(p) for p in probs]

        obligations = []
               
        obligations.append(And([And(p <= 1, p >= 0) for p in probs]))
        obligations.append(Sum(probs) == 1)
        
        for i in range(len(probs)):
            mem_locs = [x for x in range(2**self.q_memory.get_total_size()) if not(x^(i<<loc))]
            # TODO: Check valid
            s = [prev_mem[i].len_sqr() for i in mem_locs]
            obligations.append(probs[i] == Sum(s))
        
        # TODO: Handle measuring part of qstate
        self.q_memory.measure_reg(var)
        if not(self.q_memory.is_empty()):
            self.get_prev_quantum_mem()
            pass

        if with_certainty:
            return self.obligation_qmeas_with_cert(var, obligations, probs)
        if with_hp:
            return self.obligation_qmeas_whp(var, obligations, probs)
    
    def obligation_qmeas_with_cert(self, var, obligations, probs):
        meas_cert = Bool('meas_cert')
        obligations.append(Implies(Or([p == 1 for p in probs]), meas_cert == True))
        value = Int('meas_' + var)
        obligations += [Implies(1 == probs[i], value == i)
                        for i in range(len(probs))]
        return lambda lhs: obligations + [self.new_cvar(lhs) == value]
    
    # TODO: unsat on 50/50 chance, need a way to handle this just in case
    def obligation_qmeas_whp(self, var, obligations, probs):
        max_prob = Real('hprob_' + var)
        value = Int('meas_' + var)
        obligations.append(Or([max_prob == p for p in probs]))
        obligations.append(And([max_prob >= p for p in probs]))
        obligations += [Implies(max_prob == probs[i], value == i)
                        for i in range(len(probs))]
        
        return lambda lhs: obligations + [self.new_cvar(lhs) == value]
    
    def obligation_operation(self, operation, obligations):
        obs = []
        for row in operation:
            obs.append(Sum([row[col] * obligations[col] for col in range(len(row))]))
        return obs

    def obligation_value(self, value):
        if isinstance(value, list):
            return [Complex(v + "_ret") for v in value]
        else:
            return value