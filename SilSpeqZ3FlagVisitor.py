from lark.visitors import *
from lark import Token
from z3 import *

class SilSpeqZ3FlagVisitor(Visitor):
    oracles = []
    quantum_out = False
    meas_rand = False
    meas_cert = False
    meas_whp = False
    meas_atval = False
    
    def __init__(self):
        super().__init__()
    
    def specs(self, specs):
        pass
    
    def funcspec(self, tree):
        pass
    
    def qout(self, v):
        self.quantum_out = True
        
    def rand(self, v):
        self.meas_rand = True

    def cert(self, v):
        self.meas_cert = True

    def whp(self, v):
        self.meas_whp = True
    
    def atvalue(self, v):
        self.meas_atval = True

    def oracle(self, v):
        return lambda name: self.oracles.append(name)

    def definition(self, v):
        # if isinstance(v[0], type(lambda:0)):
        #     v[0](v[1].value)
        pass