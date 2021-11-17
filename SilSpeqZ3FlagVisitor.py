from lark.visitors import *
from lark import Token
from z3 import *

# TODO: Rename Interpreter to Visitor
class SilSpeqZ3FlagVisitor(Visitor):
    oracles = []
    quantum_out = False
    meas_cert = False
    
    def __init__(self):
        super().__init__()
    
    def specs(self, specs):
        pass
    
    def funcspec(self, tree):
        pass
    
    def qout(self, v):
        self.quantum_out = True
        pass
        
    def cert(self, v):
        self.meas_cert = True
        pass
    
    def oracle(self, v):
        return lambda name: self.oracles.append(name)
        
    def definition(self, v):
        # if isinstance(v[0], type(lambda:0)):
        #     v[0](v[1].value)
        pass