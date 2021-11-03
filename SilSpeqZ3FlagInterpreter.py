from lark.visitors import *
from lark import Token
from z3 import *

class SilSpeqZ3FlagInterpreter(Interpreter):
    oracles = []
    quantum_out = False
    
    def __init__(self):
        super().__init__()
    
    @visit_children_decor
    def specs(self, specs):
        pass
    
    @visit_children_decor
    def funcspec(self, tree):
        pass
    
    def qout(self, v):
        self.quantum_out = True
        
    def oracle(self, v):
        return lambda name: self.oracles.append(name)
        
    @visit_children_decor
    def definition(self, v):
        if isinstance(v[0], type(lambda:0)):
            v[0](v[1].value)