from lark.visitors import *
from lark import Token
from z3 import *

from silver.MeasureOptions import *

class SilSpeqFlagInterpreter(Interpreter):
    oracles = []
    quantum_out = False
    
    def __init__(self, func):
        self.func = func
        super().__init__()
    
    @visit_children_decor
    def specs(self, specs):
        for spec in specs:
            if spec[0] == self.func: return spec[1] if isinstance(spec[1], list) else [spec[1]]
    
    @visit_children_decor
    def funcspec(self, flags): return flags
    
    def pre(self, tree): pass

    def post(self, tree): pass

    def qout(self, v): pass
        
    def rand(self, v):
        return (RAND,None)

    def cert(self, v):
        return (CERTAINTY,None)

    def whp(self, v):
        return (HIGH_PROB, 0.5)

    def whpvalue(self, v:Tree):
        if list(v.find_data('pdec')): d = self.pdec(v.children[0])
        elif list(v.find_data('pdiv')): d = self.pdiv(v.children[0])
        return (HIGH_PROB, d)

    def pdec(self, v:Tree):
        return float("0." + str(self.token(v.children[0])))

    def pdiv(self, v:Tree):
        children = v.children
        ints = [self.token(c) for c in children]
        return ints[0] / ints[1]

    def atvalue(self, v: Tree):
        dtree = list(v.find_data('definition'))[0]
        mark = self.definition(dtree)
        return (SPECIFIC_VALUE, mark)
    
    def oracle(self, v):
        return lambda name: self.oracles.append(name)

    def definition(self, v:Tree):
        name = self.token(v.children[0])
        return Int(name)

    def token(self, tok: Token):
        if tok.type == "INT": return self.INT(tok)
        if tok.type == "NUMBER": return self.NUMBER(tok)
        if tok.type == "NAME": return self.NAME(tok)

    def INT(self, n: Token):
        return int(n.value)

    def NUMBER(self, n):
        return float(n.value)

    def NAME(self, var):
        return var.value