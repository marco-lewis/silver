from lark.visitors import *
from z3 import *

def Equiv(a, b):
    return And(Implies(a, b), Implies(b, a))

NAT = "NAT"

class SilSpeqInterpreter(Interpreter):
    def __init__(self, solver):
        self.solver = solver
        self.vars = {}
        super().__init__()

    @visit_children_decor
    def specs(self, specs):
        d = {}
        for spec in specs:
            d[spec[0].value] = spec[1:]
        return d

    @visit_children_decor
    def funcspec(self, tree):
        return tree

    @visit_children_decor
    def pre(self, stmts):
        print(stmts)
        # return stmts
        pass

    @visit_children_decor
    def post(self, stmts):
        # return stmts
        pass

    @visit_children_decor
    def definition(self, df):
        pass

    # Handling types
    def nat(self, a):
        return NAT

    
    
    @visit_children_decor
    def int(self, a):
        if a == []:
            a.append(1)
        return int(a[0])

    # Handling lexpr
    # def le(self, a):
    #     return a[0] <= a[1]

    # def land(self, a):
    #     return And(a[0], a[0])

    # def lor(self, a):
    #     return Or(a[0], a[1])

    # def implies(self, a):
    #     return Implies(a[0], a[1])

    # def equiv(self, a):
    #     return Equiv(a[0], a[1])
    
    # def lnot(self, a):
    #     return Not(a[0])
    
    # def forall(self, a):
    #     return ForAll([a[0]], a[1])

    # def exists(self, a):
    #     return Exists([a[0]], a[1])

    # Handling numexpr
    # @visit_children_decor
    # def add(self,exprs):
    #     return exprs[0] + exprs[1]

    # @visit_children_decor
    # def sub(self,exprs):
    #     return exprs[0] - exprs[1]

    # @visit_children_decor
    # def mul(self,exprs):
    #     return exprs[0] * exprs[1]

    # @visit_children_decor
    # def div(self,exprs):
    #     return exprs[0] / exprs[1]

    # @visit_children_decor
    # def pow(self,exprs):
    #     return exprs[0] ** exprs[1]

    # def call(self, a):
    #     return a

    def NUMBER(self, n):
        print(n)
        (n,) = n
        return float(n)