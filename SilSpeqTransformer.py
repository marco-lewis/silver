from lark import Transformer
from z3 import *

def Equiv(a, b):
    return And(Implies(a, b), Implies(b, a))

class SilqSpeqTransformer(Transformer):
    def __init__(self):
        pass
    
    # Handling pre/post/func

    # Handling definitions and statements
    # def definition(self, a):
    #     return a

    # Handling types
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
    def add(self,exprs):
        return exprs[0] + exprs[1]

    def sub(self,exprs):
        return exprs[0] - exprs[1]

    def mul(self,exprs):
        return exprs[0] * exprs[1]

    def div(self,exprs):
        return exprs[0] / exprs[1]

    def pow(self,exprs):
        return exprs[0] ** exprs[1]

    # def call(self, a):
    #     return a

    def NUMBER(self, n):
        (n,) = n
        return float(n)