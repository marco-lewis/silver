from lark.visitors import *
from lark import Token, Tree
from z3 import *
from itertools import chain


def Equiv(a, b):
    return And(Implies(a, b), Implies(b, a))

NAT = "NAT"
BOOL = "BOOL"

class SilSpeqInterpreter(Interpreter):
    def __init__(self):
        self.vars = {}
        super().__init__()

    # Handling pre, post, spec etc.
    @visit_children_decor
    def specs(self, specs):
        d = {}
        for spec in specs:
            func_spec = [s for s in spec[1:] if s != None]
            d[spec[0].value] = func_spec
        return d

    @visit_children_decor
    def funcspec(self, tree):
        return tree

    @visit_children_decor
    def pre(self, stmts):
        return stmts

    @visit_children_decor
    def post(self, stmts):
        return Not(And([wrap[0] for wrap in filter(None, stmts[0])]))


    # Handling definitions and statements
    # TODO: Add restrictions on values (e.g. b:{0,1} means s.add(Or(b==0, b==1)))
    @visit_children_decor
    def definition(self, df):
        var = df[0].value
        if df[1] == NAT:
            self.vars[var] = Int(var)
            return self.vars[var] >= 0
        elif df[1] == BOOL:
            self.vars[var] = Int(var)
            return Or(self.vars[var] == 0, self.vars[var] == 1)
        else:
            self.vars[var] = Int(var)
            return Or([self.vars[var] == i for i in range(0, 2**df[1])])


    @visit_children_decor
    def assertion(self, zexpr):
        return zexpr


    # Handling types
    def nat(self, a):
        return NAT

    def bool(self, a):
        return BOOL
    
    @visit_children_decor
    def int(self, n):
        if n == []:
            return 1
        return int(n[0].value)

    # Handling lexpr
    @visit_children_decor
    def eq(self, lexprs):
        return lexprs[0] == lexprs[1]

    @visit_children_decor
    def le(self, nexprs):
        return nexprs[0] <= nexprs[1]

    @visit_children_decor
    def land(self, lexprs):
        return And(lexprs[0], lexprs[0])

    @visit_children_decor
    def lor(self, lexprs):
        return Or(lexprs[0], lexprs[1])

    @visit_children_decor
    def implies(self, lexprs):
        return Implies(lexprs[0], lexprs[1])

    @visit_children_decor
    def equiv(self, lexprs):
        return Equiv(lexprs[0], lexprs[1])
    
    @visit_children_decor
    def lnot(self, lexpr):
        return Not(lexpr[0])
    
    # def forall(self, a):
    #     return ForAll([a[0]], a[1])

    # def exists(self, a):
    #     return Exists([a[0]], a[1])

    # Handling numexpr
    @visit_children_decor
    def var(self, expr):
        return self.token(expr[0])
    
    @visit_children_decor
    def add(self,exprs):
        return self.handle_token(exprs[0]) + self.handle_token(exprs[1])

    @visit_children_decor
    def sub(self,exprs):
        return self.handle_token(exprs[0]) - self.handle_token(exprs[1])

    @visit_children_decor
    def mul(self,exprs):
        return self.handle_token(exprs[0]) * self.handle_token(exprs[1])

    @visit_children_decor
    def div(self,exprs):
        return self.handle_token(exprs[0]) / self.handle_token(exprs[1])

    @visit_children_decor
    def pow(self,exprs):
        return self.handle_token(exprs[0]) ** self.handle_token(exprs[1])

    # def call(self, a):
    #     return a

    # def sum(self, expr):
    #     pass

    def handle_token(self, t):
        if isinstance(t, Token):
            return self.token(t)
        else:
            return t

    def token(self, tok: Token):
        if tok.type == "NUMBER":
            return self.NUMBER(tok)
        if tok.type == "NAME":
            return self.NAME(tok)

    def NUMBER(self, n):
        (n,) = n
        return float(n)

    def NAME(self, var):
        return self.vars[var.value]