from os import R_OK
from lark.visitors import *
from lark import Token
import logging
import numpy as np
from z3 import *

from ..silver.utils import log_error

logger = logging.getLogger('silspeq')
def error(error_msg, *args): log_error(error_msg, logger) if len(args) == 0 else log_error(error_msg, logger, *args)

def Equiv(a, b):
    return And(Implies(a, b), Implies(b, a))

NAT = "NAT"
UNIT = ()
BOOL = "BOOL"
FUNC = "FUNC"
CLASSICAL = "CLASSICAL"

class SilSpeqZ3Interpreter(Interpreter):  
    def __init__(self, not_post : bool = True):
        self.vars = {}
        self.types = {}
        self.not_post = not_post
        self.assumptions = []
        self.__meas_cert = False
        super().__init__()

    def set_meas_cert(self, val): self.__meas_cert = val

    # Handling pre, post, spec etc.
    @visit_children_decor
    def specs(self, specs):
        d = {}
        for spec in specs:
            func_spec = [s for s in spec[1:] if s != None]
            d[spec[0].value] = self.flatten(func_spec)
            d[spec[0].value] = self.simplify_list(d[spec[0].value])
        return d
    
    def simplify_list(self, spec):
        temp = []
        for obl in spec:
            if isinstance(obl, bool): temp.append(obl)
            else: temp.append(simplify(obl))
        return temp

    def flatten(self, old): return self.__flatten(old, [])

    # Inspiration: https://stackoverflow.com/questions/12472338/flattening-a-list-recursively
    def __flatten(self, old, new):
        for i in old: self.__flatten(i, new) if isinstance(i, list) else new.append(i)
        return new

    @visit_children_decor
    def funcspec(self, tree): return tree

    @visit_children_decor
    def pre(self, stmts): return stmts

    @visit_children_decor
    def post(self, stmts):
        if not(stmts == [[]]):
            obls = []
            stmts = self.flatten(stmts)
            for obl in stmts:
                if obl != None: obls.append(obl)
            post_obl = And(obls)
            if self.__meas_cert: post_obl = And(post_obl, Bool('meas_cert') == self.__meas_cert)
            post_obl = simplify(post_obl)
            return Not(post_obl) if self.not_post else post_obl
        return True
        
    # Handling definitions and statements
    # TODO: Add more types
    # TODO: Separate type handling into another function
    @visit_children_decor
    def definition(self, df):
        # Ignore flag
        if df[0] == None: df = df[1:]
        
        var = df[0].value
        self.types[var] = df[1]
        if df[1] == UNIT: return True
        elif df[1] == NAT:
            self.vars[var] = Int(var)
            return self.vars[var] >= 0
        elif df[1] == BOOL:
            self.vars[var] = Int(var)
            return Or(self.vars[var] == 0, self.vars[var] == 1)
        elif isinstance(df[1], list): return self.function_obligation(var, self.flatten(df[1]))
        else:
            self.vars[var] = Int(var)
            return And(0 <= self.vars[var], self.vars[var] < 2**df[1])

    # TODO: Test with tuples/arrays types?
    def function_obligation(self, fname, typing):
        self.vars[fname] = Function(fname, [IntSort() for typ in typing])
        out_obl = self.mass_out_obl(typing[:-1], fname, typing[-1], [])
        return simplify(And(out_obl))

    def mass_out_obl(self, in_types, fname, out_type, inputs : list):
        out = []
        if in_types == []: return self.type_obligation(self.vars[fname](inputs), out_type)
        else:
            for i in range(self.type_size(in_types[0])):
                temp = inputs
                temp.append(i)
                out.append(self.mass_out_obl(in_types[1:], fname, out_type, temp))
                temp.pop()
            return out

    def type_size(self, type):
        if type == NAT: error("Unable to handle NAT argument")
        elif type == BOOL: return 2
        else: return 2**type

    def type_obligation(self, z3_expr, type):
        if type == NAT:
            return z3_expr >= 0
        elif type == BOOL:
            return Or(z3_expr == 0, z3_expr == 1)
        else:
            return And(0 <= z3_expr, z3_expr < 2**type)

    @visit_children_decor
    def assertion(self, zexpr): return zexpr
    
    @visit_children_decor
    def assumption(self, zexpr):
        self.assumptions.append(zexpr)
        return True
    
    # Ignore most flags
    def rand(self, v): return []
    def qout(self, v): return []
    def oracle(self, v): return []
    def cert(self, v): return []
    def whp(self, v): return []
    def whpvalue(self, v): return []
    @visit_children_decor
    def atvalue(self, v): return v

    # Handling types
    def nat(self, a): return NAT

    def bool(self, a): return BOOL
    
    def unit(self, a): return UNIT
    
    @visit_children_decor
    def int(self, n):
        if n == []:
            return 1
        if n[0] == BOOL: return int(n[1])
        return int(n[0].value)
    
    def classical(self, a): return CLASSICAL

    @visit_children_decor
    def function(self, types): return types

    # Handling lexpr
    true = lambda self,_: True
    false = lambda self,_: False

    @visit_children_decor
    def eq(self, lexprs): return lexprs[0] == lexprs[1]

    @visit_children_decor
    def gt(self, nexprs): return nexprs[0] > nexprs[1]

    @visit_children_decor
    def lt(self, nexprs): return nexprs[0] < nexprs[1]

    @visit_children_decor
    def ge(self, nexprs): return nexprs[0] >= nexprs[1]

    @visit_children_decor
    def le(self, nexprs): return nexprs[0] <= nexprs[1]

    @visit_children_decor
    def land(self, lexprs): return And(lexprs[0], lexprs[1])

    @visit_children_decor
    def lor(self, lexprs): return Or(lexprs[0], lexprs[1])

    @visit_children_decor
    def implies(self, lexprs): return Implies(lexprs[0], lexprs[1])

    @visit_children_decor
    def equiv(self, lexprs): return Equiv(lexprs[0], lexprs[1])

    @visit_children_decor
    def distinct(self, args):
        args = self.flatten(args)
        return simplify(Distinct(args), blast_distinct=True)

    @visit_children_decor
    def lnot(self, lexpr): return Not(lexpr[0])

    @visit_children_decor
    def forall(self, lexpr): return ForAll([self.token(lexpr[0])], lexpr[1])

    @visit_children_decor
    def exists(self, lexpr): return Exists([self.token(lexpr[0])], lexpr[1])

    # Handling numexpr
    @visit_children_decor
    def neg(self,expr): return - self.handle_token(expr[0])

    @visit_children_decor
    def add(self,exprs): return self.handle_token(exprs[0]) + self.handle_token(exprs[1])

    @visit_children_decor
    def sub(self,exprs): return self.handle_token(exprs[0]) - self.handle_token(exprs[1])

    @visit_children_decor
    def mul(self,exprs): return self.handle_token(exprs[0]) * self.handle_token(exprs[1])

    @visit_children_decor
    def div(self,exprs): return self.handle_token(exprs[0]) / self.handle_token(exprs[1])

    @visit_children_decor
    def pow(self,exprs): return self.handle_token(exprs[0]) ** self.handle_token(exprs[1])

    @visit_children_decor
    def xor(self,exprs):
        v1 = self.handle_token(exprs[0])
        v2 = self.handle_token(exprs[1])
        t1 = self.types[v1.__str__()]
        t2 = self.types[v2.__str__()]
        if t1 >= t2: bits = t1
        else: bits = t2
        v1, v2 = Int2BV(v1, bits), Int2BV(v2, bits)
        term = v1 ^ v2
        return BV2Int(term)

    @visit_children_decor
    def mod(self,exprs): return self.handle_token(exprs[0]) % int(self.handle_token(exprs[1]))

    @visit_children_decor
    def dot(self,exprs):
        l = self.handle_token(exprs[0])
        r = self.handle_token(exprs[1])
        def extract_num_bits(x):
            try: return self.types[x.__str__()]
            except: return int(np.ceil(np.log2(x))) if not(x == 0) else 1
        tl = extract_num_bits(l)
        tr = extract_num_bits(r)
        i = max(tl, tr)
        s = (l % 2) * (r % 2)
        for j in range(1,i):
            lterm = (l / 2**j)
            rterm = (r / 2**j)
            s += (lterm*rterm) % 2
        return s

    @visit_children_decor
    def call(self, call): return self.handle_token(call[0])([self.handle_token(input) for input in call[1]])

    @visit_children_decor
    # TODO: get sum working nicely works
    def sum(self, expr):
        body = lambda x: expr[1](x)
        idx_type = self.types[str(self.token(expr[0]))]
        if idx_type == NAT: error("Can't use natural numbers as a parameter for sum")
        elif idx_type == BOOL: return Sum([body(i) for i in range(0,2)])
        else: return Sum([body(i) for i in range(0, 2**idx_type)])

    # Handling variables
    @visit_children_decor
    def var(self, expr): return self.token(expr[0])

    # Handling tokens and fetching Z3 variables
    def handle_token(self, t):
        if isinstance(t, Token): return self.token(t)
        else: return t

    def token(self, tok: Token):
        if tok.type == "NUMBER": return self.NUMBER(tok)
        if tok.type == "NAME": return self.NAME(tok)

    def NUMBER(self, n: Token): return float(n.value)

    def NAME(self, var: Token): return self.vars[var.value]