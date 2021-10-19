from lark.visitors import *
from z3 import *

class SilSpeqInterpreter(Interpreter):
    def __init__(self):
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
        # return stmts
        pass

    @visit_children_decor
    def post(self, stmts):
        # return stmts
        pass

    @visit_children_decor
    def definition(self, df):
        print(df)
        pass

    @visit_children_decor
    def int(self, a):
        if a == []:
            a.append(1)
        return int(a[0])