from lark.visitors import *
from lark import Token
from z3 import *

class SilSpeqZ3FlagInterpreter(Interpreter):
    def __init__(self):
        super().__init__()