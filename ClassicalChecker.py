from z3 import *
import numpy as np
import cmath

class ClassicalChecker:
    def __init__(self, solver):
        self.solver = solver
        self.time_stamp = {}
        self.size = {}
        self.memory = {}
        
    def token(self, name):
        return  name + '_t' + str(self.time_stamp[name] + 1)
        
# Classical Operations and Handling
    
    # Z3 can't handle things like:
    # y == sin(x) (or other trig functions, can bake in) - consider dreal?
    # Can handle:
    # y = exp(x) (np.exp(1)**x),
    # Handling of trig, exp, sqrt, abs, round with type !R can be done in here
    # For the moment, assume x = op(x)
    def set_reg(self, name, size=0, val=0):
        s = self.solver
        if not(name in self.time_stamp.keys()) and not(name in self.size.keys()):
            self.time_stamp[name] = -1
            self.size[name] = size

        token = self.token(name);
            
        if self.size[name] == size:
            if size == 0:
                var = Real(token)
                s.add(var == val)
            else:
                #  Variable is some array of bits
                var = RealVector(token, size)
                for i in range(size):
                    s.add(var[i] == int(bool((val & 1<<i))))
                
            self.time_stamp[name] += 1
            self.memory[name] = var
        else:
            raise Exception("SizeError: size given doesn't match expected size.")
            
    def handle_real_op(self, op, name, val):
        s = self.solver
        token = self.token(name);
        if not(self.size[name] == 0) :
            raise Exception("SizeError: expected a real number, not a B, int or uint")

        var = Real(token)
        s.add(var == op(val))
        self.memory[name] = var
        self.time_stamp[name] += 1