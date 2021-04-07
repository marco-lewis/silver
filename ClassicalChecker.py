from z3 import *
import numpy as np
import cmath

class ClassicalChecker:
    def __init__(self, solver):
        self.solver = solver
        self.time_stamp = {}
        self.size = {}
        
# Classical Operations and Handling
    def set_reg(self, name, size=0, val=0):
        s = self.solver
        if not(name in self.time_stamp.keys()) and not(name in self.size.keys()):
            self.time_stamp[name] = -1
            self.size[name] = size
            
        token = name + '_t' + str(self.time_stamp[name] + 1)

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
        else:
            raise Exception("SizeError: size given doesn't match expected size.")
            
    def handle_op(self):
        return False