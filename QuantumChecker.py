from z3 import *
import numpy as np
from complex import Complex, I
from ComplexVector import ComplexVector
import cmath

class QuantumChecker:
    def __init__(self):
        self.solver = Solver()
        self.t = 0
        self.qvars = []
        
    def check_solver(self):
        return self.solver.check()
    
    def print_solver(self):
        print(self.solver)
    
    def print_model(self):
        c = self.solver.check()
        if c == sat:
            m = self.solver.model()
            print(m)
        else:
            print("No model to print. Solver returned: " + str(c))
            
    def get_model(self):
        return self.solver.model()
    
    def add_constraint(self, conds):
        self.solver.add(conds)
            
    def init_new_reg(self, n):
        s = self.solver
        self.N = 2**n
        self.qs = ComplexVector('t' + str(self.t) + '_q', self.N)
        for i in range(self.N):
            q = self.qs[i]
            if (i != 0): s.add(q == 0 + 0*I)
            else: s.add(q == 1 + 0*I)
                            
    def apply_op(self, U):
        if (U.shape[0] != self.N or U.shape[1] != self.N):
            print(U.shape, self.N)
            raise Exception('Error: U not right shape')
        s = self.solver
        
        next_stamp = 't' + str(self.t + 1) + '_q'
        new_qs = ComplexVector(next_stamp, self.N)
        
        for num in range(self.N):
            qr = new_qs[num].r
            qi = new_qs[num].i
            
            s.add(qr == Sum([U.real[num][j] * self.qs[j].r - U.imag[num][j] * self.qs[j].i 
                             for j in range(self.N)]))
            s.add(qi == Sum([U.imag[num][j] * self.qs[j].r + U.real[num][j] * self.qs[j].i
                             for j in range(self.N)]))
        
        self.t += 1
        self.qs = new_qs
        
#     Return all valid models
    def get_all_models():
        return False