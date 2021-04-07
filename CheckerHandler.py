from z3 import *
from QuantumChecker import QuantumChecker
from ClassicalChecker import ClassicalChecker

class CheckerHandler:
    def __init__(self):
#     Initialise a solver
        self.solver = Solver()
        self.qc = QuantumChecker(self.solver)
        self.cc = ClassicalChecker(self.solver)
        
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

#     Return all valid models
    def get_all_models():
        return False
    
    def add_constraint(self, conds):
        self.solver.add(conds)
        
    def get_smt2lib(self):
        return self.solver.to_smt2()
