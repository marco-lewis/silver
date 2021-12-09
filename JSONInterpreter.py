'''
Goal: Take in JSON and generate a Program from it
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only
'''

from z3 import *
from Prog import *
from QuantumOps import *
from utils import *

class JSONInterpreter:
    isqrt2 = Real("isqrt2")

    def __init__(self):
        pass
        
    # TODO: Make enumerations for EXPTYPEs
    # TODO: Move to SilVer class/Remove?
    def decode_json(self, fdefs):
        # Have functions that contain an array of statements
        # (which may or may not have arrays/objects inside them)
        # Get function name
        for func_json in fdefs:
            # Generate proof obligations by using information from JSON
            self.make_program(func_json)


    def decode_func_in_json(self, json, fname):
        try:
            for i in range(len(json)):
                if json[i]["func"] == fname:
                    func_json = json[i]
                    break
        except:
            raise Exception("Function " + fname + " was not detected in json file")
        self.make_program(func_json)
        
    def make_program(self, func_json):
        print("Make Program for " + func_json["func"] + "...")
        self.args = {}
        self.decode_func(func_json)
        print("Done")

        
    def decode_func(self, func_json):
        for arg in func_json["args"]:
            # TODO: Handle args in program
            pass
        
        # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
        # Make a PO for summary if flagged
        # OR go through statements of function
        for stmt in func_json["statements"]:
            self.decode_statement(func_json["func"], stmt)
            # Make changes here
            
            
    def decode_statement(self, fname, stmt):
        e = stmt[EXPTYPE]
        
        if e == "defineExp":
            lhs = self.decode_expression(stmt["lhs"])
            rhs = self.decode_expression(stmt["rhs"])
        
        if e == "compoundExp":
            pass
        
        if e == "callExp":
            op = self._matrix_from_op(stmt["op"])
            arg = self.decode_expression(stmt["arg"])
        
        if e == "iteExp":
            pass
                    
        if e == "returnExp":
            pass
        
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        if isinstance(exp, str):
            return exp

        e = exp[EXPTYPE]
        if e == "varDecl":
            pass
        if e == "indexExp":
            pass
        if e == "callExp":
            pass
        
        if e == "litExp":
            val = exp["value"]
            return val

        if e == "typeChangeExp":
            pass

        raise Exception("TODO: expression " + e)