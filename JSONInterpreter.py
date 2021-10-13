# Goal: Take in JSON and make calls to appropriate checkers
'''
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only
'''

import json
from Prog import *
from QuantumOps import *

expType = "expType"

class JSONInterpreter:
    def __init__(self, file, checkerHandler):
        self.file = file
        
        self.spec_flags = {}
        self.spec_flags["pre"] = False
        self.spec_flags["post"] = False
        self.spec_flags["summary"] = False

        self.qc = checkerHandler.qc
        self.cc = checkerHandler.cc

        self.var_pointer = {}

    def getJSON(self):
        with open(self.file, "r") as rf:
            self.fdefs = rf.read()
            self.fdefs = json.loads(self.fdefs)
            
    def print_data(self):
        print(self.fdefs)


    # Will need to break down
    # TODO: Make enumerations for expTypes
    def decode_json(self):
        # Have functions that contain an array of statements (which may or may not have arrays/objects inside them)
        # 1) Get function name
        for func in self.fdefs:
            # 2) Check if there is a spec file or if spec is empty
            if False: 
                print("There's a spec?!")
                # a) Flag pre/post/summary conditions
            print(func["func"] + " has no spec")

            # 3) Check if there is already a generated PO file
            if False: 
                print("There's a PO file?!")
                # a) If hash of file + spec is the same, just use that
                if False: print("Same hash")
            # 4) Look into JSON and generate proof obligations by using information from JSON
            else:
                print("Make proof obligations")
                for arg in func["args"]:
                    print(arg)
                    # t = arg["type"]
                    # TODO: Handle function types (dw for now)
                    # Detect if classical/quantum and send to relative checker
                    # Create variables (in checkers?)
                # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
                # Make a PO for summary if flagged
                # OR go through statements of function
                for stmt in func["statements"]:
                    self.decode_statement(stmt)
                # At end, check postcondition flag

    def decode_func(self):
        return False

    def decode_statement(self, stmt):
        e = stmt[expType]
        if e == "defineExp":
            # Don't care about LHS? Yes for ops, no for literals
            lhs = stmt["lhs"]
            rhs = self.decode_expression(stmt["rhs"])
            if not(self.qc.is_var(lhs)):
                self.qc.init_new_qreg(lhs, self.size_from_type(rhs["type"]), rhs["expr"])
            else:
                self.apply_op(lhs, rhs)
        if e == "returnExp":
            stmt["value"]
        return False

    def decode_expression(self, exp):
        e = exp[expType]
        if e == "callExp":
            d = {}
            d["arg"] = exp["arg"]
            d["op"] = exp["op"]
            return d
        if e == "litExp":
            return exp["value"]
        if e == "typeChangeExp":
            d = {}
            d["type"] = exp["type"]
            d["expr"] = self.decode_expression(exp["expr"])
            return d
        return False

    def size_from_type(self, type):
        if self.single_type(type):
            return 1
        return 0

    def single_type(self, type):
        return type == "B" or type == "𝔹"

    def apply_op(self, lhs, rhs):
        if rhs["op"] == "H":
            self.qc.apply_H(lhs)
        self.qc.apply_sing_op(self.matrix_from_op(rhs["op"]), lhs)

    def matrix_from_op(self, op):
        if "H": return H
        if "X": return X
        if "Y": return Y
        if "Z": return Z