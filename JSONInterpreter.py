# Goal: Take in JSON and convert to Z3 using Python API
import json
from typing import Match
from Prog import *

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
            # Handle expressions
            lhs = stmt["lhs"]
            rhs_call = self.decode_expression(stmt["rhs"])
        if e == "returnExp":
            stmt["value"]
        return False

    def decode_expression(self, exp):
        e = exp[expType]
        if e == "callExp":
            exp["arg"]
            exp["op"]
        if e == "litExp":
            exp["value"]
        if e == "typeChangeExp":
            exp["expr"]
            exp["consume"]
            exp["type"]
        return False