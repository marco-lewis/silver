# Goal: Take in JSON and make calls to ObligationGenerator
'''
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only
'''

import json
from z3 import *
from Prog import *
from QuantumOps import *
from ObligationGenerator import ObilgationGenerator
from ComplexVector import ComplexVector

expType = "expType"

class JSONInterpreter:
    isqrt2 = Real("isqrt2")
    obligation_generator = ObilgationGenerator()

    def __init__(self, file, solver):
        self.file = file
        
        self.spec_flags = {}
        self.spec_flags["pre"] = False
        self.spec_flags["post"] = False
        self.spec_flags["summary"] = False

        if not isinstance(solver, Solver):
            raise Exception("InterpreterError: solver is not a Solver")
        self.solver = solver
        self.solver.add((1 / self.isqrt2)**2  == 2, self.isqrt2 > 0)

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
                # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
                # Make a PO for summary if flagged
                # OR go through statements of function
                for stmt in func["statements"]:
                    ob = self.decode_statement(stmt)
                    ob = simplify(And(ob))
                    self.solver.add(ob)
                    print(self.solver)
                # At end, check postcondition flag

    def decode_func(self):
        return False

    def decode_statement(self, stmt):
        e = stmt[expType]
        if e == "defineExp":
            lhs = stmt["lhs"]
            q_referencer = self.obligation_generator.quantum_referencer
            if not(q_referencer.is_stored(lhs)):
                q_referencer.add(lhs, 1)
            rhs = self.decode_expression(stmt["rhs"])
            q_referencer.iterate_var(lhs)
            qstate = self.obligation_generator.make_qstate(q_referencer.get_obligation_variables())
            return self.obligation_generator.obligation_quantum_assignment(qstate, rhs)
        if e == "returnExp":
            stmt["value"]
            pass
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        e = exp[expType]
        if e == "callExp":
            # TODO: Generate appropriate matrix from operation
            # TODO: Sort out arguments
            arg = exp["arg"]
            obs = self.obligation_generator.make_qstate(self.obligation_generator.quantum_referencer.get_obligation_variables())
            op = self.matrix_from_op(exp["op"])
            return self.obligation_generator.obligation_operation(op, obs)
        if e == "litExp":
            val = exp["value"]
            return self.obligation_generator.obligation_quantum_literal(val)
        if e == "typeChangeExp":
            # TODO: Something with exp["type"]
            return self.decode_expression(exp["expr"])
        raise Exception("TODO: expression " + e)

    def size_from_type(self, type):
        if self.single_type(type):
            return 1
        return 0

    def single_type(self, type):
        return type == "B" or type == "𝔹"

    def matrix_from_op(self, op):
        if op == "H": return [[self.isqrt2, self.isqrt2], [self.isqrt2, -self.isqrt2]]
        if op == "X": return X
        if op == "Y": return Y
        if op == "Z": return Z