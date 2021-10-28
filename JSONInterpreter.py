'''
Goal: Take in JSON and make calls to ObligationGenerator
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only

TODO
Handle quantum operations with multiple qubits
Handle measurement + return
Handle conditionals (if statements with quantum)
Import SilSpeq obligations
Deutsch algorithm verification
Deutsch-Jozsa algorithm verification
For loop handling
Grover algorithm verification
Fix quantum registers so they are better
'''

import json
from z3 import *
from Prog import *
from QuantumOps import *
from ObligationGenerator import ObilgationGenerator
from complex import Complex, _to_complex
from ComplexVector import ComplexVector
from utils import *

class JSONInterpreter:
    isqrt2 = Real("isqrt2")
    obligation_generator = ObilgationGenerator()

    def __init__(self, silq_json_file, solver=Solver()):
        self.silq_json_file = silq_json_file
        
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
        """
        Reads the JSON silq file and stores the data in fdefs.
        """
        with open(self.silq_json_file, "r") as rf:
            self.fdefs = rf.read()
            self.fdefs = json.loads(self.fdefs)
            
    def print_data(self):
        print(self.fdefs)


    # Will need to break down
    # TODO: Make enumerations for EXPTYPEs
    def decode_json(self):
        """
        Generates proof obligations by decoding the JSON file (or using generated specifications)
        """
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
                self.decode_func(func)


    def decode_func(self, func):
        """
        Generates proof obligation for a function specification

        Args:
            func (dict): dictionary of arguments and statements for a function
        """
        for arg in func["args"]:
            print(arg)
            # t = arg["type"]
            # TODO: Handle function types (handle arguments a bit later)
        # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
        # Make a PO for summary if flagged
        # OR go through statements of function
        for stmt in func["statements"]:
            ob = self.decode_statement(stmt)
            ob = simplify(And(ob))
            self.solver.add(ob)
            print(self.solver.assertions())

    def decode_statement(self, stmt):
        e = stmt[EXPTYPE]
        if e == "defineExp":
            # TODO: Change handling of lhs and rhs
            # Need to separate handling of logic/variable names and generation of obligations
            # I.e. need to unwrap lhs to get key details
            lhs = self.decode_expression(stmt["lhs"])
            rhs = self.decode_expression(stmt["rhs"])(lhs)

            qstate = self.obligation_generator.make_qstate()
            return self.obligation_generator.obligation_quantum_assignment(qstate, rhs)
        if e == "returnExp":
            val = self.obligation_generator.obligation_value(stmt["value"])
            if val == []:
                return True
            pass
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        # TODO: Arrange better way to handle literal expressions
        if isinstance(exp, str): return exp
        e = exp[EXPTYPE]
        if e == "varDecl":
            # TODO: Check this is right
            return self.decode_expression(exp["value"])
        if e == "indexExp":
            print(exp["var"], exp["index"]["value"])
            pass
        if e == "callExp":
            # TODO: Handle non-Pauli gates/multiple variables
            arg = exp["arg"]
            obs = lambda var: self.obligation_generator.get_and_update_q_mem(var, arg)
            op = self.obligation_generator.make_qubit_operation(
                self._matrix_from_op(exp["op"]), 
                arg)
            return lambda var: self.obligation_generator.obligation_operation(op, obs(var))
        if e == "litExp":
            # Have this return the value instead?
            val = exp["value"]
            return val
        if e == "typeChangeExp":
            # Change obligations from literals depending on type
            val = self.decode_expression(exp["expr"])
            return lambda var: self.obligation_generator.obligation_quantum_literal(var, exp["type"], val)
        raise Exception("TODO: expression " + e)
    
    def _size_from_type(self, type):
        if self._single_type(type):
            return 1
        return 0

    def _matrix_from_op(self, op):
        if op == "H": return [[_to_complex(self.isqrt2), _to_complex(self.isqrt2)], [_to_complex(self.isqrt2), _to_complex(-self.isqrt2)]]
        if op == "X": return X
        if op == "Y": return Y
        if op == "Z'": return Z
        raise Exception("OpError: operation " + str(op) + " does not exist.")