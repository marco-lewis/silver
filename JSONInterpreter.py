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

from z3 import *
from Prog import *
from QuantumOps import *
from ObligationGenerator import ObilgationGenerator
from complex import Complex, _to_complex
from ComplexVector import ComplexVector
from utils import *

class JSONInterpreter:
    isqrt2 = Real("isqrt2")

    def __init__(self, solver=Solver()):
        self.spec_flags = {}
        self.spec_flags["pre"] = False
        self.spec_flags["post"] = False
        self.spec_flags["summary"] = False

        if not isinstance(solver, Solver):
            raise Exception("InterpreterError: solver is not a Solver")
        self.solver = solver
        self.solver.add((1 / self.isqrt2)**2  == 2, self.isqrt2 > 0)

        self.args = {}

    # TODO: Make enumerations for EXPTYPEs
    # TODO: Move to SilVer class(?)
    def decode_json(self, fdefs):
        """
        Generates proof obligations by decoding the JSON file (or using generated specifications)
        """
        # Have functions that contain an array of statements
        # (which may or may not have arrays/objects inside them)
        # 1) Get function name
        for func in fdefs:
            self.obligation_generator = ObilgationGenerator()
            # 2) Check if there is a spec file or if spec is empty
                # a) Flag pre/post/summary conditions
            print(func["func"] + " has no spec")

            # 3) Check if there is already a generated PO file
            if False: 
                print("There's a PO file?!")
                # a) If hash of file + spec is the same, just use that
                if False: print("Same hash")
            # 4) Look into JSON and generate proof obligations by using information from JSON
            else:
                print("Make proof obligations for " + func["func"] + "...")
                self.args = {}
                self.decode_func(func)
                print("Done")

    def decode_func(self, func):
        """
        Generates proof obligation for a function specification

        Args:
            func (dict): dictionary of arguments and statements for a function
        """
        for arg in func["args"]:
            # TODO: Handle argument/function types to make appropriate Z3 objects
            if True:
                self.args[arg["name"]] = Function(arg["name"], IntSort(), IntSort())
        # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
        # Make a PO for summary if flagged
        # OR go through statements of function
        for stmt in func["statements"]:
            ob = self.decode_statement(stmt)
            ob = simplify(And(ob))
            self.solver.add(ob)

    def decode_statement(self, stmt):
        e = stmt[EXPTYPE]
        if e == "defineExp":
            # TODO: Change handling of lhs and rhs
            # Need to separate handling of logic/variable names and generation of obligations
            # I.e. need to unwrap lhs to get key details
            lhs = self.decode_expression(stmt["lhs"])
            rhs = self.decode_expression(stmt["rhs"])(lhs)

            if all(isinstance(r, BoolRef) for r in rhs):
                return rhs
            qstate = self.obligation_generator.make_qstate()
            return self.obligation_generator.obligation_quantum_assignment(qstate, rhs)
        if e == "iteExp":
            # TODO: Get cond and work out variables used
            # TODO: Get statement matrix
            # TODO: Make obligation
            # TODO: Handle othw exp
            rhs = self.obligation_generator.obligation_operation(
                self.decode_expression(stmt["cond"]),
                self.obligation_generator.get_prev_quantum_mem())
            self.obligation_generator.get_and_update_q_mem(stmt["cond"]["arg"])
            qstate = self.obligation_generator.make_qstate()
            return self.obligation_generator.obligation_quantum_assignment(qstate, rhs)
        if e == "returnExp":
            val = self.obligation_generator.obligation_value(stmt["value"])
            if val == []:
                return True
            pass
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        # TODO: Change handling of variables (return location or the reference perhaps?)
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
            arg = self.decode_expression(exp["arg"])
            if any(exp["op"] == key for key in self.args):
                # TODO: Not hardcode operation to return
                return self.obligation_generator.make_qubit_operation(
                    [[_to_complex(1 - 2 * self.args[exp["op"]](0)), 0],
                     [0, _to_complex(1 - 2 * self.args[exp["op"]](1))]],
                    arg)
            if exp["op"] == "measure":
                return self.obligation_generator.obligation_quantum_measurement(arg)
            op = self.obligation_generator.make_qubit_operation(
                self._matrix_from_op(exp["op"]), 
                arg)
            obs = lambda var: self.obligation_generator.get_and_update_q_mem(var, arg)
            return lambda var: self.obligation_generator.obligation_operation(op, obs(var))
        if e == "litExp":
            val = exp["value"]
            return val
        if e == "typeChangeExp":
            # Change obligations from literals depending on type
            val = self.decode_expression(exp["expr"])
            return lambda var: self.obligation_generator.obligation_quantum_literal(var, exp["type"], val)
        raise Exception("TODO: expression " + e)
    
    def _matrix_from_op(self, op):
        if op == "H": return [[_to_complex(self.isqrt2), _to_complex(self.isqrt2)], 
                              [_to_complex(self.isqrt2), _to_complex(-self.isqrt2)]]
        if op == "X": return X
        if op == "Y": return Y
        if op == "Z'": return Z
        raise Exception("OpError: operation " + str(op) + " does not exist.")