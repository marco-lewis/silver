'''
Goal: Take in JSON and make calls to ObligationGenerator
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only

TODO
Handle quantum operations with multiple qubits
Handle conditionals (if statements with quantum)
Deutsch algorithm verification
Deutsch-Jozsa algorithm verification
For loop handling
Grover algorithm verification
Fix quantum registers so they are better
'''

from z3 import *
from Prog import *
from QuantumMemory import QuantumRegister
from QuantumOps import *
from ObligationGenerator import ObilgationGenerator
from complex import Complex, _to_complex
from ComplexVector import ComplexVector
from utils import *

class JSONInterpreter:
    isqrt2 = Real("isqrt2")
    __meas_cert = False

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
        
    def set_meas_cert(self, cert):
        self.__meas_cert = cert

    # TODO: Make enumerations for EXPTYPEs
    # TODO: Move to SilVer class/Remove?
    def decode_json(self, fdefs):
        """
        Generates proof obligations by decoding the JSON file (or using generated specifications)
        """
        # Have functions that contain an array of statements
        # (which may or may not have arrays/objects inside them)
        # Get function name
        for func in fdefs:
            self.obligation_generator = ObilgationGenerator()
            # Generate proof obligations by using information from JSON
            print("Make proof obligations for " + func["func"] + "...")
            self.args = {}
            self.decode_func(func)
            print("Done")

    def decode_func_in_json(self, json, fname):
        try:
            for i in range(len(json)):
                if json[i]["func"] == fname:
                    func_json = json[i]
                    break
        except:
            raise Exception("Function " + fname + " was not detected in json file")
                        
        self.obligation_generator = ObilgationGenerator()
        print("Make proof obligations for " + func_json["func"] + "...")
        self.args = {}
        self.decode_func(func_json)
        print("Done")

        
    def decode_func(self, func_json):
        """
        Generates proof obligation for a function specification

        Args:
            func (dict): dictionary of arguments and statements for a function
        """
        for arg in func_json["args"]:
            # TODO: Handle argument/function types to make appropriate Z3 objects
            if True:
                self.args[arg["name"]] = Function(arg["name"], IntSort(), IntSort())
        # Check arguments and create variables that are needed there (with any pre-conditions if flagged)
        # Make a PO for summary if flagged
        # OR go through statements of function
        for stmt in func_json["statements"]:
            ob = self.decode_statement(func_json["func"], stmt)
            ob = simplify(And(ob))
            self.solver.add(ob)

    def decode_statement(self, fname, stmt):
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
        
        if e == "compoundExp":
            # TODO: Generalize to any list size
            return self.decode_statement(fname, stmt["statements"][0]) if not(stmt["statements"] == []) else True
        
        if e == "callExp":
            op = self._matrix_from_op(stmt["op"])
            arg = self.decode_expression(stmt["arg"])
            return lambda cond: op(arg, cond)
        
        if e == "iteExp":
            # TODO: Handle non-phase cases
            # TODO: Handle othw exp
            cond = self.decode_expression(stmt["cond"])
            then = self.decode_statement(fname, stmt["then"])
            othw = self.decode_statement(fname, stmt["othw"])

            if othw == True:
                var = self._get_var_from_cond(stmt["cond"])
                loc = self.obligation_generator.q_memory.get_loc(var)
                op = self.obligation_generator.make_qubit_operation(then(cond), loc)

                obs = self.obligation_generator.obligation_operation(
                    op,
                    self.obligation_generator.get_prev_quantum_mem()
                )
                self.obligation_generator.update_quantum_memory(var)
                qstate = self.obligation_generator.make_qstate()
                return self.obligation_generator.obligation_quantum_assignment(qstate, obs)
            else:
                pass
                    
        if e == "returnExp":
            # TODO: Handle different function returns (e.g. quantum, classical)
            val = self.obligation_generator.obligation_value(stmt["value"])
            if val == [] or isinstance(val, dict):
                return True
            classical = True
            if classical:
                return [Int(fname + "_ret") == self.obligation_generator.get_cvar(val)]
        
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        # TODO: Change handling of variables (return location or the reference perhaps?)
        if isinstance(exp, str): 
            if exp == "pi": return np.pi
            if self.obligation_generator.q_memory.is_stored(exp):
                return (exp, self.obligation_generator.q_memory.get_loc(exp))
            return (exp, 0)
        e = exp[EXPTYPE]
        
        if e == "varDecl":
            # TODO: Check this is right
            return self.decode_expression(exp["value"])
        
        if e == "indexExp":
            loc = self.obligation_generator.q_memory.get_loc(exp["var"], self.decode_expression(exp["index"]))
            return (exp["var"], loc)
        if e == "callExp":
            # TODO: Handle function calls
            # TODO: Handle multiple variables
            # TODO: Handle non-Pauli gates (single)
            # TODO: Handle index argument
            arg = self.decode_expression(exp["arg"])
            
            if any(exp["op"] == key for key in self.args):
                # TODO: Not hardcode operation to return
                # TODO: Remove assumption of result
                return lambda i: self.args[exp["op"]](i)
                return self.obligation_generator.make_qubit_operation(
                    [[_to_complex(1 - 2 * self.args[exp["op"]](0)), 0],
                     [0, _to_complex(1 - 2 * self.args[exp["op"]](1))]],
                    arg[1])
            
            if exp["op"] == "measure":
                return self.obligation_generator.obligation_quantum_measurement(arg[0], with_certainty= self.__meas_cert)
            
            op = self.obligation_generator.make_qubit_operation(
                self._matrix_from_op(exp["op"]), 
                arg[1])
            obs = lambda var: self.obligation_generator.get_and_update_q_mem(var[0], arg[0])
            return lambda var: self.obligation_generator.obligation_operation(op, obs(var))

        if e == "litExp":
            val = exp["value"]
            return val

        if e == "typeChangeExp":
            # Change obligations from literals depending on type
            val = self.decode_expression(exp["expr"])
            return lambda var: self.obligation_generator.obligation_quantum_literal(var, exp["type"], val)

        raise Exception("TODO: expression " + e)
    
    # TODO: Handle potential other cases (e.g. x == 1)
    def _get_var_from_cond(self, cond):
        return cond["arg"]
    
    def _matrix_from_op(self, op):
        if op == "H": return [[_to_complex(self.isqrt2), _to_complex(self.isqrt2)], 
                              [_to_complex(self.isqrt2), _to_complex(-self.isqrt2)]]
        if op == "X": return X
        if op == "Y": return Y
        if op == "Z'": return Z
        if op == "phase": return lambda arg, cond: self.obligation_generator.make_phase_op(cond, PHASE(arg))
        # if isinstance(op, dict): return self.decode_expression(op)
        raise Exception("OpError: operation " + str(op) + " does not exist.")