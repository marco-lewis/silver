'''
Goal: Take in JSON and generate a Program from it
Assumptions:
Variable is only one used in a function
Integers for now only
Quantum variables only
'''

from z3 import *
from Command import *
from Instruction import *
from Program import Program
from QuantumMemory import QuantumMemory
from QuantumOps import *
from utils import *

class JSONInterpreter:
    isqrt2 = Real("isqrt2")

    def __init__(self):
        self.program = Program()
        
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
        return self.make_program(func_json)
        
    def make_program(self, func_json):
        print("Make Program for " + func_json["func"] + "...")
        self.args = {}
        prog = self.decode_func(func_json)
        print("Done")
        return prog
        
    def decode_func(self, func_json):
        for arg in func_json["args"]:
            # TODO: Handle args in program
            pass
        
        for stmt in func_json["statements"]:
            self.decode_statement(func_json["func"], stmt)
        return self.program
            
            
    def decode_statement(self, fname, stmt):
        e = stmt[EXPTYPE]
        
        if e == "defineExp":
            lhs = self.decode_expression(stmt["lhs"])
            rhs = self.decode_expression(stmt["rhs"])
            if isinstance(rhs, QINIT):
                command = QuantumCommand(out_vars=[lhs], instruction=rhs)
                new_memory = self.get_quantum_memory_copy()
                new_memory.append(lhs, rhs.size)
                self.program.add_quantum_process(command, new_memory)
                return 0
            if isinstance(rhs, QOP):
                arg = rhs.arg
                command = QuantumCommand(in_vars=arg, out_vars=lhs,instruction= rhs)
                new_memory = self.get_quantum_memory_copy()
                if arg != lhs:
                    new_memory.update_reg(arg, lhs)
                new_memory.iterate_reg(lhs)
                self.program.add_quantum_process(command, new_memory)
                return 0
            
        if e == "compoundExp":
            pass
        
        if e == "callExp":
            pass
        
        if e == "iteExp":
            pass
                    
        if e == "returnExp":
            # TODO: Have attributes only in command or in_vars?
            # TODO: Separate quantum return from classical?
            command = QuantumCommand(in_vars=stmt['value'], instruction=RETURN(stmt['value']))
            self.program.add_quantum_process(command, QuantumMemory())
            return 0
        
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
            op = exp["op"]
            arg = exp["arg"]
            if self.is_quantum_op(op):
                inst = QOP(op)
                inst.arg = arg
                return inst
        
        if e == "litExp":
            val = exp["value"]
            return val

        if e == "typeChangeExp":
            val = self.decode_expression(exp["expr"])
            type = exp["type"]
            if self.is_function(type):
                pass
            if self.is_classical(type):
                pass
            else:
                # Class?
                return QINIT(val, self.interpret_type(type))

        raise Exception("TODO: expression " + e)
    
    def interpret_type(self, type):
        if type == "𝔹" or type == "B":
            return 1
        
    def is_classical(self, type):
        return False
    
    def is_function(self, type):
        return False
    
    def is_quantum_op(self, op):
        return (op == "Y") or (op == "X") or (op == "Z'") or (op == "H")
    
    def get_quantum_memory_copy(self):
        new_memory = QuantumMemory()
        new_memory.q_mem = copy.deepcopy(self.program.get_current_quantum_memory().q_mem)
        return new_memory