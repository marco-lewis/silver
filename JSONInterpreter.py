'''
Goal: Take in JSON and generate a Program from it
Assumptions:
Variable is only one used in a function
Integers for now only
(Mostly) Quantum variables only
'''

from lib2to3.pgen2.token import RIGHTSHIFT
from z3 import *
from ClassicalMemory import ClassicalMemory
from utils import *

from Instruction import *
from Program import Program
from QuantumMemory import QuantumMemory
from QuantumOps import *
from VarRef import VarRef

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
        
    def make_program(self, func_json, verbose = False):
        if verbose: print("Make Program for " + func_json["func"] + "...")
        self.func_arg = {}
        prog = self.decode_func(func_json)
        if verbose: print("Done")
        return prog
        
    def decode_func(self, func_json):
        for arg in func_json["args"]:
            # TODO: Handle non-function args in program
            func = Function(arg['name'], convert_type_to_Z3_literal(arg['type']))
            self.func_arg[arg['name']] = func
        
        for stmt in func_json["statements"]:
            self.controls = []
            self.decode_statement(func_json["func"], stmt)
        return self.program
            
            
    def decode_statement(self, fname, stmt):
        e = stmt[EXPTYPE]
        
        if e == "defineExp":
            lhs = self.decode_expression(stmt["lhs"])
            rhs = self.decode_expression(stmt["rhs"])
            if isinstance(rhs, QINIT):
                instruction = rhs
                instruction.variable = lhs
                self.add_qinit(instruction)
                return 0
            if isinstance(rhs, QOP):
                rhs.out = lhs
                instruction = rhs
                if isinstance(instruction.arg, QINIT):
                    qinit = instruction.arg
                    qinit.variable = instruction.out
                    self.add_qinit(qinit)
                    instruction.arg = instruction.out
                self.add_qop(instruction)
                return 0
            if isinstance(rhs, QMEAS):
                rhs.classical_ref = lhs
                instruction = rhs
                # TODO: Move into program statement?
                new_memory = self.get_quantum_memory_copy()
                new_memory.measure_reg(instruction.quantum_ref.variable)
                new_memory.iterate_all()
                classical_instruction = CMEAS(instruction.quantum_ref, lhs)
                self.program.add_quantum_to_classical(instruction, new_memory, classical_instruction, copy.deepcopy(self.controls))
                return 0
            
        if e == "compoundExp":
            for stmt in stmt["statements"]:
                self.decode_statement(fname, stmt)
            return 0
        
        if e == "callExp":
            # TODO: Move repeated code
            # Handle PHASE
            op = stmt['op']
            arg = self.decode_expression(stmt['arg'])
            if self.is_quantum_op(op):
                pass
            if self.is_phase(op):
                instruction = QPHASE(arg)
                new_memory = self.get_quantum_memory_copy()
                new_memory.iterate_all()
                self.program.add_quantum_process(instruction, new_memory, controls=copy.deepcopy(self.controls))
                return 0
        
        if e == "iteExp":
            # TODO: Handle decode of cond separately
            cond = self.decode_expression(stmt['cond'])
            print(cond)
            self.controls.append(cond)
            self.decode_statement(fname, stmt['then'])
            # self.decode_statement(fname, stmt['othw'])
            self.controls.pop()
            return 0
                    
        if e == "returnExp":
            # TODO: Have attributes only in command or in_vars?
            # TODO: Check whether quantum return or classical return
            vals = self.decode_expression(stmt['value'])
            instruction = RETURN(vals, fname)
            if all([self.program.is_variable_ref_quantum(val) for val in vals]):
                self.program.add_quantum_process(instruction, QuantumMemory())
            else: self.program.add_classical_process(instruction, ClassicalMemory())
            return 0
        
        if e == "forgetExp":
            # TODO: Handle classical/quantum forget, assume quantum for now
            variable = self.decode_expression(stmt['var'])
            value = self.decode_expression(stmt['val'])
            instruction = QFORGET(variable, value)
            new_memory = self.get_quantum_memory_copy()
            new_memory.measure_reg(variable.variable)
            new_memory.iterate_all()
            self.program.add_quantum_process(instruction, new_memory, self.controls)
            return 0
        
        raise Exception("TODO: statement " + e)


    def decode_expression(self, exp):
        if isinstance(exp, str):
            if exp == "pi": return math.pi
            return VarRef(exp)
        if isinstance(exp, list):
            return [self.decode_expression(e) for e in exp]

        e = exp[EXPTYPE]
        if e == "varDecl":
            pass
        if e == "indexExp":
            # TODO: Handle non-const index
            idx = self.decode_expression(exp["index"])
            var_ref = self.decode_expression(exp["var"])
            var_ref.index = idx
            return var_ref
        if e == "callExp":
            op = exp["op"]
            arg = self.decode_expression(exp["arg"])
            if self.is_quantum_op(op):
                inst = QOP(op)
                inst.arg = arg
                return inst
            if self.is_arg(op):
                inst = QOP(self.func_arg[op])
                inst.arg = arg
                return inst
            if op == 'measure':
                inst = QMEAS(arg)
                return inst
        if e == "litExp":
            val = exp["value"]
            return val
        if e == "tupleExp":
            return self.decode_expression(exp["values"])

        if e == "typeChangeExp":
            val = self.decode_expression(exp["expr"])
            type = exp["type"]
            if self.is_function(type):
                pass
            if self.is_classical(type):
                pass
            else:
                return QINIT(val, self.interpret_type(type))

        raise Exception("TODO: expression " + e)
    
    def add_qinit(self, instruction : QINIT):
        new_memory = self.get_quantum_memory_copy()
        new_memory.append(instruction.variable.variable, instruction.size)
        self.program.add_quantum_process(instruction, new_memory, copy.deepcopy(self.controls))    
    
    def add_qop(self, instruction : QOP):
        new_memory = self.get_quantum_memory_copy()
        if instruction.arg != instruction.out:
            new_memory.update_reg(instruction.arg.variable, instruction.out.variable)
        new_memory.iterate_reg(instruction.out.variable)
        self.program.add_quantum_process(instruction, new_memory, copy.deepcopy(self.controls))
    
    def interpret_type(self, type):
        if 'typeObj' in type:
            if type['typeObj'] == "𝔹" or type['typeObj'] == "B":
                return 1
            if type['typeObj'] == 'uint':
                return self.decode_expression(type['size'])
            pass
        # Deprecrated (need to update JSONs if this still used)
        if type == "𝔹" or type == "B":
            return 1
        raise Exception("TypeError: unable to handle type ", type)
        
    def is_arg(self, ref):
        return ref in self.func_arg

    def is_classical(self, type):
        return False
    
    def is_function(self, type):
        return False
    
    def is_quantum_op(self, op):
        return (op == "Y") or (op == "X") or (op == "Z'") or (op == "H")
    
    def is_phase(self, op):
        return (op == "phase")
    
    def get_quantum_memory_copy(self):
        new_memory = QuantumMemory()
        new_memory.q_mem = copy.deepcopy(self.program.get_current_quantum_memory().q_mem)
        return new_memory