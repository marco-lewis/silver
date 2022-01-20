from genericpath import exists
import json as json
from os.path import splitext
import subprocess

from z3.z3 import *

from ClassicalMemory import ClassicalMemory
from Instruction import Instruction
from JSONInterpreter import JSONInterpreter
from MeasureOptions import MEASURE_OPTION, CERTAINTY, HIGH_PROB, MeasureOptions
from ObligationGenerator import ObilgationGenerator
from Program import Program
from QuantumMemory import QuantumMemory
from silspeq.SilSpeqParser import SilSpeqParser
from silspeq.SilSpeqZ3FlagVisitor import SilSpeqZ3FlagVisitor
from silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from SpeqGenerator import SpeqGenerator

class SilVer:
    def __init__(self):
        self.solver = Solver()
        self.json_interp = JSONInterpreter()
        self.speq_parser = SilSpeqParser()
        # TODO: Move so that Interpreters are only function specific
        self.speq_z3_itp = SilSpeqZ3Interpreter()
        self.speq_flag_itp = SilSpeqZ3FlagVisitor()
        self.config = {}
    
    def check_speq_exists(self, file):
        if not(exists(self.get_speq_file_name(file))):
            self.generate_speq_file(file)
            raise Exception("New SilSpeq file created, you should add your specification before continuing")
        
    def reset(self):
        self.solver.reset()
        self.json_interp = JSONInterpreter()
        
    def check_solver_sat(self):
        return self.solver.check()
        
    def print_solver_sat(self, solver_sat):
        print("Checking satisfiability...")
        if solver_sat == sat:
            m = self.solver.model()
            print("Counterexample found")
            print(m)
        elif solver_sat == unsat:
            print("Program is correct!")
        else:
            print("Unable to determine if satisfiable")
            print(sat)
            
    def check_flags(self, file):
        tree = self.speq_parser.parse_file(file)
        self.speq_flag_itp.visit(tree)
        
        if self.speq_flag_itp.meas_cert: self.config[MEASURE_OPTION] = CERTAINTY
        else: self.config[MEASURE_OPTION] = HIGH_PROB
        self.speq_z3_itp.set_meas_cert(self.speq_flag_itp.meas_cert)
        
        if self.speq_flag_itp.quantum_out:
            pass
    
    def verify_slq_file(self, silq_file):
        # Call silq with this command to get ast
        # Make sure ast is stored in a hidden folder
        # Run one of the other commands on this file
        pass
    
    def verify_json_file(self, file):
        # 1) Check file is a valid JSON file
        # 2) Generate speq file if it doesn't already exist
        # 3) Rank functions by looking into JSON
        # 4) Verify functions in order. Stop if something is wrong
            # 4a) Produce obligation/sat(?) files for correct functions
        pass
    
    def verify_func(self, file, func, verbose=False):
        print("Verifying " + func + " in " + file)
        self.check_speq_exists(file)
        spq_name = self.get_speq_file_name(file)
        self.check_flags(spq_name)
        
        if verbose: print("Adding isqrt2...")
        isqrt2 = Real("isqrt2")
        self.solver.add(1/(isqrt2 ** 2) == 2, isqrt2 > 0)
        
        if verbose: print("Generating SilSpeq proof obligations...")
        self.generate_speq_obligations(spq_name, func)
        
        if verbose: print("Generating Program from AST...")
        prog = self.generate_json_program(file, func)

        if verbose: 
            print("Generating proof obligations from Program")
            print(prog)
        self.generate_program_obligations(prog)
        
        if verbose: print(self.solver)
        
        return self.check_solver_sat()
    
    def getJSON(self, silq_json_file):
        """
        Reads the JSON silq file and stores the data in fdefs.
        """
        with open(silq_json_file, "r") as rf:
            data = rf.read()
            silq_json = json.loads(data)
        return silq_json
        
    def get_speq_obs(self, file):
        tree = self.speq_parser.parse_file(file)
        self.check_speq_sat(self, tree)
        return self.speq_z3_itp.visit(tree)
    
    def check_speq_sat(self, tree):
        speq_solver = Solver()
        speq_itp = SilSpeqZ3Interpreter(False)
        speq_solver.add(speq_itp.visit(tree))
        sat = speq_solver.check()
        if not(sat == z3.sat):
            raise Exception("SilSpeqError: one of your SilSpeq files is unsatisfiable. Check there are no contradictions in your specificaiton.")
        
    def add_func_speq_to_solver(self, speq_obs, func):
        self.solver.add(speq_obs[func])
        
    def generate_speq_obligations(self, speq_file, func):
        speq_obs = self.get_speq_obs(speq_file)
        self.add_func_speq_to_solver(speq_obs, func)
        
    def get_speq_file_name(self, silq_json_file):
        return splitext(silq_json_file)[0] + ".spq"    
    
    def generate_speq_file(self, silq_json_file):
        speq_gen = SpeqGenerator(self.getJSON(silq_json_file),
                                 self.get_speq_file_name(silq_json_file))
        speq_gen.generate_speq_file()
                
    def generate_json_program(self, silq_json_file, func):
        silq_json = self.getJSON(silq_json_file)
        prog = self.json_interp.decode_func_in_json(silq_json, func)
        return prog
    
    def generate_program_obligations(self, prog : Program):
        obs : list[BoolRef]
        obs = []
        ob_gen = ObilgationGenerator(self.config)
        for time in range(prog.current_time):
            if prog.quantum_processes[time].instruction != Instruction():
                prev_memory = self.get_prev_quantum_memory(prog, time)
                process_obligation = ob_gen.make_quantum_process_obligation(prog.quantum_processes[time], prev_memory, prog.controls[time])
                obs += process_obligation
            if prog.classical_processes[time].instruction != Instruction():
                # TODO: Handle classical obligation
                prev_memory = self.get_prev_classical_memory(prog, time)
                classical_obligation = ob_gen.make_classical_process_obligation(prog.classical_processes[time], prev_memory, prog.controls[time])
                obs += classical_obligation
            pass
        self.solver.add(obs)
    
    def get_prev_quantum_memory(self, prog : Program, time):
        if time != 0:
            return prog.quantum_processes[time - 1].end_memory
        return QuantumMemory()
    
    def get_prev_classical_memory(self, prog : Program, time):
        if time != 0:
            return prog.classical_processes[time - 1].end_memory
        return ClassicalMemory()