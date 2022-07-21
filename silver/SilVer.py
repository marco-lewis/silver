from genericpath import exists
import inspect
import json as json
from os.path import splitext
import re
import subprocess

from z3.z3 import *

import silver
from silspeq.SilSpeqParser import SilSpeqParser
from silspeq.SilSpeqZ3FlagVisitor import SilSpeqZ3FlagVisitor
from silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from silver.ClassicalMemory import ClassicalMemory
from silver.Instruction import Instruction
from silver.JSONInterpreter import JSONInterpreter
from silver.MeasureOptions import MEASURE_OPTION, CERTAINTY, HIGH_PROB, SPECIFIC_VALUE
from silver.ObligationGenerator import ObilgationGenerator
from silver.Program import Program
from silver.QuantumMemory import QuantumMemory
from silver.SpeqGenerator import SpeqGenerator

class SilVer:
    __silver_tactic = Then(
        Repeat('propagate-ineqs'),
        Repeat('propagate-values'),
        'elim-and',
        'elim-uncnstr',
        'solve-eqs',
        'eq2bv',
        'bit-blast',
        'smt',
        "collect-statistics"
        )

    def __init__(self, timeout=30000, seed=3):
        self.timeout = timeout
        self.seed = seed
        self.solver = self.make_solver_instance()
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
    
    def make_solver_instance(self):
        s = self.__silver_tactic.solver()
        s.set(
            timeout=self.timeout,
            random_seed=self.seed,
        )
        return s

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
        elif self.speq_flag_itp.meas_whp: self.config[MEASURE_OPTION] = HIGH_PROB
        elif self.speq_flag_itp.meas_atval: self.config[MEASURE_OPTION] = SPECIFIC_VALUE
        else: self.config[MEASURE_OPTION] = HIGH_PROB
        self.speq_z3_itp.set_meas_cert(self.speq_flag_itp.meas_cert)
        
        if self.speq_flag_itp.quantum_out: pass
    
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

    def verify_func(self, silq_file_path, func, verbose=False, show_objects=False):
        json_file_path = self.generate_ast_file(silq_file_path)
        obs = self.make_obs(json_file_path, func, verbose, show_objects)
        self.solver.add(obs)
        if verbose:
            print("Full Obligations in Solver")
            if show_objects: print(self.solver)
            print()

        print("Verifying program with specification...")
        sat = self.check_solver_sat()
        return sat

    def get_ast_folder(self, silq_file_path):
        folder_path = splitext(silq_file_path)[0].split("/")[0]
        ast_path = folder_path + "/.ast"
        if not(exists(ast_path)):
            os.makedirs(ast_path)
        return ast_path

    def create_json_file(self, silq_file_path):
        rc = subprocess.check_call(["silq", "--ast-dump", silq_file_path])
        json_file_path = splitext(silq_file_path)[0] + ".json"
        return json_file_path

    def generate_ast_file(self, silq_file_path):
        ast_path = self.get_ast_folder(silq_file_path)
        json_file_path = self.create_json_file(silq_file_path)
        json_file_name = splitext(json_file_path)[0].split("/")[-1] + ".json"
        json_file_path_dest = ast_path + "/" + json_file_name
        os.rename(json_file_path, json_file_path_dest)
        return json_file_path_dest

    def make_obs(self, file, func, verbose=False, show_objects=False):
        print("Verifying " + func + " in " + file)
        self.check_speq_exists(file)
        spq_name = self.get_speq_file_name(file)
        self.check_flags(spq_name)
        
        if verbose: print("Generating SilSpeq proof obligations...")
        speq_obs = self.get_speq_obs(spq_name)
        
        if verbose:
            print("SilSpeq proof obligations generated and satisfiable")
            print()
            print("Generating Program from AST...") 
        prog = self.generate_json_program(file, func)
        prog.optimise()

        if verbose:
            print("Generating proof obligations from Program...")
            if show_objects: print(prog)
            print()
        prog_obs = self.generate_program_obligations(prog)
        
        if verbose:
            print("Program obligations generated")
            print()

        prog_sat, stats, reason = self.check_generated_obs_sat(prog_obs)
        if prog_sat != z3.sat:
            if verbose: print(stats)
            if prog_sat == z3.unknown: 
                print("Warning: program obligations unkown; could be unsat")
                print("Reason: ", reason)
            else: raise Exception("SatError(" + str(prog_sat) + "): generated obligations from Silq program are invalid.")

        if verbose:
            print("Program obligations satisfiable")
            print()
        return prog_obs + speq_obs[func]

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
        self.check_speq_sat(tree)
        return self.speq_z3_itp.visit(tree)
    
    def check_speq_sat(self, tree):
        """
        Given a SilSpeq tree, check that all generated Z3 expressions are satisfiable
        """
        speq_solver = self.make_solver_instance()
        speq_itp = SilSpeqZ3Interpreter(False)
        obl_dict = speq_itp.visit(tree)
        for func_name in obl_dict:
            func_obls = obl_dict[func_name]
            speq_solver.add(func_obls)
            sat = speq_solver.check()
            if sat == z3.unknown:
                print("Warning: SilSpeq obligations unkown; could be unsat")
                print("Reason: ", speq_solver.reason_unknown())
            elif sat == z3.unsat:
                raise Exception(
                    "SilSpeqError(" + str(sat) +
                    "): one of your SilSpeq function specifications is not sat. " +
                    "Check there are no contradictions in your specificaiton."
                )
            speq_solver.reset()
        
    def get_speq_file_name(self, silq_json_file):
        spq_path = splitext(silq_json_file)[0].split("/")
        del spq_path[-2]
        spq_path = '/'.join(spq_path)
        return spq_path + ".spq"
    
    def generate_speq_file(self, silq_json_file):
        speq_gen = SpeqGenerator(self.getJSON(silq_json_file),
                                 self.get_speq_file_name(silq_json_file))
        speq_gen.generate_speq_file()
                
    def generate_json_program(self, silq_json_file, func):
        silq_json = self.getJSON(silq_json_file)
        prog = self.json_interp.decode_func_in_json(silq_json, func)
        return prog
    
    def generate_program_obligations(self, prog : Program):
        obs : list[BoolRef] = []
        ob_gen = ObilgationGenerator(self.config)
        for time in range(prog.current_time):
            if prog.quantum_processes[time].instruction != Instruction():
                prev_memory = self.get_prev_quantum_memory(prog, time)
                if time == 0: obs += ob_gen.make_quantum_memory_initial_obligations(prev_memory)
                process_obligation = ob_gen.make_quantum_process_obligation(prog.quantum_processes[time], prev_memory, prog.controls[time])
                obs += process_obligation
            if prog.classical_processes[time].instruction != Instruction():
                # TODO: Handle classical obligation
                prev_memory = self.get_prev_classical_memory(prog, time)
                classical_obligation = ob_gen.make_classical_process_obligation(prog.classical_processes[time], prev_memory, prog.controls[time])
                obs += classical_obligation
        return obs
        
    def check_generated_obs_sat(self, obs : list[BoolRef]):
        s = self.make_solver_instance()
        s.add(obs)
        sat = s.check()
        stats = s.statistics()
        return sat, stats, s.reason_unknown()
    
    def get_prev_quantum_memory(self, prog : Program, time):
        return prog.quantum_processes[time - 1].end_memory
    
    def get_prev_classical_memory(self, prog : Program, time):
        return prog.classical_processes[time - 1].end_memory