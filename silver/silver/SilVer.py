from genericpath import exists
import hashlib
import json as json
import logging
from os.path import splitext
import subprocess

from z3.z3 import *

from silver.silspeq.SilSpeqParser import SilSpeqParser
from silver.silspeq.SilSpeqZ3FlagVisitor import SilSpeqZ3FlagVisitor
from silver.silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from silver.silver.Instruction import Instruction
from silver.silver.JSONInterpreter import JSONInterpreter
from silver.MeasureOptions import *
from silver.silver.ObligationGenerator import ObilgationGenerator
from silver.silver.Program import Program
from silver.silver.SpeqGenerator import SpeqGenerator
from .utils import get_path

class SilVer:
    def __init__(self, timeout=30000, seed=3, check_store=True):
        self.timeout = timeout
        self.seed = seed
        self.check_store = check_store
        self.make_silver_tactic()
        self.solver = self.make_solver_instance()
        self.json_interp = JSONInterpreter()
        self.speq_parser = SilSpeqParser()
        # TODO: Move so that Interpreters are only function specific
        self.speq_z3_itp = SilSpeqZ3Interpreter()
        self.speq_flag_itp = SilSpeqZ3FlagVisitor()
        self.config = {}
        self.assumptions = {}

    def make_silver_tactic(self):
        self.__silver_tactic = Then(
            'propagate-values',
            'elim-and',
            'elim-term-ite',
            'elim-uncnstr',
            'simplify',
            'solve-eqs',
            'eq2bv',
            'dt2bv',
            'bit-blast',
            'tseitin-cnf',
            OrElse(
                TryFor('smt', self.timeout),
                TryFor('nlsat', self.timeout),
                Then('nlsat', 'smt'),
                )
            )

    def check_speq_exists(self, file):
        if not(exists(self.get_speq_file_name(file))):
            self.generate_speq_file(file)
            raise Exception("New SilSpeq file created, you should add your specification before continuing")
    
    def make_solver_instance(self):
        s = self.__silver_tactic.solver()
        s.set(
            timeout=self.timeout,
            random_seed=self.seed,
            seed=self.seed,
            unsat_core=True,
        )
        # s.set("parallel.enable", True)
        # s.set("threads", 4)
        # s.set("arith.solver", 6)
        # s.set("arith.nl.rounds", 100)
        # s.set("arith.ignore_int", True)
        # s.set("eq2ineq", True)
        return s

    def reset(self):
        self.solver.reset()
        self.json_interp = JSONInterpreter()
        
    def check_solver_sat(self):
        return self.solver.check(*self.assumptions)
        
    def print_solver_sat(self, solver_sat):
        logging.info("Checking satisfiability...")
        if solver_sat == sat:
            m = self.solver.model()
            logging.info("Counterexample found")
            logging.debug("Model: %s", m)
        elif solver_sat == unsat:
            logging.info("Program is correct!")
        else:
            logging.info("Unable to determine if satisfiable")
            logging.debug("Satisfiability: %s", sat)
            
    def check_flags(self, file):
        tree = self.speq_parser.parse_file(file)
        self.speq_flag_itp.visit(tree)

        self.config[MEASURE_OPTION] = self.speq_flag_itp.meas_options
        
        if HIGH_PROB in self.config[MEASURE_OPTION]: 
            low = self.speq_flag_itp.meas_low_bound
            if low >= 0 and  low <= 1: self.config[MEASURE_BOUND] = low
            else: raise Exception("FlagError(whp): bound given is not between 0 and 1")
        if SPECIFIC_VALUE in self.config[MEASURE_OPTION]: self.config[MEASURE_MARK] = self.speq_flag_itp.meas_mark
        if self.config[MEASURE_OPTION] == []: self.config[MEASURE_OPTION].append(RAND)
        self.speq_z3_itp.set_meas_cert(CERTAINTY in self.config[MEASURE_OPTION])

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

    def verify_func(self, silq_file_path, func, log_level=logging.WARNING):
        logging.basicConfig(level=log_level, force=True)
        print("###########################################################")
        print("Verifying " + func + " in " + silq_file_path)
        json_file_path = self.generate_ast_file(silq_file_path)
        obs = self.make_obs(json_file_path, func)
        for i in range(len(obs)):
            if obs[i] == True: continue 
            self.solver.assert_and_track(obs[i], func + '_tracker' + str(i))
        logging.info("Full Obligations in Solver")
        logging.debug("Solver: %s", self.solver)

        print("Verifying program with specification...")
        sat = self.check_solver_sat()
        self.sanity_check(sat)
        return sat

    def get_ast_folder(self, silq_file_path):
        folder_path = get_path(silq_file_path)
        ast_path = folder_path + "/.ast"
        if not(exists(ast_path)):
            os.makedirs(ast_path)
        return ast_path

    def sanity_check(self, sat):
        if sat == z3.sat:
            logging.info("Performing sanity check on satisfiable model...")
            m = self.solver.model()
            s = self.make_solver_instance()
            s.add(self.solver.assertions())
            # TODO: handle functions correctly in except
            for var in m: 
                try: s.add(var() == m[var()])
                except: pass
            sat_c = s.check()
            if sat_c == z3.unsat:
                logging.info("Erroneous model found\n %s", m)
                raise Exception("Generated model failed sanity check.")
            logging.info("Sanity check passed")
        if sat == z3.unsat:
            # TODO: Fetch unsat core and check that postconditions tracker is in there
            pass

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

    def make_obs(self, json_file_path, func):
        self.check_speq_exists(json_file_path)
        spq_name = self.get_speq_file_name(json_file_path)
        self.check_flags(spq_name)
        
        logging.info("Generating SilSpeq proof obligations...")
        speq_obs = self.get_speq_obs(spq_name)
        
        logging.info("SilSpeq proof obligations generated")
        logging.debug("SpeqObligations:%s", speq_obs)

        silq_json = self.getJSON(json_file_path)
        hash = hashlib.md5(str(silq_json).encode('utf-8') + str(self.config).encode('utf-8')).hexdigest()
        hash_path = self.get_hash_path(json_file_path, func)
        stored_hash = self.get_stored_hash(hash_path)

        if hash == stored_hash and self.check_store:
            logging.info("Obtaining stored obligations...")
            prog_obs = []
            self.load_stored_obligations(json_file_path, func)
        else:
            logging.info("Generating Program from AST...") 
            prog = self.json_interp.decode_func_in_json(silq_json, func)
            prog.optimise()

            logging.info("Generating proof obligations from Program...")
            logging.debug("Program:%s", prog)
            prog_obs = self.generate_program_obligations(prog)
            
            logging.info("Program obligations generated")
            logging.info("Checking program obligations satisfiable...")

            prog_sat, stats, reason = self.check_generated_obs_sat(prog_obs)
            if prog_sat != z3.sat:
                if prog_sat == z3.unknown:
                    logging.warning("Warning: program obligations unkown; could be unsat.")
                    logging.warning("Reason: %s", reason)
                else: raise Exception("SatError(" + str(prog_sat) + "): generated obligations from Silq program are invalid.")

            logging.info("Program obligations satisfiable")
            logging.info("Storing obligations...")
            
            with open(hash_path, 'w') as writer: writer.write(str(hash))
            temp_solver = self.__silver_tactic.solver()
            temp_solver.add(prog_obs)
            prog_smt2 = temp_solver.to_smt2()
            with open(self.get_obligation_path(json_file_path, func), 'w') as writer: writer.write(str(prog_smt2))
        return prog_obs + speq_obs[func]

    def getJSON(self, silq_json_file):
        """
        Reads the JSON silq file and stores the data in fdefs.
        """
        with open(silq_json_file, "r") as rf:
            data = rf.read()
            silq_json = json.loads(data)
        return silq_json

    def get_hash_path(self, json_file_path, func):
        path = splitext(json_file_path)[0].split("/")
        path[-1] = path[-1] + "_" + str(func)
        path[-2] = ".hash"
        folder = "/".join(path[:-1])
        if not(exists(folder)): os.mkdir(folder)
        path = "/".join(path) + ".hash"
        return path
    
    def get_stored_hash(self, hash_file_path):
        if not(exists(hash_file_path)):
            return ""
        with open(hash_file_path, 'rb') as r: hash = r.read()
        return hash.decode('utf-8')

    def get_obligation_path(self, json_file_path, func):
        path = splitext(json_file_path)[0].split("/")
        path[-1] = path[-1] + "_" + str(func)
        path[-2] = ".obl"
        folder = "/".join(path[:-1])
        if not(exists(folder)): os.mkdir(folder)
        path = "/".join(path) + ".smt2"
        return path

    def load_stored_obligations(self, json_file_path, func):
        obl_path = self.get_obligation_path(json_file_path, func)
        self.solver.from_file(obl_path)

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
        self.assumptions = speq_itp.assumptions
        for func_name in obl_dict:
            func_obls = obl_dict[func_name]
            speq_solver.add(func_obls)
            sat = speq_solver.check(*self.assumptions)
            if sat == z3.unknown:
                logging.warning("Warning: SilSpeq obligations unkown; could be unsat")
                logging.warning("Reason: %s", speq_solver.reason_unknown())
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