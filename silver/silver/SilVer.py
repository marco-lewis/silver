from genericpath import exists
import hashlib
import json as json
import logging
from os.path import splitext
import subprocess

from z3.z3 import *

from silver.silspeq.SilSpeqParser import SilSpeqParser
from silver.silspeq.SilSpeqFlagInterpreter import SilSpeqFlagInterpreter
from silver.silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from silver.silver.Instruction import Instruction
from silver.silver.JSONInterpreter import JSONInterpreter
from silver.MeasureOptions import *
from silver.silver.ObligationGenerator import ObilgationGenerator
from silver.silver.Program import Program
from silver.silver.SpeqGenerator import SpeqGenerator
from .utils import get_path, log_error

PROG_OBS = "prog_obs"
SPEQ_OBS = "speq_obs"

logger = logging.getLogger('silver')
def error(error_msg, *args): log_error(error_msg, logger) if len(args) == 0 else log_error(error_msg, logger, *args)

class SilVer:
    def __init__(self, timeout=30000, seed=3, check_store=True):
        self.timeout = timeout
        self.seed = seed
        self.check_store = check_store
        self.make_silver_tactic()
        self.solver = self.make_solver_instance(self.timeout)
        self.json_interp = JSONInterpreter()
        self.speq_parser = SilSpeqParser()
        self.config = {}
        self.assumptions = {}

    def make_silver_tactic(self, timeout=0):
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
                TryFor('smt', timeout),
                TryFor('nlsat', timeout),
                Then('nlsat', 'smt'),
                )
            )
        
    def make_solver_instance(self, timeout=0):
        s = self.__silver_tactic.solver()
        s.set(
            timeout=timeout,
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
    
    def check_solver_sat(self): return self.solver.check(*self.assumptions)
        
    def print_solver_sat(self, solver_sat):
        logger.info("Checking satisfiability...")
        if solver_sat == sat:
            m = self.solver.model()
            logger.info("Counterexample found")
            logger.debug("Model: %s", m)
        elif solver_sat == unsat:
            logger.info("Program is correct!")
        else:
            logger.info("Unable to determine if satisfiable")
            logger.debug("Satisfiability: %s", sat)
            
    def check_flags(self, file, func):
        speq_flag_itp = SilSpeqFlagInterpreter(func)
        tree = self.speq_parser.parse_file(file)
        flags = speq_flag_itp.visit(tree)
        self.config[MEASURE_OPTION] = []

        for flag, other in flags:
            if isinstance(flag, MeasureOptions): self.config[MEASURE_OPTION].append(flag)
            if flag == HIGH_PROB:
                low = other
                if low >= 0 and low <= 1: self.config[MEASURE_BOUND] = low
                else: error("Bound given for highprob flag is not between 0 and 1")
            if flag == SPECIFIC_VALUE:
                self.config[MEASURE_MARK] = other
        if self.config[MEASURE_OPTION] == []: self.config[MEASURE_OPTION].append(RAND)

        if speq_flag_itp.quantum_out: pass
    
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

    def verify_func(self, silq_file_path, func, log_level=logging.WARNING, spq_file=None):
        logger.level = log_level
        self.check_inputs(silq_file_path,func,spq_file)

        logger.info("Verifying %s in %s", func, silq_file_path)
        json_file_path = self.generate_ast_file(silq_file_path)
        obl_dict = self.make_obs(json_file_path, func, spq_file=spq_file)
        obs = obl_dict[PROG_OBS] + obl_dict[SPEQ_OBS]
        for i in range(len(obs)): self.solver.assert_and_track(obs[i], func + '_tracker' + str(i))
        logger.info("Full Obligations in Solver")
        logger.debug("Solver:\n%s", self.solver)
        logger.info("Verifying program with specification...")
        sat = self.check_solver_sat()
        logger.debug("Solver satisfiability: %s", sat)
        logger.info("Checking returned solver status...")
        self.check_sat_instance(sat, obl_dict)
        return sat

    def check_inputs(self, silq_file_path,func,spq_file):
        try: exists(silq_file_path)
        except: error("Silq file path provided is invalid. The path %s does not exist.", silq_file_path)
        if not(isinstance(func,str)): error("%s is not a string.", func)
        try:
            if not(spq_file == None): exists(spq_file)
        except: 
            logger.warn("Provided path for SilSpeq file is invalid. Will continue without using path provided but this may affect later computation.")
            spq_file = None

    def get_ast_folder(self, silq_file_path):
        ast_path = get_path(silq_file_path) + "/.ast"
        if not(exists(ast_path)): os.makedirs(ast_path)
        return ast_path

    def check_sat_instance(self, sat, obl_dict):
        if sat == z3.sat:
            logger.info("Performing check on satisfiable model...")
            logger.debug("Fetching model...")
            m = self.solver.model()
            solver = self.make_solver_instance()
            logger.debug("Adding obligations to new solver...")
            solver.add(obl_dict[PROG_OBS] + obl_dict[SPEQ_OBS])
            model_obs = []
            logger.debug("Assigning variables to model values...")
            for var in m:
                try:
                    if isinstance(m[var], FuncInterp): self.add_func_interp(model_obs, m, var)
                    else: model_obs.append(var() == m[var()])
                except:
                    logger.warn("%s was not added as an obligation.", var)
                    logger.warn("This may cause problems when checking.")
            solver.add(model_obs)
            logger.debug("Model Obligation:\n%s", "\n".join([str(obl) for obl in model_obs]))
            logger.debug("Checking...")
            sat_check = solver.check()
            if sat_check == z3.unsat: error("Erroneous model found. This means the solver returned a model that is unsatisfiable.")
            elif sat_check == z3.unknown: error("Satisfiability check is unknown. Model cannot be verified.")
            else: logger.info("Satisfiability check passed.")
        elif sat == z3.unknown: logger.warn("Solver returned unknown.")
        elif sat == z3.unsat:
            logger.info("Performing check on unsat instance...")
            unsat_core = self.solver.unsat_core()
            num_of_assertions = len(self.solver.assertions())
            unsat_core_size = len(unsat_core)
            speq_size = len(obl_dict[SPEQ_OBS])
            logger.debug("# of program/specification obligations: %s/%s", len(obl_dict[PROG_OBS]), speq_size)
            logger.debug("# of trackers in unsat core/solver: %s/%s", unsat_core_size, num_of_assertions)
            tracker_num_start_idx = str(unsat_core[0]).rfind("r") + 1
            sorted_core = sorted([int(str(tracker)[tracker_num_start_idx:]) for tracker in unsat_core])
            logger.debug("Tracker (numbers) in unsatcore: %s", sorted_core)
            last_tracker = sorted_core[-1]
            post_in_unsat_core = last_tracker == num_of_assertions - 1
            if post_in_unsat_core: logger.debug("Post-condition is in unsat core.")
            else: error("Post-condition is not in the unsat core.")
            logger.info("Unsatisfiability check passed.")

    def add_func_interp(self, model_obs : list, model : ModelRef, var):
        fixed_inputs = []
        for inout_pair in model[var].as_list():
            if isinstance(inout_pair, list):
                model_obs.append(var(inout_pair[0]) == inout_pair[1])
                fixed_inputs.append(inout_pair[0])
        f_in = Int(str(var) +'_in')
        model_obs.append(var(f_in) == model[var].else_value())
        if not(fixed_inputs == []): model_obs.append(And([Not(f_in == i) for i in fixed_inputs]))

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

    def make_obs(self, json_file_path, func, spq_file=None):
        self.check_speq_exists(json_file_path, spq_file=spq_file)
        spq_path = self.get_speq_file_name(json_file_path,spq_file=spq_file)
        self.check_flags(spq_path, func)
        
        logger.info("Generating SilSpeq proof obligations...")
        speq_obs = self.get_speq_obs(spq_path)
        for key in speq_obs: speq_obs[key] = self.clean_obligation_list(speq_obs[key])
        logger.info("SilSpeq proof obligations generated")
        logger.debug("SpeqObligations:\n%s", speq_obs)

        # TODO: Move/modify so SilVer more modular; feed in functions/options?
        silq_json = self.getJSON(json_file_path)
        hash = hashlib.md5(str(silq_json).encode('utf-8') + str(self.config).encode('utf-8')).hexdigest()
        hash_path = self.get_hash_path(json_file_path, func)
        stored_hash = self.get_stored_hash(hash_path)

        if hash == stored_hash and self.check_store:
            logger.info("Obtaining stored obligations...")
            prog_obs = [obl for obl in z3.parse_smt2_file(self.get_obligation_path(json_file_path, func))]
            logger.debug(prog_obs)
        else:
            logger.info("Generating Program from AST...") 
            prog = self.json_interp.decode_func_in_json(silq_json, func)
            prog.optimise()

            logger.info("Generating proof obligations from Program...")
            logger.debug("Program:\n%s", prog)
            prog_obs = self.generate_program_obligations(prog)
            prog_obs = self.clean_obligation_list(prog_obs)
            logger.info("Program obligations generated")

            logger.info("Checking program obligations satisfiable...")
            prog_sat, stats, reason = self.check_generated_obs_sat(prog_obs)
            if prog_sat != z3.sat:
                if prog_sat == z3.unknown:
                    logger.warning("Program obligations unkown; could be unsat.")
                    logger.warning("Reason: %s", reason)
                else:
                    logger.debug("Program obligations:\n%s", prog_obs)
                    error("Generated obligations from Silq program are invalid. Expected sat but got %s.", prog_sat)
            else: logger.info("Program obligations satisfiable")

            logger.info("Storing obligations...")
            with open(hash_path, 'w') as writer: writer.write(str(hash))
            temp_solver = self.__silver_tactic.solver()
            temp_solver.add(prog_obs)
            prog_smt2 = temp_solver.to_smt2()
            with open(self.get_obligation_path(json_file_path, func), 'w') as writer: writer.write(str(prog_smt2))
            logger.info("Obligations stored")
        return {PROG_OBS: prog_obs, SPEQ_OBS: speq_obs[func]}

    def clean_obligation_list(self, obs): return list(filter(lambda x: not(isinstance(x, bool) and x), obs))

    def getJSON(self, silq_json_file):
        """
        Reads the JSON silq file and stores the data in fdefs.
        """
        with open(silq_json_file, "r") as rf: silq_json = json.loads(rf.read())
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
        if not(exists(hash_file_path)): return ""
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

    def get_speq_obs(self, file):
        tree = self.speq_parser.parse_file(file)
        self.check_speq_sat(tree)
        speq_z3_itp = SilSpeqZ3Interpreter()
        return speq_z3_itp.visit(tree)
    
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
                logger.warning("SilSpeq obligations unkown; could be unsat")
                logger.warning("Reason: %s", speq_solver.reason_unknown())
            elif sat == z3.unsat: error("One of your SilSpeq function specifications is %s when it should be sat. Check there are no contradictions in your specificaiton.", sat)
            speq_solver.reset()
        
    def check_speq_exists(self, file, spq_file=None):
        if not(spq_file == None) and not(exists(spq_file)):
            self.generate_speq_file(spq_file)
            error("New SilSpeq file created, you should add your specification before continuing.")
        if not(exists(self.get_speq_file_name(file))):
            self.generate_speq_file(file)
            error("New SilSpeq file created, you should add your specification before continuing.")

    def get_speq_file_name(self, silq_json_file, spq_file=None):
        if spq_file != None: return spq_file
        spq_path = splitext(silq_json_file)[0].split("/")
        del spq_path[-2]
        spq_path = '/'.join(spq_path)
        return spq_path + ".spq"
    
    def generate_speq_file(self, silq_json_file):
        speq_gen = SpeqGenerator(self.getJSON(silq_json_file),
                                 self.get_speq_file_name(silq_json_file))
        speq_gen.generate_speq_file()
    
    def generate_program_obligations(self, prog : Program):
        ob_gen = ObilgationGenerator(prog, self.config)
        obs = ob_gen.make_obligations()
        return obs
        
    def check_generated_obs_sat(self, obs : list[BoolRef]):
        s = self.make_solver_instance()
        s.add(obs)
        sat = s.check()
        stats = s.statistics()
        return sat, stats, s.reason_unknown()