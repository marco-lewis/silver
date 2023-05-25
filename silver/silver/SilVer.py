from genericpath import exists
import hashlib
import json as json
import logging
from os.path import splitext
import subprocess
import time

import numpy as np
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
from .utils import *

logger = logging.getLogger('silver')
def error(error_msg, *args): log_error(error_msg, logger) if len(args) == 0 else log_error(error_msg, logger, *args)

class SilVer:
    def __init__(self, timeout=30000, seed=None, check_store=True):
        self.timeout = timeout
        self.seed = seed if isinstance(seed, int) else np.random.randint(0, 100000)
        self.check_store = check_store
        self.make_silver_tactic()
        self.solver = self.make_solver_instance(self.timeout)
        self.json_interp = JSONInterpreter()
        self.speq_parser = SilSpeqParser()
        self.config = {}
        self.assumptions = {}
        self.dreal_time = 0

    def make_silver_tactic(self, timeout=5000):
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
        
    def make_solver_instance(self, timeout=5000):
        s = self.__silver_tactic.solver()
        s.set(
            timeout=timeout,
            random_seed=self.seed,
            seed=self.seed,
            unsat_core=True,
        )
        return s
    
    def get_times(self, mode=Z3):
        try: solve_time = self.solver.statistics().get_key_value('time')
        except: solve_time = 0 if mode == Z3 else self.dreal_time
        return {"setup": self.setup_time, "solve": solve_time}
        
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

    def verify_func(self, silq_file_path, func, log_level=logging.WARNING, spq_file=None, mode=Z3, delta = 0.0001):
        logger.level = log_level
        self.json_interp.set_log_level(log_level)
        self.solver.reset()
        self.dreal_time = 0
        self.check_inputs(silq_file_path,func,spq_file)

        logger.info("Verifying %s in %s", func, silq_file_path)
        json_file_path = self.generate_ast_file(silq_file_path)
        obl_dict = self.make_obs(json_file_path, func, spq_file=spq_file)
        obs = obl_dict[PROG_OBS] + obl_dict[SPEQ_OBS]
        for i in range(len(obs)): self.solver.assert_and_track(obs[i], func + '_tracker' + str(i))
        logger.info("Full Obligations in Solver")
        logger.debug("Solver:\n%s", self.solver)
        logger.info("Verifying program with specification...")
        sat, model = self.check_solver_sat(mode, silq_file_path=silq_file_path, delta=delta)
        logger.debug("Solver satisfiability: %s", sat)
        logger.info("Checking returned solver status...")
        self.check_sat_instance(sat, model, obl_dict, mode)
        return sat, model

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
    
    def check_sat_instance(self, sat, model, obl_dict, mode=Z3):
        if mode == Z3:
            self.check_z3sat_instance(sat, model, obl_dict)
            return 0
        elif mode == DREAL:
            return 0
        error("Mode %s is not supported", mode)

    def check_z3sat_instance(self, sat, model, obl_dict):
        if sat == z3.sat:
            logger.info("Performing check on satisfiable model...")
            logger.debug("Fetching model...")
            m = model
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
    
    def check_drealsat_instance(self, sat, model, obl_dict):
        logger.warn("Not checking dreal instances")

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
        self.setup_time = 0
        start = time.time()
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

            logger.info("Storing program obligations...")
            with open(hash_path, 'w') as writer: writer.write(str(hash))
            temp_solver = self.__silver_tactic.solver()
            temp_solver.add(prog_obs)
            prog_smt2 = temp_solver.to_smt2()
            with open(self.get_obligation_path(json_file_path, func), 'w') as writer: writer.write(str(prog_smt2))
            logger.info("Program obligations stored")

        self.setup_time = time.time() - start
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
    
    def check_solver_sat(self, mode="z3", silq_file_path="", delta=0.0001):
        if mode==Z3:
            sat = self.solver.check(*self.assumptions)
            model = [] if not sat == z3.sat else self.solver.model()
            return sat, model
        if mode==DREAL:
            logging.info("Converting smt2 to dreal...")
            smt2 = self.solver.to_smt2()
            smt2 = self.z3_to_dreal(smt2)
            logging.info("Converted.")
            smt2_path = self.generate_smt2_path(silq_file_path)
            with open(smt2_path, "w") as smt2file:
                smt2file.write(smt2)
            command = [DREAL_PATH, '--precision', str(delta), smt2_path]
            logging.info("Running...")
            start = time.time()
            # Timeout is in seconds for subprocess
            result = subprocess.run(command, stdout=subprocess.PIPE, timeout=self.timeout/1000)
            self.dreal_time = time.time() - start
            logging.info("dReal ran successfully.")
            output = result.stdout.decode('utf-8')
            logger.debug("dReal output:\n" + output)
            sat = output[:output.index("\n")]
            model = output[output.index("\n") + 1:-1]
            os.remove(smt2_path)
            return sat, model
        error("Mode %s is not supported", mode)

    def z3_to_dreal(self, smt2: str):
        roots = 0
        trackers = 0
        smt2 = smt2[:smt2.index("(")] + ";" + smt2[smt2.index("("):]
        smt2 = smt2[:smt2.index("(check-sat)")] 
        while True:
            tracker_tok = "_tracker" + str(trackers)
            # Replace root-objects with variables taking on value
            if "root-obj" in smt2:
                # Get expression
                start = smt2.index("root-obj") - 1
                end = start + 8
                i = 1
                while not i == 0:
                    if smt2[end] == "(": i += 1
                    elif smt2[end] == ")": i -= 1
                    end += 1
                old_root_expr = smt2[start:end+1]

                # Find root value
                s = Solver()
                s.from_string("(declare-fun a () Real)\n(assert (= "+old_root_expr+"a))\n(check-sat)\n")
                s.check()
                v = s.model()[Real("a")].approx(2).numerator_as_long()

                # Make a new root
                root = Real("root" + str(roots))
                new_root_expr = "(declare-fun " + str(root) + " () Real)\n" 
                new_root_expr += "(assert (= " + old_root_expr[10:-4].replace("x", str(root)) + " 0))\n"
                new_root_expr += "(assert ("
                if v > 0: new_root_expr += "< 0 " + str(root)
                else: new_root_expr += "> 0 " + str(root)
                new_root_expr += "))\n"

                # Replace it in the smt2 string
                smt2 = smt2.replace(old_root_expr, str(root) + " ")
                smt2 = new_root_expr + smt2
                roots += 1
            # Add trackers to the end; must be true
            elif  tracker_tok in smt2:
                tracker = smt2[:smt2.index(tracker_tok) + len(tracker_tok)]
                tracker = tracker[tracker.rfind(" ") + 1:]
                smt2 += "(assert (= " + tracker + " true))\n"
                trackers += 1
            # Remove to_real functions
            elif  "to_real" in smt2:
                start = smt2.index("to_real") - 1
                end = start + smt2[start:].find(")")
                expr = smt2[start:end+1]
                spaceidx = expr.find(" ")
                var = expr[spaceidx+1:-1]
                var = Int(var)
                smt2 = smt2.replace(expr, str(var))
            # Replace functions
            elif "(Int) Int" in smt2:
                idx = smt2.index("(Int) Int")
                start = smt2[:idx].rfind("(")
                end = idx + len("(Int) Int") + 1
                old_expr = smt2[start:end]
                var = old_expr[old_expr.index(" ")+1:]
                var = var[:var.index(" ")]
                # Replace all calls to function
                while True:
                    if "(" + var + " " in smt2:
                        idx = smt2.find("(" + var + " ")
                        var_call = smt2[idx:]
                        var_call = var_call[: var_call.find(")") + 1]
                        var_i = var_call[var_call.find(" ") + 1:-1]
                        new_var = var + "_" + var_i
                        decl_expr = "(declare-fun " + new_var + " () Int)\n"
                        smt2 = smt2.replace(var_call, new_var)
                        smt2 = decl_expr + smt2
                    else:
                        break
                smt2 = smt2.replace(old_expr + "\n", "")
            else:
                break

        # smt2 = "(set-logc QF_NRA)\n" + smt2
        smt2 += '(check-sat)\n'
        smt2 += '(get-model)\n'
        smt2 += '(exit)\n'
        return smt2

    def generate_smt2_path(self, silq_file_path=""):
        return str("/tmp/" + silq_file_path[silq_file_path.rfind("/") + 1:][:-4] + ".smt2")