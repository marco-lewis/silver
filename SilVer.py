from JSONInterpreter import JSONInterpreter
import json as json
from silspeq.SilSpeqParser import SilSpeqParser
from silspeq.SilSpeqZ3FlagInterpreter import SilSpeqZ3FlagInterpreter
from silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from z3.z3 import Solver

class SilVer:
    def __init__(self):
        self.solver = Solver()
        self.json_interp = JSONInterpreter(self.solver)
        self.speq_parser = SilSpeqParser()
        self.speq_z3_itp = SilSpeqZ3Interpreter()
        self.speq_flag_itp = SilSpeqZ3FlagInterpreter()
        
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
        return self.speq_z3_itp.visit(tree)
        
    def add_func_speq_to_solver(self, speq_obs, func):
        self.solver.add(speq_obs[func])
        
    def verify_speq(self, speq_file):
        speq_obs = self.get_speq_obs(speq_file)
        self.add_func_speq_to_solver(speq_obs, "dj_alg")
        
    def verify_silq(self, silq_json_file):
        silq_json = self.getJSON(silq_json_file)
        self.json_interp.decode_json(silq_json)