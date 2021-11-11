from JSONInterpreter import JSONInterpreter
import json as json
from os.path import splitext
from silspeq.SilSpeqParser import SilSpeqParser
from silspeq.SilSpeqZ3FlagInterpreter import SilSpeqZ3FlagInterpreter
from silspeq.SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from utils import generate_silspeq_from_func
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
        
    def generate_speq_file(self, silq_json_file):
        silq_json = self.getJSON(silq_json_file)
        silspeq = ""
        for func_json in silq_json:
            fname = func_json['func']
            args = [arg["name"] + ":" + self.convert_type_to_speq_type(arg["type"])
                    for arg in func_json['args']]
            ret = fname + "_ret:{0,1}"
            silspeq += generate_silspeq_from_func(fname, args, ret) + "\n\n"
        silspeq = silspeq[:-2]
        spq_file = splitext(silq_json_file)[0] + ".spq"
        with open(spq_file, "w") as wf:
            wf.write(silspeq)
        pass

    # TODO: Correctly interpret types to speq version
    def convert_type_to_speq_type(self, type):
        return type
        
    def verify_json(self, silq_json_file):
        silq_json = self.getJSON(silq_json_file)
        self.json_interp.decode_json(silq_json)