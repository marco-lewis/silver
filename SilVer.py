from JSONInterpreter import JSONInterpreter
import json as json
from os.path import splitext
import re
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
        
    def generate_speq_obligations(self, speq_file):
        speq_obs = self.get_speq_obs(speq_file)
        self.add_func_speq_to_solver(speq_obs, "deutsch")
        
    def generate_speq_file(self, silq_json_file):
        silq_json = self.getJSON(silq_json_file)
        silspeq = ""
        for func_json in silq_json:
            fname = func_json['func']
            args = ["define " + arg["name"] + ":" + self.convert_type_to_speq_type(arg["type"])
                    for arg in func_json['args']]
            ret = "define " + fname + "_ret:{0,1}"
            silspeq += generate_silspeq_from_func(fname, args, ret) + "\n\n"
        silspeq = silspeq[:-2]
        with open(self.get_speq_file_name(silq_json_file), "w") as wf:
            wf.write(silspeq)
        pass
    
    def get_speq_file_name(self, silq_json_file):
        return splitext(silq_json_file)[0] + ".spq"

    # TODO: Correctly interpret types to speq version
    # TODO: Make a test library for this
    def convert_type_to_speq_type(self, type):
        if (re.match("[B|𝔹]", type)):
            return "{0, 1}"
        if (re.match(r".*(→.*)+",type)):
            types = [self.convert_type_to_speq_type(arg_type) + "->"
                     for arg_type in re.split(r"→", type)]
            out = "".join(types)[:-2]
            return out
        if (re.match(r"[¬, const, qfree].*", type)):
            split = re.split(r"[¬, const, qfree]", type, maxsplit=1)[1]
            return self.convert_type_to_speq_type(split)
        raise Exception("TypeTODO: " + type)
        
    def generate_json_obligations(self, silq_json_file):
        silq_json = self.getJSON(silq_json_file)
        self.json_interp.decode_json(silq_json)