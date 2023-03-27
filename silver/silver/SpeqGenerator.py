import re
from silver.silver.utils import generate_silspeq_from_func

PROD = "prod"

class SpeqGenerator():
    def __init__(self, silq_json, speq_file):
        self.silq_json = silq_json
        self.speq_file = speq_file
        
    # TODO: Convert argument types from Silq to JSON format
    # TODO: Correctly interpret types to speq version
    # TODO: Make a test library for this    
    def generate_speq_file(self):
        silspeq = ""
        for func_json in self.silq_json:
            fname = func_json['func']
            args = ["define " + arg["name"] + ":" + self.convert_type(arg["type"])
                    for arg in func_json['args']]
            ret = "define " + fname + "_ret:" + self.convert_type(func_json["retType"])
            silspeq += generate_silspeq_from_func(fname, args, ret) + "\n\n"
        silspeq = silspeq[:-2]
        with open(self.speq_file, "w") as wf:
            wf.write(silspeq)
            
    def convert_type(self, jsonType: dict):
        print(jsonType)
        t = jsonType["typeObj"]
        if (re.match(r"𝟙", t)): return "()"
        if (re.match(r"[B|𝔹]", t)): return "{0, 1}"
        if (re.match(r"[N|ℕ]", t)): return "N"
        if (re.match(r"[uint]", t)):
            try:
                size = jsonType["size"]["value"]
            except:
                size = jsonType["size"]
            return "{0, 1}^" + str(size)
        if (re.match(r"[prod]", t)):
            l = self.convert_type(jsonType['lhs'])
            r = self.convert_type(jsonType['rhs'])
            return l + "->" + r
        raise Exception("TypeTODO: " + str(type))