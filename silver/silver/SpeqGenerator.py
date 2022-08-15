import re
from silver.utils import generate_silspeq_from_func

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
            args = ["define " + arg["name"] + ":" + self.convert_type_to_speq_type(arg["type"])
                    for arg in func_json['args']]
            ret = "define " + fname + "_ret:" + self.convert_retType(func_json["retType"])
            silspeq += generate_silspeq_from_func(fname, args, ret) + "\n\n"
        silspeq = silspeq[:-2]
        with open(self.speq_file, "w") as wf:
            wf.write(silspeq)
            
    def convert_retType(self, retType: dict):
        type = retType["typeObj"]
        speq_type = self.convert_type_to_speq_type(type)
        if type == "uint":
            try:
                size = retType["size"]["value"]
            except:
                size = retType["size"]
            speq_type += "^" + str(size)
        if speq_type == "prod":
            l = self.convert_retType(retType['lhs'])
            r = self.convert_retType(retType['rhs'])
            speq_type = l + "->" + r
        return speq_type
        
    def convert_type_to_speq_type(self, type : str):
        if (re.match(r"𝟙", type)):
            return "()"
        if (re.match(r"[N|ℕ]", type)):
            return "N"
        if (re.match(r"[B|𝔹]", type)):
            return "{0, 1}"
        if (re.match(r"uint", type)):
            if (re.match(r"uint\[[0-9]+\]", type)):
                return "{0, 1}^" + type.split("[")[1].split("]")[0]
            return "{0, 1}"
        if (re.match(r".*(→.*)+",type)):
            types = [self.convert_type_to_speq_type(arg_type) + "->"
                     for arg_type in re.split(r"→", type)]
            out = "".join(types)[:-2]
            return out
        if (re.match(r"[¬, const, qfree].*", type)):
            split = re.split(r"[¬, const, qfree]", type, maxsplit=1)[1]
            return self.convert_type_to_speq_type(split)
        if (re.match(r'prod', type)):
            return PROD
        raise Exception("TypeTODO: " + type)