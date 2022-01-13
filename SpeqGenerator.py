import re
from utils import generate_silspeq_from_func

class SpeqGenerator():
    def __init__(self, silq_json, speq_file):
        self.silq_json = silq_json
        self.speq_file = speq_file
    
    def generate_speq_file(self):
        silspeq = ""
        for func_json in self.silq_json:
            fname = func_json['func']
            args = ["define " + arg["name"] + ":" + self.convert_type_to_speq_type(arg["type"])
                    for arg in func_json['args']]
            ret = "define " + fname + "_ret:{0,1}"
            silspeq += generate_silspeq_from_func(fname, args, ret) + "\n\n"
        silspeq = silspeq[:-2]
        with open(self.speq_file, "w") as wf:
            wf.write(silspeq)

    # TODO: Correctly interpret types to speq version
    # TODO: Make a test library for this
    def convert_type_to_speq_type(self, type):
        if (re.match("[N|ℕ]", type)):
            return "N"
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