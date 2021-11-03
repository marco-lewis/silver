from SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
import SilqSpeqParser as ssp
from z3 import *

def example(run_inter):
    parser = ssp.SilSpeqParser()
    tree = parser.parse_file("ex3.spq")
    # print(tree.pretty())
    if run_inter:
        s = Solver()
        itp = SilSpeqZ3Interpreter()
        intp_tree = itp.visit(tree)
        obl = intp_tree['dj_alg']
        s.add(obl)
        print(s)

if __name__ == "__main__":
    example(True)