from SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
import SilqSpeqParser as ssp
from z3 import *

symbols = ("examples/symbols.spq", 'test')

def example(run_inter, args=("examples/ex3.spq", 'dj_alg')):
    parser = ssp.SilSpeqParser()
    tree = parser.parse_file(args[0])
    # print(tree.pretty())
    if run_inter:
        s = Solver()
        itp = SilSpeqZ3Interpreter()
        intp_tree = itp.visit(tree)
        obl = intp_tree[args[1]]
        print(obl)
        s.add(obl)

if __name__ == "__main__":
    example(True, symbols)