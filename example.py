from SilSpeqZ3Interpreter import SilSpeqZ3Interpreter
from SilSpeqZ3FlagInterpreter import SilSpeqZ3FlagInterpreter
import SilSpeqParser as ssp
from z3 import *

symbols = ("examples/symbols.spq", 'test')

def flag_example(arg=symbols):
    parser = ssp.SilSpeqParser()
    tree = parser.parse_file(arg[0])
    itp = SilSpeqZ3FlagInterpreter()
    itp.visit(tree)
    print(itp.oracles, itp.quantum_out)


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
        s.check()

if __name__ == "__main__":
    flag_example()
    example(True, symbols)