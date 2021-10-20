from SilSpeqInterpreter import SilSpeqInterpreter
import SilqSpeqParser as ssp
from z3 import Solver

def example(run_inter):
    parser = ssp.SilSpeqParser()
    tree = parser.parse_file("ex.spq")
    print(tree.pretty())
    if run_inter:
        s = Solver()
        itp = SilSpeqInterpreter()
        print(itp.visit(tree))
        tree = parser.parse_file("ex2.spq")
        print(itp.visit(tree))
        print(s)
        print(s.check())

if __name__ == "__main__":
    example(True)