from lark import Lark
from SilSpeqInterpreter import SilSpeqInterpreter
from SilSpeqTransformer import SilqSpeqTransformer
import SilqSpeqParser as ssp

def example(run_inter):
    # parser = ssp.SilSpeqParser(SilqSpeqTransformer())
    parser = ssp.SilSpeqParser(None)
    tree = parser.parse_file("ex.spq")
    print(tree.pretty())
    itp = SilSpeqInterpreter()
    print(itp.visit(tree))
    tree = parser.parse_file("ex2.spq")
    print(itp.visit(tree))

if __name__ == "__main__":
    example(True)