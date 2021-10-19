from lark import Lark
import SilqSpeqParser as ssp

def example():
    parser = ssp.SilSpeqParser()
    tree = parser.parse_file("ex.spq")
    print(tree)


if __name__ == "__main__":
    example()