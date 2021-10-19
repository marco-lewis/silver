from lark import Lark

with open("SilSpeq.lark", 'r') as f:
    grammar = f.read()

with open("ex.spq", 'r') as f:
    spec = f.read()

print("Read files")
parser = Lark(grammar, parser='lalr')
print("Parser made")
tree = parser.parse(spec)

print(tree)
