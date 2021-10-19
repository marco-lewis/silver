from lark import Lark
from lark.visitors import Transformer
from SilSpeqTransformer import SilqSpeqTransformer

class SilSpeqParser:
    def __init__(self):
        with open("SilSpeq.lark", 'r') as f:
            self.grammar = f.read()
        self.parser = Lark(
            self.grammar, 
            parser='lalr', 
            transformer=SilqSpeqTransformer())

    def parse(self, spec):
        return self.parser.parse(spec)

    def parse_file(self, file_name):
        with open(file_name, 'r') as file:
            spec = file.read()
        return self.parse(spec)