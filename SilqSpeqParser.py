from lark import Lark

class SilSpeqParser:
    def __init__(self, transformer=None):
        with open("SilSpeq.lark", 'r') as f:
            self.__grammar = f.read()
        self.parser = Lark(
            self.__grammar, 
            parser='lalr', 
            transformer=transformer)

    def parse(self, spec):
        return self.parser.parse(spec)

    def parse_file(self, file_name):
        with open(file_name, 'r') as file:
            spec = file.read()
        return self.parse(spec)