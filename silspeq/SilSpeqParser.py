from lark import Lark
from os import getcwd

class SilSpeqParser:
    def __init__(self, transformer=None):
        try:
            with open("SilSpeq.lark", 'r') as f:
                self.__grammar = f.read()
        except:
            try:
                with open(getcwd() + "/silspeq/SilSpeq.lark", 'r') as f:
                    self.__grammar = f.read()
            except:
                raise Exception("Cannot find SilSpeq.lark file")
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