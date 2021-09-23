# Goal: Take in JSON and convert to a Python format

import json

class JSONInterpreter:
    def __init__(self, file):
        self.file = file

    def getJSON(self):
        with open(self.file, "r") as rf:
            self.data = json.load(rf)
            
    def print_data(self):
        print(self.data)