# Goal: Take in JSON and convert to a Python format

import json

class JSONInterpreter:
    def __init__(self, file):
        self.file = file

    def getJSON(self):
        with open(self.file, "r") as rf:
            self.fdefs = rf.read()
            self.fdefs = json.loads(self.fdefs)
            
    def print_data(self):
        print(self.fdefs)

    def decode_json(self, dict):
        # Have functions that contain an array of statements (which may or may not have arrays/objects inside them)
        # 1) Get function name
        # 2) Check if there is a summary of it
        # a) Create the summary if there is one and go to next function
        # 3) Check if there is already a generated PO file
        # a) If hash is the same, just use that
        # 4) Look into statements and generate proof obligations by necessary things from exprType
        return dict