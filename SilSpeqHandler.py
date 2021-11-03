import os

class SilSpeqHandler():
    def __init__(self, silq_json_file):
        self.silq_json_file = silq_json_file
        self.__spq_file = os.path.splitext(self.silq_json_file)[0]+'.spq'

    def make_silspeq_file(self, functions):
        spq = ""
        with open(self.__spq_file, 'w') as f:
            for func in functions:
                name = func['func']
                args = func['args']
                spq += name + "("
                # TODO: Handle args here
                # TODO: Replace type from N to return type
                spq += ")->(define " + name + "_ret : N" + ")\n"
                spq += "pre{\n\n}\npost{\n\n}"
            f.write(spq)
        pass
    
    def open_spq_file(self):
        try:
            with open(self.__spq_file, 'r') as f:
                spq = f.read()
                print("A SilSpeq file exists")
        except FileNotFoundError:
            self.make_silspeq_file()
            print("A SilSpeq file has been generated. You should add your specification first before running your code again.")
            exit()