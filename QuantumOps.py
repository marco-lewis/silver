import numpy as np
from complex import I

ID = [[1,0],
      [0,1]]
X = [[0,1],
     [1,0]]
Y = [[0, I],
     [0-I, 0]]
Z = [[1,0],
     [0,-1]]

ROTX = lambda r: [[np.cos(r/2), I * np.sin(r/2)], 
                  [0-I * np.sin(r/2), np.cos(r/2)]]
ROTY = lambda r: [[np.cos(r/2), np.sin(r/2)], 
                  [-np.sin(r/2) ,np.cos(r/2)]]
ROTZ = lambda r: [[np.cos(r/2), 0-I * np.sin(r/2)], 
                  [I * np.sin(r/2) ,np.cos(r/2)]]

def EXP(r):
     if r == 0:
          return 1
     if r == np.pi:
          return -1
     return np.cos(r) + I * np.sin(r)

PHASE = lambda r: EXP(r)

CNOT = [[1,0,0,0], 
        [0,1,0,0], 
        [0,0,0,1], 
        [0,0,1,0]]