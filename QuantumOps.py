import numpy as np
from complex import I

ID = [[1,0],[0,1]]
X = [[0,1],[1,0]]
Y = [[0, I],[0-I, 0]]
Z = [[1,0],[0,-1]]

rotX = lambda r: [[np.cos(r/2), I * np.sin(r/2)], [0-I * np.sin(r/2), np.cos(r/2)]]
rotY = lambda r: [[np.cos(r/2), np.sin(r/2)], [-np.sin(r/2) ,np.cos(r/2)]]
rotZ = lambda r: [[np.cos(r/2), 0-I * np.sin(r/2)], [I * np.sin(r/2) ,np.cos(r/2)]]

# Not used
# H = 1/np.sqrt(2) * np.array([[1,1],[1,-1]])

phase = lambda r: np.array(np.exp(1j*r))

cnot = [[1,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0]]