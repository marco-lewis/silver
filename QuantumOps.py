import numpy as np
import cmath, re

X = np.array([[0,1],[1,0]])
Y = np.array([[0, 0+1j],[0-1j, 0]])
Z = np.array([[1,0],[0,-1]])

rotX = lambda r: np.array([[np.cos(r/2), 1j * np.sin(r/2)], [-1j * np.sin(r/2), np.cos(r/2)]])
rotY = lambda r: np.array([[np.cos(r/2), np.sin(r/2)], [-np.sin(r/2) ,np.cos(r/2)]])
rotZ = lambda r: np.array([[np.cos(r/2), -1j * np.sin(r/2)], [1j * np.sin(r/2) ,np.cos(r/2)]])

H = 1/np.sqrt(2) * np.array([[1,1],[1,-1]])

phase = lambda r: np.array(np.exp(1j*r))

cnot = np.array([[1,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0]])