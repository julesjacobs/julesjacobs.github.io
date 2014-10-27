from math import *

# We have a cone-shaped tent with height h and radius r
# The volume V = 1/3*pi*r^2*h
# The surface area A = pi*r^2 + pi*r*sqrt(r^2 + h^2)
# We pick a volume V:

V = 10.0

# We rewrite the volume to h = 3*V/(pi*r^2)
# Substitue into area: A = pi*r^2 + pi*r*sqrt(r^2 + (3*V/(pi*r^2))^2)
# This is the function we want to optimize:

def f(r): return pi*r^2 + pi*r*sqrt(r^2 + (3*V/(pi*r^2))^2)

# We also need the first and second derivatives:

def df(r): return pi*(sqrt(r^2 + (3*V/(pi*r^2))^2
