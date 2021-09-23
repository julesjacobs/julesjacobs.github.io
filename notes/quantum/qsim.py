from math import sqrt

n = 5  # number of bits in our state
       # we represent bit strings as integers

def print_state(s):
  print(" + ".join([f'{s[i]}|{bin(i)[2:].zfill(n)}>'
                      for i in range(len(s)) if s[i] != 0]))

# initialize a state such as |00010>, where k indicates the position of the 1
def init(k):
  s = [0]*2**n
  s[1 << k] = 1
  return s

# apply a classical gate to the state, where f is a bijective function on bit strings
def classical(s,f):
  s2 = [0]*2**n
  for x in range(2**n):
    s2[f(x)] = s[x]
  return s2

# apply the Hadamard gate to bit k
def hadamard(s,k):
  bitk = 1 << k
  s2 = [0]*2**n
  for x in range(2**n):
    sign = (-1)**((x >> k) & 1)
    s2[x] = (s[x & ~bitk] + sign*s[x | bitk])/sqrt(2)
  return s2

# example
s = init(1)
print_state(s)              # 1|00010>
print()
print_state(hadamard(s,0))  # 0.7071067811865475|00010> + 0.7071067811865475|00011>
print()
print_state(hadamard(s,1))  # 0.7071067811865475|00000> + -0.7071067811865475|00010>