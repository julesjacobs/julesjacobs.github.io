from math import sqrt

n = 5  # number of bits in our state
        # we represent bit strings as integers

def print_state(s):
  print(" + ".join([f'{s[i]:.5f}|{bin(i)[2:].zfill(n)}>'
                          for i in range(len(s)) if s[i] != 0]))

# gives the basis state |x>, where x is a string of 0's and 1's
def basis(x):
  s = [0]*2**n
  s[int(x,base=2)] = 1
  return s


# apply the classical gate C_f, where f is a bijective function on bit strings
def classical(s,f):
  s2 = [0]*2**n
  for x in range(2**n):
    s2[f(x)] = s[x]
  return s2

# apply the Hadamard gate H_k, where k is the bit to apply the gate to
def hadamard(s,k):
  bitk = 1 << k
  s2 = [0]*2**n
  for x in range(2**n):
    sign = (-1)**((x >> k) & 1)
    s2[x] = (s[x & ~bitk] + sign*s[x | bitk])/sqrt(2)
  return s2

# example
s = basis("10101")
print_state(s) # 1.00000|10101>
s = hadamard(s,1)
print_state(s) # 0.70711|10101> + 0.70711|10111>
s = classical(s, lambda x: ~x)
print_state(s) # 0.70711|01000> + 0.70711|01010>
s = hadamard(s,3)
print_state(s) # 0.50000|00000> + 0.50000|00010> + -0.50000|01000> + -0.50000|01010>
s = hadamard(s,1)
print_state(s) # 0.70711|00000> + -0.70711|01000>