using LinearAlgebra

p = [
    (3.0, [1,1,1,1]),

    (1.0, [2,1,1,1]),
    (1.0, [1,2,1,1]),
    (1.0, [1,1,2,1]),
    (1.0, [1,1,1,2]),

    (2.0, [1,1,0,0]),
    (2.0, [1,0,1,0]),
    (2.0, [1,0,0,1]),
    (2.0, [0,1,1,0]),
    (2.0, [0,1,0,1]),
    (2.0, [0,0,1,1]),
]

n = 4
A = rand(n,n)
xs = eigvals(A)

s = sum([
    c*prod([xs[i]^powers[i] for i in 1:4])
    for (c,powers) in p
])

r = sum([
    c*det([(A^powers[i])[i,j] for i in 1:n, j in 1:n])
    for (c,powers) in p
])
