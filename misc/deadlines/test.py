import itertools

def generate_tuples(n, k, sorted=True, duplicates=False):
    if sorted and duplicates:
        return itertools.combinations_with_replacement(range(n), k)
    elif sorted and not duplicates:
        return itertools.combinations(range(n), k)
    elif not sorted and duplicates:
        return itertools.product(range(n), repeat=k)
    else:
        return itertools.permutations(range(n), k)

def generalized_product(xss, k):
    return [[xss[a[i]][i] for i in range(k)] for a in generate_tuples(len(xss), k, duplicates=True, sorted=False)]

def generalized_permutations(xss, k):
    return [[xss[a[i]][i] for i in range(k)] for a in generate_tuples(len(xss), k, duplicates=False, sorted=False)]

def generalized_combinations(xss, k):
    return [[xss[a[i]][i] for i in range(k)] for a in generate_tuples(len(xss), k, duplicates=False, sorted=True)]

def generalized_combinations_with_replacement(xss, k):
    return [[xss[a[i]][i] for i in range(k)] for a in generate_tuples(len(xss), k, duplicates=True, sorted=True)]

# Example usage:
sequences = [
    [1, 2],
    ['a', 'b'],
    [True, False]
]

print("Product:", list(generalized_product(sequences, 2)))
print("Permutations:", list(generalized_permutations(sequences, 2)))
print("Combinations:", list(generalized_combinations(sequences, 2)))
print("Combinations with Replacement:", list(generalized_combinations_with_replacement(sequences, 2)))