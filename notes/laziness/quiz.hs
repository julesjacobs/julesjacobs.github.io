fib = 1 : 1 : zipWith (+) fib (tail fib)

cp1 xs = case xs of [x] -> [x] ; xs -> xs
cp2 xs = case xs of [] -> [] ; xs -> xs
cp3 xs = xs !! 0 : xs !! 1 : tail (tail xs)

fib1 = 1 : 1 : zipWith (+) fib1 (cp1 (tail fib1))
fib2 = 1 : 1 : zipWith (+) fib2 (tail (cp1 fib2))
fib3 = 1 : 1 : zipWith (+) fib3 (cp2 (tail fib3))
fib4 = 1 : 1 : zipWith (+) fib4 (tail (cp2 fib4))
fib5 = 1 : 1 : zipWith (+) fib5 (cp3 (tail fib5))
fib6 = 1 : 1 : zipWith (+) fib6 (tail (cp3 fib6))
fib7 = 1 : 1 : zipWith (+) fib7 (tail (tail fib7))
fib8 = 1 : zipWith (+) fib8 (tail fib8)
fib9 = 1 : 1 : zipWith (+) (tail fib9) (tail fib9)
fib10 = 1 : 1 : zipWith (+) fib10 (cp1 (cp3 (tail fib10)))
fib11 = 1 : 1 : zipWith (+) fib11 (cp3 (cp1 (tail fib11)))
fib12 = 1 : 1 : zipWith (+) fib12 (cp3 (tail (cp1 fib12)))
fib13 = 1 : 1 : zipWith (+) fib13 (cp1 (tail (cp3 fib13)))