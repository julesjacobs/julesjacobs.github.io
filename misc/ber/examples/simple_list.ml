type 'a list = Nil | Cons of 'a * 'a list

let bad =
  Cons (2, Cons (true, Nil))
