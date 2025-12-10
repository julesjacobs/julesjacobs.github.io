type 'a list = Nil | Cons of 'a * 'a list

let bool_and b1 b2 =
  match b1 with
  | true -> b2
  | false -> false

let rec fold f z xs =
  match xs with
  | Nil -> z
  | Cons(x,xs') -> f x (fold f z xs')

let xs = Cons(true, Cons(false, Nil))
let bad = fold xs bool_and true
