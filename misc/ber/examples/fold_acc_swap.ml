type 'a list = Nil | Cons of 'a * 'a list

let rec fold f z xs =
  match xs with
  | Nil -> z
  | Cons(x,xs') -> f x (fold f z xs')

let folder (x : int) (y : bool) = x

let bad = fold folder