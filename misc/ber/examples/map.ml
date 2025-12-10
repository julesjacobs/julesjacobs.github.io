type 'a list = Nil | Cons of 'a * 'a list

let rec map f xs =
  match xs with
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (f hd, map f tl)

let inc x = x + 1
let shout s = s ^ "!"

let nums = Cons (1, Cons (2, Cons (3, Nil)))
let words = Cons ("hi", Cons ("ber", Nil))

let mapped_nums = map inc nums
let mapped_words = map shout words
