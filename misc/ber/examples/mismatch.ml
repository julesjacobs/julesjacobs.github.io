type 'a list = Nil | Cons of 'a * 'a list

let bool_not b =
  match b with
  | true -> false
  | false -> true

let demo =
  (* Intentional mismatch: bool_not expects a bool but gets an int. *)
  Cons (bool_not 0, Nil)
