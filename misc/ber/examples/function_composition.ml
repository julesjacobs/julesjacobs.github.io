let compose f g x = f (g x)

let bool_not b =
  match b with
  | true -> false
  | false -> true

let bool_to_int b = 
  match b with
  | false -> 0
  | true -> 1

let good = compose bool_to_int bool_not
let bad = compose bool_not bool_to_int