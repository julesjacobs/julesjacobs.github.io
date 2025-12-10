let compose f g x = f (g x)

let bool_not b =
  match b with
  | true -> false
  | false -> true

let bad = compose bool_not bool_not 3