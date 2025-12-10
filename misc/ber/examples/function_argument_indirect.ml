let bool_not b =
  match b with
  | true -> false
  | false -> true

let id x = x

let compose f g x = f (g x)
  
let bad = (id bool_not) (compose id id 3)