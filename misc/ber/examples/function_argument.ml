let bool_not b =
  match b with
  | true -> false
  | false -> true
  
let bad = bool_not 3