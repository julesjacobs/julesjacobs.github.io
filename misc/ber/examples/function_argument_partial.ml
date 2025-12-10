let bool_not b =
  match b with
  | true -> false
  | false -> true

let both_not (b1,b2) = (bool_not b1, bool_not b2)
  
let bad = both_not (true, 3)