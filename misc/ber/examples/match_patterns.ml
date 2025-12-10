type 'a option = None | Some of 'a

let bad x =
  match x with 
  | Some y -> false
  | false -> true