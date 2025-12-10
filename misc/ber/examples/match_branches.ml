type 'a option = None | Some of 'a

let x = Some 3

let bad =
  match x with 
  | None -> Some false
  | Some y -> y