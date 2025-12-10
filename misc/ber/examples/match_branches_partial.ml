type 'a option = None | Some of 'a

let x = Some 3

let bad =
  match x with 
  | Some y -> (y, y)
  | None -> (1, true)
