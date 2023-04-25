type word = char list
type guess = char * int
type guesses = guess list
type response =
  | Green of char
  | Amber of char
  | Black


let mapi fn xs =
    let rec inner i xs =
        match xs with
        | x::xs -> (fn i x)::inner (i+1) xs
        | [] -> []
    in inner 0 xs

let rec lookfor a xs =
    match xs with
    | (b, a')::xs -> if a=a' then Some b else lookfor a xs
    | [] -> None

let respond (word : word) (guesses : guesses) =
    let rec contains_c word c =
      match word with
      | c' :: cs -> c=c' || contains_c cs c
      | [] -> false
    in
    mapi (fun i c ->
      match lookfor i guesses with
      | Some c' ->
        if c=c' then Green c
        else if contains_c word c then Amber c
        else Black
      | None -> Black) word


let _ = ignore respond