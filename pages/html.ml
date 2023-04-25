(* Html.ml *)
open Tyxml.Html

let table : string list -> string list list -> _ = fun headings data ->
  let ccls i = a_class [ Printf.sprintf "column%d" i ] in
  table ~thead:(thead
      [tr (List.mapi (fun i h -> th ~a:[ ccls i ] [txt h]) headings)])
      (List.map (fun row ->
        tr (List.mapi (fun i d -> td ~a:[ ccls i ] [txt d]) row)) data
      )
  