(* 2015-10-13   -*-ocaml-*- *)
(* Peter Sewell                                                       *)

(* This file contains an interpreter, pretty-printer and type-checker
   for the language L1.  To make it go, copy it into a working
   directory, ensure OCaml is available, and type

       ocamlc l1_ocaml.ml 

   That will build an executable a.out, and typing
      
      ./a.out

   will show the reduction sequence of < l1:=3;!l1 , {l1=0 } >.

   You can edit the file and recompile to run

      doit2 ();

   to run the type-checker on the same simple example; you can try
   other examples analogously.  This file doesn't have a parser for
   l1, so you'll have to enter the abstract syntax directly, eg

      prettyreduce (Seq( Assign ("l1",Integer 3), Deref "l1"), [("l1",0)]);

*)

[@@@warning "-37-32-34"]

(* *********************)
(* the abstract syntax *)
(* *********************)

type loc = string

type oper = Plus | GTEQ

type expr = 
  | Integer of int
  | Boolean of bool
  | Op of expr * oper * expr
  | If of expr * expr * expr
  | Assign of loc * expr
  | Deref of loc
  | Skip
  | Seq of expr * expr
  | While of expr * expr


(* **********************************)
(* an interpreter for the semantics *)
(* **********************************)

let is_value v = 
  match v with
  | Integer _n -> true
  | Boolean _b -> true
  | Skip -> true
  | _ -> false

  (* In the semantics, a store is a finite partial function from
  locations to integers.  In the implementation, we represent a store
  as a list of loc*int pairs containing, for each l in the domain of
  the store, exactly one element of the form (l,n).  The operations

    lookup : store -> loc         -> int option
    update : store -> (loc * int) -> store option

  both return NONE if given a location that is not in the domain of
  the store.  This is not a very efficient implementation, but it is
  simple. *)

type store = (loc * int) list

let rec lookup s l = 
  match s with
  | [] -> None
  | (l',n')::s' -> 
    if l=l' then Some n' else lookup s' l 

let rec update' front s (l,n) = 
  match s with
  | [] -> None
  | (l',n')::s' ->
    if l=l' then 
      Some(front @ ((l,n)::s'))
    else 
      update' ((l',n')::front) s' (l,n)

let update s (l,n) = update' [] s (l,n)


  (* now define the single-step function

     reduce :  expr * store -> (expr * store) option 

  which takes a configuration (e,s) and returns either None, if it has
  no transitions, or Some (e',s'), if it has a transition (e,s) -->
  (e',s'). 

  Note that the code depends on global properties of the semantics,
  including the fact that it defines a deterministic transition
  system, so the comments indicating that particular lines of code
  implement particular semantic rules are not the whole story.  *)

let rec reduce (e,(s : store)) = 
  match e with
  | Integer _n -> None
  | Boolean _b -> None
  | Op (e1,opr,e2) -> 
      (match (e1,opr,e2) with
      | (Integer n1, Plus, Integer n2) -> Some(Integer (n1+n2), s)   (*op + *)
      | (Integer n1, GTEQ, Integer n2) -> Some(Boolean (n1 >= n2), s)(*op >=*)
      | (e1,opr,e2) -> (                                               
          if (is_value e1) then 
            (match reduce (e2,s) with
            | Some (e2',s') -> Some (Op(e1,opr,e2'),s')     (* (op2) *)
            | None -> None )                           
          else 
            (match reduce (e1,s) with
            | Some (e1',s') -> Some(Op(e1',opr,e2),s')      (* (op1) *)
            | None -> None ) ) )
  | If (e1,e2,e3) ->
      (match e1 with
      | Boolean(true) -> Some(e2,s)                         (* (if1) *)
      | Boolean(false) -> Some(e3,s)                        (* (if2) *)
      | _ -> 
          (match reduce (e1,s) with
          | Some(e1',s') -> Some(If(e1',e2,e3),s')          (* (if3) *)
          | None -> None ))
  | Deref l -> 
      (match lookup s l with
      | Some n -> Some(Integer n,s)                         (* (deref) *)
      | None -> None )                  
  | Assign (l,e) ->                                  
      (match e with                                                  
      | Integer n -> 
          (match update  s (l,n) with
          | Some s' -> Some(Skip, s')                       (* (assign1) *)
          | None -> None)                                   
      | _ -> 
          (match reduce (e,s) with
          | Some (e',s') -> Some(Assign (l,e'), s')         (* (assign2) *)
          | None -> None  ) )                          
  | While (e1,e2) -> Some( If(e1,Seq(e2,While(e1,e2)),Skip),s) (* (while) *)
  | Skip -> None                                     
  | Seq (e1,e2) ->                                   
    (match e1 with                                                
    | Skip -> Some(e2,s)                                    (* (seq1) *)
    | _ -> 
        (match reduce (e1,s) with
        | Some (e1',s') -> Some(Seq (e1',e2), s')           (* (seq2) *)
        | None -> None ) )


  (* now define the many-step evaluation function

     evaluate :  expr * store -> (expr * store) option 

  which takes a configuration (e,s) and returns the unique (e',s')
  such that   (e,s) -->* (e',s') -/->.  *)

let rec evaluate (e,s) = 
  match reduce (e,s) with
  | None -> (e,s)
  | Some (e',s') -> evaluate (e',s')


(* **********************************)
(* typing                           *)
(* **********************************)

(* types *)

type type_L1 =
  | Ty_int
  | Ty_unit
  | Ty_bool

type type_loc =
  | Ty_intref

type typeEnv = (loc*type_loc) list 

(* in the semantics, type environments gamma are partial functions
from locations to the singleton set {intref}. Here, just as we did for
stores, we represent them as a list of loc*type_loc pairs containing,
for each l in the domain of the type environment, exactly one element
of the form (l,intref).  *)


(* ****************)
(* type inference *)
(* ****************)

(* infertype : typeEnv -> expr -> type_L1 option *)

(* again, we depend on a uniqueness property, without which we would
have to have infertype return a type_L1 list of all the possible types *)

let rec infertype gamma e = 
  match e with
  | Integer _n -> Some Ty_int
  | Boolean _b -> Some Ty_bool
  | Op (e1,opr,e2) ->
      (match (infertype gamma e1, opr, infertype gamma e2) with
      | (Some Ty_int, Plus, Some Ty_int) -> Some Ty_int
      | (Some Ty_int, GTEQ, Some Ty_int) -> Some Ty_bool
      | _ -> None)
  | If (e1,e2,e3) ->
    (match (infertype gamma e1, infertype gamma e2, infertype gamma e3) with
    | (Some Ty_bool, Some t2, Some t3) -> 
        (if t2=t3 then Some t2 else None)
    | _ -> None)
  | Deref l ->
     (match lookup gamma l with
     | Some Ty_intref -> Some Ty_int
     | None -> None)
  | Assign (l,e) ->
      (match (lookup gamma l, infertype gamma e) with
      | (Some Ty_intref,Some Ty_int) -> Some Ty_unit
      | _ -> None)
  | Skip -> Some Ty_unit
  | Seq (e1,e2) ->
     (match (infertype gamma e1, infertype gamma e2) with
     | (Some Ty_unit, Some t2) -> Some t2
     | _ -> None )
  | While (e1,e2) -> 
      (match (infertype gamma e1, infertype gamma e2) with
      | (Some Ty_bool, Some Ty_unit) -> Some Ty_unit 
      | _ -> None )



(* ****************** *)
(* testing machinery  *)
(* ****************** *)
(*;
load "Listsort";
load "Int";
load "Bool";
*)

(* pretty print expressions *)

let prettyprintop op = 
  match op with
  | Plus -> "+"
  | GTEQ ->">="
             
let rec prettyprintexpr e = 
  match e with            
  | Integer n -> string_of_int  n
  | Boolean b -> string_of_bool b
  | Op (e1,opr,e2) ->
      "(" ^ (prettyprintexpr e1) ^ (prettyprintop opr) 
      ^ (prettyprintexpr e2) ^ ")"
  | If (e1,e2,e3) ->
      "if " ^ (prettyprintexpr e1 ) ^ " then " ^ (prettyprintexpr e2)
      ^ " else " ^ (prettyprintexpr e3)
  | Deref l -> "!" ^ l
  | Assign (l,e) ->  l ^ ":=" ^ (prettyprintexpr e)
  | Skip -> "skip"
  | Seq (e1,e2) ->  (prettyprintexpr e1 ) ^ ";" ^ (prettyprintexpr e2)
  | While (e1,e2) ->  
      "while " ^ (prettyprintexpr e1 ) 
      ^ " do " ^ (prettyprintexpr e2)

(* pretty print stores, first sorting by location names for readability *)

let rec rawprintstore s = 
  match s with
  | [] -> ""
  | ((l,n)::pairs) ->
    l ^ "=" ^ (string_of_int n) 
    ^ " " ^ (rawprintstore pairs)

let prettyprintstore pairs = 
  let pairs' = List.sort 
      (function (l,_n) -> function (l',_n') -> compare l l')
      pairs
  in
  "{" ^ rawprintstore pairs' ^ "}" 

(* pretty print configurations *)

let prettyprintconfig (e,s) = 
  "< " ^ (prettyprintexpr e) 
  ^ " , " ^ (prettyprintstore s) ^ " >"

(* do a reduction sequence, printing the initial state and the state
   after each reduction step *)

let rec prettyreduce' (e,s) = 
    match reduce (e,s) with
    | Some (e',s') -> 
        ( Printf.printf "%s" ("\n -->  " ^ prettyprintconfig (e',s') ) ;
          prettyreduce' (e',s'))
    | None -> (Printf.printf "%s" "\n -/->  " ; 
               if is_value e then 
                 Printf.printf "(a value)\n" 
               else 
                 Printf.printf "(stuck - not a value)" )
          
let prettyreduce (e,s) = (Printf.printf "%s" ("      "^(prettyprintconfig (e,s))) ;
                              prettyreduce' (e,s))

(* **************)
(* simple tests *)
(* **************)

(* l1:=3;!l1 *)
let e = Seq( Assign ("l1",Integer 3), Deref "l1")

(* {l1=0 } *)
let s = [("l1",0)]

let doit () = 
  prettyreduce (e, s)
    

(*
 infertype [("l1",intref)] (Seq( Assign ("l1",Integer 3), Deref "l1"));;
*)
let doit2 () = infertype [("l1",Ty_intref)] (Seq( Assign ("l1",Integer 3), Deref "l1"))

let _ = doit ()

let _ = doit2 ()