(*
 * Copyright (c) 2018 Thomas Gazagnaire <thomas@gazagnaire.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

let src = Logs.Src.create "ocaml-mdx"

module Log = (val Logs.src_log src : Logs.LOG)
open Astring
open Misc

type t = {
  vpad : int;
  hpad : int;
  pos : Lexing.position;
  command : string list;
  output : Output.t list;
}

let dump_line ppf = function
  | #Output.t as o -> Output.dump ppf o
  | `Command (c, _) -> Fmt.pf ppf "`Command %a" Fmt.(Dump.list dump_string) c

let dump_lines = Fmt.(Dump.list dump_line)

let dump ppf { vpad; hpad; command; output; _ } =
  Fmt.pf ppf "@[{vpad=%d;@ hpad=%d;@ command=%a;@ output=%a}@]" vpad hpad
    Fmt.(Dump.list dump_string)
    command
    Fmt.(Dump.list Output.dump)
    output

let pp_vpad ppf t =
  let rec aux = function
    | 0 -> ()
    | i ->
        Fmt.pf ppf "\n";
        aux (i - 1)
  in
  aux t.vpad

let pp_command ppf (t : t) =
  match t.command with
  | [] -> ()
  | l ->
      pp_vpad ppf t;
      List.iteri
        (fun i s ->
          if i = 0 then Fmt.pf ppf "%a# %s\n" pp_pad t.hpad s
          else
            match s with
            | "" -> Fmt.string ppf "\n"
            | _ -> Fmt.pf ppf "%a  %s\n" pp_pad t.hpad s)
        l

let pp ppf (t : t) =
  pp_command ppf t;
  pp_lines (Output.pp ~pad:t.vpad) ppf t.output

let lexbuf ~(pos : Lexing.position) s =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_start_p <- pos;
  lexbuf.lex_curr_p <- pos;
  lexbuf

let vpad_of_lines t =
  let rec aux i = function
    | `Output h :: t when String.trim h = "" -> aux (i + 1) t
    | t -> (i, t)
  in
  aux 0 t

let of_lines ~syntax ~(loc : Location.t) t =
  let pos = loc.loc_start in
  let hpad =
    match syntax with
    | Syntax.Mli -> pos.pos_cnum + 2
    | _ -> hpad_of_lines t
  in
  let unpad line =
    match syntax with
    | Syntax.Mli -> String.trim line
    | Syntax.Normal | Syntax.Cram | Syntax.Mld ->
        if String.is_empty line then line
        else if String.length line < hpad then
          Fmt.failwith "invalid padding: %S" line
        else String.with_index_range line ~first:hpad
  in
  let lines = List.map unpad t in
  let lines =
    match syntax with Syntax.Mli | Syntax.Mld -> "" :: lines | _ -> lines
  in
  let lines = String.concat ~sep:"\n" lines in
  let lines = Lexer_top.token (lexbuf ~pos lines) in
  let vpad, lines = vpad_of_lines lines in
  Log.debug (fun l ->
      l "Toplevel.of_lines (vpad=%d, hpad=%d) %a" vpad hpad dump_lines lines);
  let mk vpad (command, (loc : Location.t)) output =
    { vpad; hpad; pos = loc.loc_start; command; output = List.rev output }
  in
  let rec aux vpad command output acc = function
    | [] -> List.rev (mk vpad command output :: acc)
    | (`Ellipsis as o) :: t -> aux vpad command (o :: output) acc t
    | (`Output _ as o) :: t -> aux vpad command (o :: output) acc t
    | `Command cmd :: t ->
        let vpad', output = vpad_of_lines output in
        aux vpad' cmd [] (mk vpad command output :: acc) t
  in
  match lines with
  | `Command cmd :: t -> aux vpad cmd [] [] t
  | _ -> Fmt.failwith "invalid toplevel block: %a" Fmt.(Dump.list string) t
