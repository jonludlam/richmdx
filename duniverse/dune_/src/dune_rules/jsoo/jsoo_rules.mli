(** Generate rules for js_of_ocaml *)

open Import

module Config : sig
  type t

  val all : t list
end

module Version : sig
  type t = int * int

  val of_string : string -> t option

  val compare : t -> t -> Ordering.t
end

val build_cm :
     Super_context.t
  -> dir:Path.Build.t
  -> in_context:Js_of_ocaml.In_context.t
  -> src:Path.t
  -> obj_dir:Path.Build.t Obj_dir.t
  -> config:Config.t option
  -> Action.Full.t Action_builder.With_targets.t Memo.t

val build_exe :
     Compilation_context.t
  -> loc:Loc.t
  -> in_context:Js_of_ocaml.In_context.t
  -> src:Path.Build.t
  -> obj_dir:Path.Build.t Obj_dir.t
  -> top_sorted_modules:Module.t list Action_builder.t
  -> promote:Rule.Promote.t option
  -> linkall:bool Action_builder.t
  -> link_time_code_gen:Link_time_code_gen_type.t Resolve.t
  -> unit Memo.t

val setup_separate_compilation_rules :
  Super_context.t -> string list -> unit Memo.t

val runner : string
