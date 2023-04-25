open Import
open Dune_file
open Memo.O
module Modules_group = Modules

module Origin = struct
  type t =
    | Library of Dune_file.Library.t
    | Executables of Dune_file.Executables.t
    | Melange of Melange_stanzas.Emit.t

  let loc = function
    | Library l -> l.buildable.loc
    | Executables e -> e.buildable.loc
    | Melange mel -> mel.loc
end

module Modules = struct
  type component = Modules.t * Path.Build.t Obj_dir.t

  type t =
    { libraries : component Lib_name.Map.t
    ; executables : component String.Map.t
    ; melange_emits : component String.Map.t
    ; (* Map from modules to the origin they are part of *)
      rev_map : Origin.t Module_name.Path.Map.t
    }

  let empty =
    { libraries = Lib_name.Map.empty
    ; executables = String.Map.empty
    ; melange_emits = String.Map.empty
    ; rev_map = Module_name.Path.Map.empty
    }

  type 'stanza group_part =
    'stanza
    * (Loc.t * Module.Source.t) Module_trie.t
    * Modules_group.t
    * Path.Build.t Obj_dir.t

  type groups =
    { libraries : Library.t group_part list
    ; executables : Executables.t group_part list
    ; melange_emits : Melange_stanzas.Emit.t group_part list
    }

  let make { libraries = libs; executables = exes; melange_emits = emits } =
    let libraries =
      match
        Lib_name.Map.of_list_map libs ~f:(fun (lib, _, m, obj_dir) ->
            (Library.best_name lib, (m, obj_dir)))
      with
      | Ok x -> x
      | Error (name, _, (lib2, _, _, _)) ->
        User_error.raise ~loc:lib2.buildable.loc
          [ Pp.textf "Library %S appears for the second time in this directory"
              (Lib_name.to_string name)
          ]
    in
    let executables =
      match
        String.Map.of_list_map exes
          ~f:(fun ((exes : Executables.t), _, m, obj_dir) ->
            (snd (List.hd exes.names), (m, obj_dir)))
      with
      | Ok x -> x
      | Error (name, _, (exes2, _, _, _)) ->
        User_error.raise ~loc:exes2.buildable.loc
          [ Pp.textf
              "Executable %S appears for the second time in this directory" name
          ]
    in
    let melange_emits =
      match
        String.Map.of_list_map emits ~f:(fun (mel, _, m, obj_dir) ->
            (mel.target, (m, obj_dir)))
      with
      | Ok x -> x
      | Error (name, _, (mel, _, _, _)) ->
        User_error.raise ~loc:mel.loc
          [ Pp.textf "Target %S appears for the second time in this directory"
              name
          ]
    in
    let rev_map =
      let modules =
        let by_path (origin : Origin.t) trie =
          Module_trie.fold trie ~init:[] ~f:(fun (_loc, m) acc ->
              (Module.Source.path m, origin) :: acc)
        in
        List.concat
          [ List.concat_map libs ~f:(fun (l, m, _, _) -> by_path (Library l) m)
          ; List.concat_map exes ~f:(fun (e, m, _, _) ->
                by_path (Executables e) m)
          ; List.concat_map emits ~f:(fun (l, m, _, _) -> by_path (Melange l) m)
          ]
      in
      match Module_name.Path.Map.of_list modules with
      | Ok x -> x
      | Error (path, _, _) ->
        let locs =
          List.filter_map modules ~f:(fun (n, origin) ->
              Option.some_if
                (Ordering.is_eq (Module_name.Path.compare n path))
                (Origin.loc origin))
          |> List.sort ~compare:Loc.compare
        in
        let main_message =
          Pp.textf "Module %S is used in several stanzas:"
            (Module_name.Path.to_string path)
        in
        let loc, related_locs =
          match locs with
          | [] ->
            (* duplicates imply at least at one module with this location *)
            assert false
          | loc :: related_locs -> (loc, related_locs)
        in
        let annots =
          let main = User_message.make ~loc [ main_message ] in
          let related =
            List.map related_locs ~f:(fun loc ->
                User_message.make ~loc [ Pp.text "Used in this stanza" ])
          in
          User_message.Annots.singleton Compound_user_error.annot
            [ Compound_user_error.make ~main ~related ]
        in
        User_error.raise ~annots ~loc:(Loc.drop_position loc)
          [ main_message
          ; Pp.enumerate locs ~f:(fun loc ->
                Pp.verbatim (Loc.to_file_colon_line loc))
          ; Pp.text
              "To fix this error, you must specify an explicit \"modules\" \
               field in every library, executable, and executables stanzas in \
               this dune file. Note that each module cannot appear in more \
               than one \"modules\" field - it must belong to a single library \
               or executable."
          ]
    in
    { libraries; executables; melange_emits; rev_map }
end

module Artifacts = struct
  type t =
    { libraries : Lib_info.local Lib_name.Map.t
    ; modules : (Path.Build.t Obj_dir.t * Module.t) Module_name.Map.t
    }

  let empty =
    { libraries = Lib_name.Map.empty; modules = Module_name.Map.empty }

  let lookup_module { modules; libraries = _ } = Module_name.Map.find modules

  let lookup_library { libraries; modules = _ } = Lib_name.Map.find libraries

  let make ~dir ~lib_config ~libs ~exes =
    let+ libraries =
      Memo.List.map libs ~f:(fun (lib, _, _, _) ->
          let name = Lib_name.of_local lib.Library.name in
          let+ info = Dune_file.Library.to_lib_info lib ~dir ~lib_config in
          (name, info))
      >>| Lib_name.Map.of_list_exn
    in
    let modules =
      let by_name modules obj_dir =
        Modules_group.fold_user_available ~init:modules ~f:(fun m modules ->
            Module_name.Map.add_exn modules (Module.name m) (obj_dir, m))
      in
      let init =
        List.fold_left exes ~init:Module_name.Map.empty
          ~f:(fun modules (_, _, m, obj_dir) -> by_name modules obj_dir m)
      in
      List.fold_left libs ~init ~f:(fun modules (_, _, m, obj_dir) ->
          by_name modules obj_dir m)
    in
    { libraries; modules }
end

type t =
  { modules : Modules.t
  ; artifacts : Artifacts.t Memo.Lazy.t
  }

let empty =
  { modules = Modules.empty; artifacts = Memo.Lazy.of_val Artifacts.empty }

let artifacts t = Memo.Lazy.force t.artifacts

let modules_of_files ~path ~dialects ~dir ~files =
  let dir = Path.build dir in
  let impl_files, intf_files =
    let make_module dialect name fn =
      (name, Module.File.make dialect (Path.relative dir fn))
    in
    let loc = Loc.in_dir dir in
    String.Set.to_list files
    |> List.filter_partition_map ~f:(fun fn ->
           (* we aren't using Filename.extension because we want to handle
              filenames such as foo.cppo.ml *)
           match String.lsplit2 fn ~on:'.' with
           | None -> Skip
           | Some (s, ext) -> (
             match Dialect.DB.find_by_extension dialects ("." ^ ext) with
             | None -> Skip
             | Some (dialect, ml_kind) -> (
               let name = Module_name.of_string_allow_invalid (loc, s) in
               let module_ = make_module dialect name fn in
               match ml_kind with
               | Impl -> Left module_
               | Intf -> Right module_)))
  in
  let parse_one_set (files : (Module_name.t * Module.File.t) list) =
    match Module_name.Map.of_list files with
    | Ok x -> x
    | Error (name, f1, f2) ->
      let src_dir = Path.drop_build_context_exn dir in
      User_error.raise
        [ Pp.textf "Too many files for module %s in %s:"
            (Module_name.to_string name)
            (Path.Source.to_string_maybe_quoted src_dir)
        ; Pp.textf "- %s" (Path.to_string_maybe_quoted (Module.File.path f1))
        ; Pp.textf "- %s" (Path.to_string_maybe_quoted (Module.File.path f2))
        ]
  in
  let impls = parse_one_set impl_files in
  let intfs = parse_one_set intf_files in
  Module_name.Map.merge impls intfs ~f:(fun name impl intf ->
      Some (Module.Source.make (path @ [ name ]) ?impl ?intf))

type for_ =
  | Library of Lib_name.t
  | Exe of { first_exe : string }
  | Melange of { target : string }

let dyn_of_for_ =
  let open Dyn in
  function
  | Library n -> variant "Library" [ Lib_name.to_dyn n ]
  | Exe { first_exe } ->
    variant "Exe" [ record [ ("first_exe", string first_exe) ] ]
  | Melange { target } ->
    variant "Melange" [ record [ ("target", string target) ] ]

let modules_and_obj_dir t ~for_ =
  match
    match for_ with
    | Library name -> Lib_name.Map.find t.modules.libraries name
    | Exe { first_exe } -> String.Map.find t.modules.executables first_exe
    | Melange { target } -> String.Map.find t.modules.melange_emits target
  with
  | Some s -> s
  | None ->
    let map =
      match for_ with
      | Library _ ->
        Lib_name.Map.keys t.modules.libraries |> Dyn.list Lib_name.to_dyn
      | Exe _ -> String.Map.keys t.modules.executables |> Dyn.(list string)
      | Melange _ ->
        String.Map.keys t.modules.melange_emits |> Dyn.(list string)
    in
    Code_error.raise "modules_and_obj_dir: failed lookup"
      [ ("keys", map); ("for_", dyn_of_for_ for_) ]

let modules t ~for_ = modules_and_obj_dir t ~for_ |> fst

let find_origin (t : t) name =
  (* TODO generalize to any path *)
  Module_name.Path.Map.find t.modules.rev_map [ name ]

let virtual_modules ~lookup_vlib vlib =
  let info = Lib.info vlib in
  let+ modules =
    match Option.value_exn (Lib_info.virtual_ info) with
    | External modules -> Memo.return modules
    | Local ->
      let src_dir = Lib_info.src_dir info |> Path.as_in_build_dir_exn in
      let+ t = lookup_vlib ~dir:src_dir in
      modules t ~for_:(Library (Lib.name vlib))
  in
  let existing_virtual_modules = Modules_group.virtual_module_names modules in
  let allow_new_public_modules =
    Modules_group.wrapped modules |> Wrapped.to_bool |> not
  in
  { Modules_field_evaluator.Implementation.existing_virtual_modules
  ; allow_new_public_modules
  }

let make_lib_modules ~dir ~libs ~lookup_vlib ~(lib : Library.t) ~modules
    ~include_subdirs:
      (loc_include_subdirs, (include_subdirs : Dune_file.Include_subdirs.t)) =
  let open Resolve.Memo.O in
  let+ kind, main_module_name, wrapped =
    match lib.implements with
    | None ->
      (* In the two following pattern matching, we can only get [From _] if
         [lib] is an implementation. Since we know that it is not one because of
         the above [match lib.implements with ...], we know that we can't get
         [From _]. That's why we have these [assert false]. *)
      let main_module_name =
        match Library.main_module_name lib with
        | This x -> x
        | From _ -> assert false
      in
      let wrapped =
        match lib.wrapped with
        | This x -> x
        | From _ -> assert false
      in
      let kind : Modules_field_evaluator.kind =
        match lib.virtual_modules with
        | None -> Exe_or_normal_lib
        | Some virtual_modules -> Virtual { virtual_modules }
      in
      Memo.return (Resolve.return (kind, main_module_name, wrapped))
    | Some _ ->
      assert (Option.is_none lib.virtual_modules);
      let open Memo.O in
      let* resolved =
        let name = Library.best_name lib in
        Lib.DB.find_even_when_hidden libs name
        (* can't happen because this library is defined using the current
           stanza *)
        >>| Option.value_exn
      in
      let open Resolve.Memo.O in
      (* This [Option.value_exn] is correct because the above [lib.implements]
         is [Some _] and this [lib] variable correspond to the same library. *)
      let* vlib = Option.value_exn (Lib.implements resolved) in
      let* wrapped = Lib.wrapped resolved in
      let wrapped = Option.value_exn wrapped in
      let* main_module_name = Lib.main_module_name resolved in
      let+ impl = Resolve.Memo.lift_memo (virtual_modules ~lookup_vlib vlib) in
      let kind : Modules_field_evaluator.kind = Implementation impl in
      (kind, main_module_name, wrapped)
  in
  let sources, modules =
    let { Buildable.loc = stanza_loc; modules = modules_settings; _ } =
      lib.buildable
    in
    Modules_field_evaluator.eval ~modules ~stanza_loc ~kind
      ~private_modules:
        (Option.value ~default:Ordered_set_lang.standard lib.private_modules)
      ~src_dir:dir modules_settings
  in
  let () =
    match (lib.stdlib, include_subdirs) with
    | Some stdlib, Include Qualified ->
      let main_message =
        Pp.text
          "a library with (stdlib ...) may not use (include_subdirs qualified)"
      in
      let annots =
        let main =
          User_message.make ~loc:loc_include_subdirs [ main_message ]
        in
        let related =
          [ User_message.make ~loc:stdlib.loc [ Pp.text "Already defined here" ]
          ]
        in
        User_message.Annots.singleton Compound_user_error.annot
          [ Compound_user_error.make ~main ~related ]
      in
      User_error.raise ~annots ~loc:loc_include_subdirs [ main_message ]
    | _, _ -> ()
  in
  let implements = Option.is_some lib.implements in
  let _loc, lib_name = lib.name in
  ( sources
  , Modules_group.lib ~stdlib:lib.stdlib ~implements ~lib_name ~obj_dir:dir
      ~modules ~main_module_name ~wrapped )

let modules_of_stanzas dune_file ~dir ~scope ~lookup_vlib ~modules
    ~include_subdirs =
  let rev_filter_partition =
    let rec loop l (acc : Modules.groups) =
      match l with
      | [] -> acc
      | x :: l -> (
        match x with
        | `Skip -> loop l acc
        | `Library y -> loop l { acc with libraries = y :: acc.libraries }
        | `Executables y ->
          loop l { acc with executables = y :: acc.executables }
        | `Melange_emit y ->
          loop l { acc with melange_emits = y :: acc.melange_emits })
    in
    fun l -> loop l { libraries = []; executables = []; melange_emits = [] }
  in
  let filter_partition_map l =
    let { Modules.libraries; executables; melange_emits } =
      rev_filter_partition l
    in
    { Modules.libraries = List.rev libraries
    ; executables = List.rev executables
    ; melange_emits = List.rev melange_emits
    }
  in
  Memo.parallel_map dune_file.stanzas ~f:(fun stanza ->
      match (stanza : Stanza.t) with
      | Library lib ->
        (* jeremiedimino: this [Resolve.get] means that if the user writes an
           invalid [implements] field, we will get an error immediately even if
           the library is not built. We should change this to carry the
           [Or_exn.t] a bit longer. *)
        let+ sources, modules =
          let lookup_vlib = lookup_vlib ~loc:lib.buildable.loc in
          make_lib_modules ~dir ~libs:(Scope.libs scope) ~lookup_vlib ~modules
            ~lib ~include_subdirs
          >>= Resolve.read_memo
        in
        let obj_dir = Library.obj_dir lib ~dir in
        `Library (lib, sources, modules, obj_dir)
      | Executables exes | Tests { exes; _ } ->
        let obj_dir = Dune_file.Executables.obj_dir ~dir exes in
        let sources, modules =
          let { Buildable.loc = stanza_loc; modules = modules_settings; _ } =
            exes.buildable
          in
          Modules_field_evaluator.eval ~modules ~stanza_loc
            ~kind:Modules_field_evaluator.Exe_or_normal_lib
            ~private_modules:Ordered_set_lang.standard ~src_dir:dir
            modules_settings
        in
        let modules =
          let project = Scope.project scope in
          let obj_dir = Obj_dir.obj_dir obj_dir in
          if Dune_project.wrapped_executables project then
            Modules_group.make_wrapped ~obj_dir ~modules `Exe
          else Modules_group.exe_unwrapped modules ~obj_dir
        in
        Memo.return (`Executables (exes, sources, modules, obj_dir))
      | Melange_stanzas.Emit.T mel ->
        let obj_dir = Obj_dir.make_melange_emit ~dir ~name:mel.target in
        let sources, modules =
          Modules_field_evaluator.eval ~modules ~stanza_loc:mel.loc
            ~kind:Modules_field_evaluator.Exe_or_normal_lib
            ~private_modules:Ordered_set_lang.standard ~src_dir:dir mel.modules
        in
        let modules =
          Modules_group.make_wrapped ~obj_dir:(Obj_dir.obj_dir obj_dir) ~modules
            `Melange
        in
        Memo.return (`Melange_emit (mel, sources, modules, obj_dir))
      | _ -> Memo.return `Skip)
  >>| filter_partition_map

let make dune_file ~dir ~scope ~lib_config ~loc ~lookup_vlib
    ~include_subdirs:
      (loc_include_subdirs, (include_subdirs : Dune_file.Include_subdirs.t))
    ~dirs =
  let+ modules_of_stanzas =
    let modules =
      let dialects = Dune_project.dialects (Scope.project scope) in
      match include_subdirs with
      | Include Qualified ->
        List.fold_left dirs ~init:Module_trie.empty
          ~f:(fun acc ((dir : Path.Build.t), local, files) ->
            let path = List.map local ~f:Module_name.of_string in
            let modules = modules_of_files ~dialects ~dir ~files ~path in
            match Module_trie.set_map acc path modules with
            | Ok s -> s
            | Error module_ ->
              let module_ =
                match module_ with
                | Leaf m ->
                  Module.Source.files m |> List.hd |> Module.File.path
                  |> Path.drop_optional_build_context
                  |> Path.to_string_maybe_quoted
                | Map _ ->
                  (* it's not possible to define the same group twice because
                     there can be at most one directory *)
                  assert false
              in
              let group =
                (dir |> Path.Build.drop_build_context_exn
               |> Path.Source.to_string_maybe_quoted)
                ^ "/"
              in
              User_error.raise ~loc
                [ Pp.text
                    "The following module and module group cannot co-exist in \
                     the same executable or library because they correspond to \
                     the same module path"
                ; Pp.textf "- module %s" module_
                ; Pp.textf "- module group %s" group
                ])
      | No | Include Unqualified ->
        List.fold_left dirs ~init:Module_name.Map.empty
          ~f:(fun acc ((dir : Path.Build.t), _local, files) ->
            let modules = modules_of_files ~dialects ~dir ~files ~path:[] in
            Module_name.Map.union acc modules ~f:(fun name x y ->
                User_error.raise ~loc
                  [ Pp.textf "Module %S appears in several directories:"
                      (Module_name.to_string name)
                  ; Pp.textf "- %s"
                      (Path.to_string_maybe_quoted (Module.Source.src_dir x))
                  ; Pp.textf "- %s"
                      (Path.to_string_maybe_quoted (Module.Source.src_dir y))
                  ; Pp.text "This is not allowed, please rename one of them."
                  ]))
        |> Module_trie.of_map
    in
    modules_of_stanzas dune_file ~dir ~scope ~lookup_vlib ~modules
      ~include_subdirs:(loc_include_subdirs, include_subdirs)
  in
  let modules = Modules.make modules_of_stanzas in
  let artifacts =
    Memo.lazy_ (fun () ->
        Artifacts.make ~dir ~lib_config ~libs:modules_of_stanzas.libraries
          ~exes:modules_of_stanzas.executables)
  in
  { modules; artifacts }
