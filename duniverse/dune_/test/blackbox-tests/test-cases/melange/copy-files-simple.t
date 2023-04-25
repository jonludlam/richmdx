Test simple interactions between melange.emit and copy_files

  $ cat > dune-project <<EOF
  > (lang dune 3.7)
  > (using melange 0.1)
  > EOF

  $ cat > dune <<EOF
  > (melange.emit
  >  (target output)
  >  (alias mel)
  >  (module_system commonjs))
  > 
  > (copy_files
  >  (alias mel)
  >  (files assets/file.txt))
  > EOF

  $ mkdir assets
  $ cat > assets/file.txt <<EOF
  > hello from file
  > EOF

  $ cat > main.ml <<EOF
  > let dirname = [%bs.raw "__dirname"]
  > let file_path = "../assets/file.txt"
  > let file_content = Node.Fs.readFileSync (dirname ^ "/" ^ file_path) \`utf8
  > let () = Js.log file_content
  > EOF

  $ dune build @mel
  $ node _build/default/output/main.js
  hello from file
  
Copy the file into the output folder, so we can use same path as in-source

  $ cat > dune <<EOF
  > (melange.emit
  >  (target output)
  >  (alias mel)
  >  (module_system commonjs))
  > 
  > (subdir output
  >  (subdir assets
  >   (copy_files (alias mel) (files %{project_root}/assets/file.txt))))
  > EOF

  $ cat > main.ml <<EOF
  > let dirname = [%bs.raw "__dirname"]
  > let file_path = "assets/file.txt"
  > let file_content = Node.Fs.readFileSync (dirname ^ "/" ^ file_path) \`utf8
  > let () = Js.log file_content
  > EOF

  $ dune build @mel
  $ node _build/default/output/main.js
  hello from file
  
