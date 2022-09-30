(lang dune 3.0)

(using mdx 0.2)

(name richmdx)
(version 0.0.1)
(generate_opam_files true)

(license MIT)
(authors "Jon Ludlam")
(maintainers "jon@recoil.org")

(package
 (name richmdx)
 (synopsis "Promotable mld files with rich content")
 (description "Description goes here")
 (depends
  mdx
  odoc
  imagelib
  mime_printer
  base64
  ))

