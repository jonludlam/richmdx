type encoding = Noencoding | Base64
type t = { mime_type : string; encoding : encoding; data : string }

let dummy = { mime_type="text/odoc"; encoding=Noencoding; data="hello"}
let outputs : t list ref = ref []

let push ?(encoding = Noencoding) mime_type data =
  outputs := { mime_type; encoding; data } :: !outputs

let get () =
  let result = !outputs in
  outputs := [];
  result

let to_odoc x =
  match String.split_on_char '/' x.mime_type, x.encoding with
  | ["image"; "svg"], Noencoding -> Printf.sprintf "{%%html: %s %%}" x.data
  | "image"::_, Base64 -> Printf.sprintf "{%%html: <img src=\"data:%s;base64,%s\" /> %%}" x.mime_type x.data
  | "text"::"odoc"::[], Noencoding -> x.data
  | _ -> ""