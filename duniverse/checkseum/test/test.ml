let const x _ = x

let make ~name (module M : Checkseum.S) input expected =
  let checkseum = Alcotest.testable M.pp M.equal in
  ( name,
    `Quick,
    fun () ->
      Alcotest.check checkseum name
        M.(digest_string input 0 (String.length input) default)
        M.(of_int32 expected) )

let () =
  Alcotest.run "checkseum"
    [
      ( "adler32",
        [
          make ~name:"0" (module Checkseum.Adler32) "" 1l;
          make ~name:"1" (module Checkseum.Adler32) "\x00" 65537l;
          make ~name:"2"
            (module Checkseum.Adler32)
            "\xff\xff\xff\xff" 167379965l;
          make ~name:"3" (module Checkseum.Adler32) "123456789" 0x91E01DEl;
          make ~name:"4"
            (module Checkseum.Adler32)
            (String.concat ""
               [
                 "\x9d\x02\x9d\x02\x90\xad\x14\x72\xb9\xb4\x44\x59\x5d\x21\x05\xb7";
                 "\x34\x4f\x64\xe9\xa8\x5a\x3e\xd9\x91\x1f\x44\x91\xc1\x5c";
               ])
            0xBDE50CD1l;
        ] );
      ( "crc32c",
        [
          make ~name:"0" (module Checkseum.Crc32c) "" 0l;
          make ~name:"1" (module Checkseum.Crc32c) "\x00" 0x527d5351l;
          make ~name:"2"
            (module Checkseum.Crc32c)
            "\xff\xff\xff\xff" 0xffffffffl;
          make ~name:"3" (module Checkseum.Crc32c) "123456789" 0xe3069283l;
          make ~name:"4"
            (module Checkseum.Crc32c)
            "Thou hast made me, and shall thy work decay?" 0x866374c0l;
        ] );
      ( "crc32",
        [
          make ~name:"0" (module Checkseum.Crc32) "" 0l;
          make ~name:"1" (module Checkseum.Crc32) "\x00" 0xd202ef8dl;
          make ~name:"2" (module Checkseum.Crc32) "\xff\xff\xff\xff" 0xffffffffl;
          make ~name:"3" (module Checkseum.Crc32) "123456789" 0xcbf43926l;
          make ~name:"4"
            (module Checkseum.Crc32)
            "Thou hast made me, and shall thy work decay?" 0xf1fabe1dl;
          make ~name:"5"
            (module Checkseum.Crc32)
            (String.concat "%" (List.init 1000 (const "abcdef")))
            0xadc436fl;
        ] );
      ( "crc24",
        [
          make ~name:"0" (module Checkseum.Crc24) "" 0xb704cel;
          make ~name:"1" (module Checkseum.Crc24) "a" 0xf25713l;
          make ~name:"2" (module Checkseum.Crc24) "abc" 0xba1c7bl;
          make ~name:"3" (module Checkseum.Crc24) "message digest" 0xdbf0b6l;
        ] );
    ]
