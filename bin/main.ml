open VerproParser.Lexer
open VerproParser.Parser

(* open VerproSyntax.Syntax *)

let input = ref None
let speclist = []
let usage_msg = "verpro <file>"
let anon_fun filename = input := Some filename

let () =
  Arg.parse speclist anon_fun usage_msg;
  match !input with
  | None -> print_string "no input file"
  | Some filename ->
      let f = open_in filename in
      print_string (">>" ^ filename);
      let lexbuf = Lexing.from_channel f in
      let _ = process read_token lexbuf in
      ()
(* print_string "\n";
   print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q)))) *)
