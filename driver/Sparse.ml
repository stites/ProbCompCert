(*
let read_file sourcefile =
  let ic = open_in_bin sourcefile in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  text

 
let parse_stan_file sourcefile =
  let text = read_file sourcefile in
  Sparser.program (Slexer.token (Lexing.from_string text))
 *)

exception Foo of string

let parse_stan_file sourcefile ifile =
  raise (Foo "Bar")


(*
    Slexer.token (Lexing.from_channel ch)
 *)
