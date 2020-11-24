open Sparser.MenhirLibParser.Inter

exception SNIY of string
   
let read_file sourcefile =
  let ic = open_in_bin sourcefile in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  text

let tokens_stream text: buffer =
  let lexbuf = Lexing.from_string text in
  let rec compute_buffer () =
    let loop t = Buf_cons (t, Lazy.from_fun compute_buffer) in
    loop (Slexer.token lexbuf)
  in
  Lazy.from_fun compute_buffer
         
let parse_stan_file sourcefile ifile =
  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  match Sparser.program log_fuel (tokens_stream text) with
  | Sparser.MenhirLibParser.Inter.Fail_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> ast
      
