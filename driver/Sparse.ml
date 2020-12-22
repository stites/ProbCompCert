open Sparser.MenhirLibParser.Inter

exception SNIY of string
exception NIY_elab of string

let elaborate p = raise (NIY_elab "TODO")
                
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
  Frontend.init();
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;
  
  C2C.decl_stan_function "logdensity";
  C2C.decl_stan_function "get_parameters_size";
  C2C.decl_stan_function "log";

  let _ = Camlcoq.intern_string "data" in
  let _ = Camlcoq.intern_string "d_size" in
  
  (* C2C.convertGlobvar ("dummy",0) Env.empty (C.Storage_extern,(Camlcoq.intern_string "data"),0,None); *)
  
  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  match Sparser.program log_fuel (tokens_stream text) with
  | Sparser.MenhirLibParser.Inter.Fail_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate ast
      
