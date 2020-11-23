let read_file sourcefile =
  let ic = open_in_bin sourcefile in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  text

let parse_stan_file sourcefile =
  let text = read_file sourcefile in
  Parser.program (SLexer.tokens_stream name text)
