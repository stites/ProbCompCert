(** The lexer that will feed into the parser. An OCamllex file. *)

{
open Lexing

exception NIY_Lexer of string
   
let lexer_logging = ref false
let lexer_logger s = if !lexer_logging then print_endline s
   
(* Boilerplate for getting line numbers for errors *)
  let incr_linenum lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
                         }

  let try_get_new_lexbuf fname pos =
    let ch = open_in fname in
    Lexing.from_channel ch

exception SyntaxError of string
    
}

(* Some auxiliary definition for variables and constants *)
let string_literal = '"' [^ '"' '\r' '\n']* '"'
let identifier = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*   (* TODO: We should probably expand the alphabet *)

let integer_constant =  ['0'-'9']+ ('_' ['0'-'9']+)*

let exp_literal = ['e' 'E'] ['+' '-']? integer_constant
let real_constant1 = integer_constant '.' integer_constant? exp_literal?
let real_constant2 = '.' integer_constant exp_literal?
let real_constant3 = integer_constant exp_literal
let real_constant = real_constant1 | real_constant2 | real_constant3
let space = ' ' | '\t' | '\012'
let newline = '\r' | '\n' | '\r'*'\n'
let non_space_or_newline =  [^ ' ' '\t' '\012' '\r' '\n' ]

rule token = parse
(* White space, line numers and comments *)
  | newline                   { lexer_logger "newline" ;
                                incr_linenum lexbuf ; token lexbuf }
  | space                     { lexer_logger "space" ; token lexbuf }
  | "/*"                      { lexer_logger "multicomment" ;
                                multiline_comment lexbuf ; token lexbuf }
  | "//"                      { lexer_logger "single comment" ;
                                singleline_comment lexbuf ; token lexbuf }
  | "#include"
    ( ( space | newline)+)
    ( '"' ([^ '"' '\r' '\n']* as fname) '"'
    | '<' ([^ '>' '\r' '\n']* as fname) '>'
    | (non_space_or_newline* as fname)
    )
    { let _ = raise (NIY_Lexer "Preprocessor not implement yet") in
      lexer_logger ("include " ^ fname) ;
      let new_lexbuf =
        try_get_new_lexbuf fname lexbuf.lex_curr_p in
      token new_lexbuf
    }
  | "#"                       { lexer_logger "#comment" ;
                                singleline_comment lexbuf; token lexbuf } (* deprecated *)
(* Program blocks *)
  | "functions"               { lexer_logger "functions" ;
                                Sparser.FUNCTIONBLOCK () }
  | "data"                    { lexer_logger "data" ; Sparser.DATABLOCK () }
  | "transformed"
      ( space+ )
      "data"                  { lexer_logger "transformed data" ;
                                Sparser.TRANSFORMEDDATABLOCK () }
  | "parameters"              { lexer_logger "parameters" ;
                                Sparser.PARAMETERSBLOCK () }
  | "transformed"
      ( space+ )
      "parameters"            { lexer_logger "transformed parameters" ;
                                Sparser.TRANSFORMEDPARAMETERSBLOCK () }
  | "model"                   { lexer_logger "model" ; Sparser.MODELBLOCK () }
  | "generated"
      ( space+ )
      "quantities"    { lexer_logger "generated quantities" ;
                                Sparser.GENERATEDQUANTITIESBLOCK () }
(* Punctuation *)
  | '{'                       { lexer_logger "{" ; Sparser.LBRACE () }
  | '}'                       { lexer_logger "}" ; Sparser.RBRACE () }
  | '('                       { lexer_logger "(" ; Sparser.LPAREN () }
  | ')'                       { lexer_logger ")" ; Sparser.RPAREN () }
  | '['                       { lexer_logger "[" ; Sparser.LBRACK () }
  | ']'                       { lexer_logger "]" ; Sparser.RBRACK () }
  | '<'                       { lexer_logger "<" ; Sparser.LABRACK () }
  | '>'                       { lexer_logger ">" ; Sparser.RABRACK () }
  | ','                       { lexer_logger "," ; Sparser.COMMA () }
  | ';'                       { lexer_logger ";" ; Sparser.SEMICOLON () }
  | '|'                       { lexer_logger "|" ; Sparser.BAR () }
(* Control flow keywords *)
  | "return"                  { lexer_logger "return" ; Sparser.RETURN () }
  | "if"                      { lexer_logger "if" ; Sparser.IF_ () }
  | "else"                    { lexer_logger "else" ; Sparser.ELSE () }
  | "while"                   { lexer_logger "while" ; Sparser.WHILE () }
  | "for"                     { lexer_logger "for" ; Sparser.FOR () }
  | "in"                      { lexer_logger "in" ; Sparser.IN () }
  | "break"                   { lexer_logger "break" ; Sparser.BREAK () }
  | "continue"                { lexer_logger "continue" ; Sparser.CONTINUE () }
(* Types *)
  | "void"                    { lexer_logger "void" ; Sparser.VOID () }
  | "int"                     { lexer_logger "int" ; Sparser.INT () }
  | "real"                    { lexer_logger "real" ; Sparser.REAL () }
  | "vector"                  { lexer_logger "vector" ; Sparser.VECTOR () }
  | "row_vector"              { lexer_logger "row_vector" ; Sparser.ROWVECTOR () }
  | "matrix"                  { lexer_logger "matrix" ; Sparser.MATRIX () }
  | "ordered"                 { lexer_logger "ordered" ; Sparser.ORDERED () }
  | "positive_ordered"        { lexer_logger "positive_ordered" ;
                                Sparser.POSITIVEORDERED () }
  | "simplex"                 { lexer_logger "simplex" ; Sparser.SIMPLEX () }
  | "unit_vector"             { lexer_logger "unit_vector" ; Sparser.UNITVECTOR () }
  | "cholesky_factor_corr"    { lexer_logger "cholesky_factor_corr" ;
                                Sparser.CHOLESKYFACTORCORR () }
  | "cholesky_factor_cov"     { lexer_logger "cholesky_factor_cov" ;
                                Sparser.CHOLESKYFACTORCOV () }
  | "corr_matrix"             { lexer_logger "corr_matrix" ; Sparser.CORRMATRIX () }
  | "cov_matrix"              { lexer_logger "cov_matrix" ; Sparser.COVMATRIX () }
(* Transformation keywords *)
  | "lower"                   { lexer_logger "lower" ; Sparser.LOWER () }
  | "upper"                   { lexer_logger "upper" ; Sparser.UPPER () }
  | "offset"                  { lexer_logger "offset" ; Sparser.OFFSET () }
  | "multiplier"              { lexer_logger "multiplier" ; Sparser.MULTIPLIER () }
(* Operators *)
  | '?'                       { lexer_logger "?" ; Sparser.QMARK () }
  | ':'                       { lexer_logger ":" ; Sparser.COLON () }
  | '!'                       { lexer_logger "!" ; Sparser.BANG () }
  | '-'                       { lexer_logger "-" ; Sparser.MINUS () }
  | '+'                       { lexer_logger "+" ; Sparser.PLUS () }
  | '^'                       { lexer_logger "^" ; Sparser.HAT () }
  | '\''                      { lexer_logger "\'" ; Sparser.TRANSPOSE () }
  | '*'                       { lexer_logger "*" ; Sparser.TIMES () }
  | '/'                       { lexer_logger "/" ; Sparser.DIVIDE () }
  | '%'                       { lexer_logger "%" ; Sparser.MODULO () }
  | "%/%"                     { lexer_logger "%/%" ; Sparser.IDIVIDE () }
  | "\\"                      { lexer_logger "\\" ; Sparser.LDIVIDE () }
  | ".*"                      { lexer_logger ".*" ; Sparser.ELTTIMES () }
  | ".^"                      { lexer_logger ".^" ; Sparser.ELTPOW () }
  | "./"                      { lexer_logger "./" ; Sparser.ELTDIVIDE () }
  | "||"                      { lexer_logger "||" ; Sparser.OR () }
  | "&&"                      { lexer_logger "&&" ; Sparser.AND () }
  | "=="                      { lexer_logger "==" ; Sparser.EQUALS () }
  | "!="                      { lexer_logger "!=" ; Sparser.NEQUALS () }
  | "<="                      { lexer_logger "<=" ; Sparser.LEQ () }
  | ">="                      { lexer_logger ">=" ; Sparser.GEQ () }
  | "~"                       { lexer_logger "~" ; Sparser.TILDE () }
(* Assignments *)
  | '='                       { lexer_logger "=" ; Sparser.ASSIGN () }
  | "+="                      { lexer_logger "+=" ; Sparser.PLUSASSIGN () }
  | "-="                      { lexer_logger "-=" ; Sparser.MINUSASSIGN () }
  | "*="                      { lexer_logger "*=" ; Sparser.TIMESASSIGN () }
  | "/="                      { lexer_logger "/=" ; Sparser.DIVIDEASSIGN () }
  | ".*="                     { lexer_logger ".*=" ; Sparser.ELTTIMESASSIGN () }
  | "./="                     { lexer_logger "./=" ; Sparser.ELTDIVIDEASSIGN () }
  | "<-"                      { lexer_logger "<-" ;
                                Sparser.ARROWASSIGN () } (* deprecated *)
  | "increment_log_prob"      { lexer_logger "increment_log_prob" ;
                                Sparser.INCREMENTLOGPROB () } (* deprecated *)
(* Effects *)
  | "print"                   { lexer_logger "print" ; Sparser.PRINT () }
  | "reject"                  { lexer_logger "reject" ; Sparser.REJECT () }
  | 'T'                       { lexer_logger "T" ; Sparser.TRUNCATE () } (* TODO: this is a hack; we should change to something like truncate and make it a reserved keyword *)
(* Constants and identifiers *)
  | integer_constant as i     { lexer_logger ("int_constant " ^ i) ;
                                Sparser.INTNUMERAL (lexeme lexbuf) }
  | real_constant as r        { lexer_logger ("real_constant " ^ r) ;
                                Sparser.REALNUMERAL (lexeme lexbuf) }
  | "target"                  { lexer_logger "target" ; Sparser.TARGET () } (* NB: the stanc2 parser allows variables to be named target. I think it's a bad idea and have disallowed it. *)
  | "get_lp"                  { lexer_logger "get_lp" ;
                                Sparser.GETLP () } (* deprecated *)
  | string_literal as s       { lexer_logger ("string_literal " ^ s) ;
                                Sparser.STRINGLITERAL (lexeme lexbuf) }
  | identifier as id          { lexer_logger ("identifier " ^ id) ;
                                Sparser.IDENTIFIER (lexeme lexbuf) }
(* End of file *)
  | eof                       { lexer_logger "eof" ; Sparser.EOF () }

  | _                         { raise (SyntaxError "Unidentified pattern") }

(* Multi-line comment terminated by "*/" *)
and multiline_comment = parse
  | "*/"   { () }
  | eof    { failwith "unterminated comment" }
  | '\n'   { incr_linenum lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }

(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | newline   { incr_linenum lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }

{
}
