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

  let get_position lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)

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
        try_get_new_lexbuf fname (get_position lexbuf) in
      token new_lexbuf
    }
  | "#"                       { lexer_logger "#comment" ;
                                singleline_comment lexbuf; token lexbuf } (* deprecated *)
(* Program blocks *)
  | "functions"               { lexer_logger "functions" ;
                                Sparser.FUNCTIONBLOCK (get_position lexbuf)  }
  | "data"                    { lexer_logger "data" ; Sparser.DATABLOCK (get_position lexbuf)  }
  | "transformed"
      ( space+ )
      "data"                  { lexer_logger "transformed data" ;
                                Sparser.TRANSFORMEDDATABLOCK (get_position lexbuf)  }
  | "parameters"              { lexer_logger "parameters" ;
                                Sparser.PARAMETERSBLOCK (get_position lexbuf)  }
  | "transformed"
      ( space+ )
      "parameters"            { lexer_logger "transformed parameters" ;
                                Sparser.TRANSFORMEDPARAMETERSBLOCK (get_position lexbuf)  }
  | "model"                   { lexer_logger "model" ; Sparser.MODELBLOCK (get_position lexbuf)  }
  | "generated"
      ( space+ )
      "quantities"    { lexer_logger "generated quantities" ;
                                Sparser.GENERATEDQUANTITIESBLOCK (get_position lexbuf)  }
(* Punctuation *)
  | '{'                       { lexer_logger "{" ; Sparser.LBRACE (get_position lexbuf)  }
  | '}'                       { lexer_logger "}" ; Sparser.RBRACE (get_position lexbuf)  }
  | '('                       { lexer_logger "(" ; Sparser.LPAREN (get_position lexbuf)  }
  | ')'                       { lexer_logger ")" ; Sparser.RPAREN (get_position lexbuf)  }
  | '['                       { lexer_logger "[" ; Sparser.LBRACK (get_position lexbuf)  }
  | ']'                       { lexer_logger "]" ; Sparser.RBRACK (get_position lexbuf)  }
  | '<'                       { lexer_logger "<" ; Sparser.LABRACK (get_position lexbuf)  }
  | '>'                       { lexer_logger ">" ; Sparser.RABRACK (get_position lexbuf)  }
  | ','                       { lexer_logger "," ; Sparser.COMMA (get_position lexbuf)  }
  | ';'                       { lexer_logger ";" ; Sparser.SEMICOLON (get_position lexbuf)  }
  | '|'                       { lexer_logger "|" ; Sparser.BAR (get_position lexbuf)  }
(* Control flow keywords *)
  | "return"                  { lexer_logger "return" ; Sparser.RETURN (get_position lexbuf)  }
  | "if"                      { lexer_logger "if" ; Sparser.IF_ (get_position lexbuf)  }
  | "else"                    { lexer_logger "else" ; Sparser.ELSE (get_position lexbuf)  }
  | "while"                   { lexer_logger "while" ; Sparser.WHILE (get_position lexbuf) }
  | "for"                     { lexer_logger "for" ; Sparser.FOR (get_position lexbuf)  }
  | "in"                      { lexer_logger "in" ; Sparser.IN (get_position lexbuf)  }
  | "break"                   { lexer_logger "break" ; Sparser.BREAK (get_position lexbuf)  }
  | "continue"                { lexer_logger "continue" ; Sparser.CONTINUE (get_position lexbuf)  }
(* Types *)
  | "void"                    { lexer_logger "void" ; Sparser.VOID (get_position lexbuf)  }
  | "int"                     { lexer_logger "int" ; Sparser.INT (get_position lexbuf)  }
  | "real"                    { lexer_logger "real" ; Sparser.REAL (get_position lexbuf)  }
  | "vector"                  { lexer_logger "vector" ; Sparser.VECTOR (get_position lexbuf)  }
  | "row_vector"              { lexer_logger "row_vector" ; Sparser.ROWVECTOR (get_position lexbuf)  }
  | "matrix"                  { lexer_logger "matrix" ; Sparser.MATRIX (get_position lexbuf)  }
  | "ordered"                 { lexer_logger "ordered" ; Sparser.ORDERED (get_position lexbuf)  }
  | "positive_ordered"        { lexer_logger "positive_ordered" ;
                                Sparser.POSITIVEORDERED (get_position lexbuf)  }
  | "simplex"                 { lexer_logger "simplex" ; Sparser.SIMPLEX (get_position lexbuf)  }
  | "unit_vector"             { lexer_logger "unit_vector" ; Sparser.UNITVECTOR (get_position lexbuf)  }
  | "cholesky_factor_corr"    { lexer_logger "cholesky_factor_corr" ;
                                Sparser.CHOLESKYFACTORCORR (get_position lexbuf)  }
  | "cholesky_factor_cov"     { lexer_logger "cholesky_factor_cov" ;
                                Sparser.CHOLESKYFACTORCOV (get_position lexbuf)  }
  | "corr_matrix"             { lexer_logger "corr_matrix" ; Sparser.CORRMATRIX (get_position lexbuf)  }
  | "cov_matrix"              { lexer_logger "cov_matrix" ; Sparser.COVMATRIX (get_position lexbuf)  }
(* Transformation keywords *)
  | "lower"                   { lexer_logger "lower" ; Sparser.LOWER (get_position lexbuf)  }
  | "upper"                   { lexer_logger "upper" ; Sparser.UPPER (get_position lexbuf)  }
  | "offset"                  { lexer_logger "offset" ; Sparser.OFFSET (get_position lexbuf)  }
  | "multiplier"              { lexer_logger "multiplier" ; Sparser.MULTIPLIER (get_position lexbuf)  }
(* Operators *)
  | '?'                       { lexer_logger "?" ; Sparser.QMARK (get_position lexbuf)  }
  | ':'                       { lexer_logger ":" ; Sparser.COLON (get_position lexbuf)  }
  | '!'                       { lexer_logger "!" ; Sparser.BANG (get_position lexbuf)  }
  | '-'                       { lexer_logger "-" ; Sparser.MINUS (get_position lexbuf)  }
  | '+'                       { lexer_logger "+" ; Sparser.PLUS (get_position lexbuf)  }
  | '^'                       { lexer_logger "^" ; Sparser.HAT (get_position lexbuf)  }
  | '\''                      { lexer_logger "\'" ; Sparser.TRANSPOSE (get_position lexbuf)  }
  | '*'                       { lexer_logger "*" ; Sparser.TIMES (get_position lexbuf)  }
  | '/'                       { lexer_logger "/" ; Sparser.DIVIDE (get_position lexbuf)  }
  | '%'                       { lexer_logger "%" ; Sparser.MODULO (get_position lexbuf)  }
  | "%/%"                     { lexer_logger "%/%" ; Sparser.IDIVIDE (get_position lexbuf)  }
  | "\\"                      { lexer_logger "\\" ; Sparser.LDIVIDE (get_position lexbuf)  }
  | ".*"                      { lexer_logger ".*" ; Sparser.ELTTIMES (get_position lexbuf)  }
  | ".^"                      { lexer_logger ".^" ; Sparser.ELTPOW (get_position lexbuf)  }
  | "./"                      { lexer_logger "./" ; Sparser.ELTDIVIDE (get_position lexbuf)  }
  | "||"                      { lexer_logger "||" ; Sparser.OR (get_position lexbuf)  }
  | "&&"                      { lexer_logger "&&" ; Sparser.AND (get_position lexbuf)  }
  | "=="                      { lexer_logger "==" ; Sparser.EQUALS (get_position lexbuf)  }
  | "!="                      { lexer_logger "!=" ; Sparser.NEQUALS (get_position lexbuf)  }
  | "<="                      { lexer_logger "<=" ; Sparser.LEQ (get_position lexbuf)  }
  | ">="                      { lexer_logger ">=" ; Sparser.GEQ (get_position lexbuf)  }
  | "~"                       { lexer_logger "~" ; Sparser.TILDE (get_position lexbuf)  }
(* Assignments *)
  | '='                       { lexer_logger "=" ; Sparser.ASSIGN (get_position lexbuf)  }
  | "+="                      { lexer_logger "+=" ; Sparser.PLUSASSIGN (get_position lexbuf)  }
  | "-="                      { lexer_logger "-=" ; Sparser.MINUSASSIGN (get_position lexbuf)  }
  | "*="                      { lexer_logger "*=" ; Sparser.TIMESASSIGN (get_position lexbuf)  }
  | "/="                      { lexer_logger "/=" ; Sparser.DIVIDEASSIGN (get_position lexbuf)  }
  | ".*="                     { lexer_logger ".*=" ; Sparser.ELTTIMESASSIGN (get_position lexbuf)  }
  | "./="                     { lexer_logger "./=" ; Sparser.ELTDIVIDEASSIGN (get_position lexbuf)  }
(* Effects *)
  | "print"                   { lexer_logger "print" ; Sparser.PRINT (get_position lexbuf)  }
  | "reject"                  { lexer_logger "reject" ; Sparser.REJECT (get_position lexbuf)  }
  | 'T'                       { lexer_logger "T" ; Sparser.TRUNCATE (get_position lexbuf)  } (* TODO: this is a hack; we should change to something like truncate and make it a reserved keyword *)
(* Constants and identifiers *)
  | integer_constant as i     { lexer_logger ("int_constant " ^ i) ;
                                Sparser.INTNUMERAL ((lexeme lexbuf), (get_position lexbuf))}
  | real_constant as r        { lexer_logger ("real_constant " ^ r) ;
                                Sparser.REALNUMERAL ((lexeme lexbuf), (get_position lexbuf)) }
  | "target"                  { lexer_logger "target" ; Sparser.TARGET (get_position lexbuf)  } (* NB: the stanc2 parser allows variables to be named target. I think it's a bad idea and have disallowed it. *)
  | string_literal as s       { lexer_logger ("string_literal " ^ s) ;
                                Sparser.STRINGLITERAL ((lexeme lexbuf), (get_position lexbuf) ) }
  | identifier as id          { lexer_logger ("identifier " ^ id) ;
                                Sparser.IDENTIFIER ((lexeme lexbuf), (get_position lexbuf) )}
(* End of file *)
  | eof                       { lexer_logger "eof" ; Sparser.EOF (get_position lexbuf) }

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
