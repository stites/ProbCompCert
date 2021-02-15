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
                                Sparser.FUNCTIONBLOCK lexbuf.lex_curr_p  }
  | "data"                    { lexer_logger "data" ; Sparser.DATABLOCK lexbuf.lex_curr_p  }
  | "transformed"
      ( space+ )
      "data"                  { lexer_logger "transformed data" ;
                                Sparser.TRANSFORMEDDATABLOCK lexbuf.lex_curr_p  }
  | "parameters"              { lexer_logger "parameters" ;
                                Sparser.PARAMETERSBLOCK lexbuf.lex_curr_p  }
  | "transformed"
      ( space+ )
      "parameters"            { lexer_logger "transformed parameters" ;
                                Sparser.TRANSFORMEDPARAMETERSBLOCK lexbuf.lex_curr_p  }
  | "model"                   { lexer_logger "model" ; Sparser.MODELBLOCK lexbuf.lex_curr_p  }
  | "generated"
      ( space+ )
      "quantities"    { lexer_logger "generated quantities" ;
                                Sparser.GENERATEDQUANTITIESBLOCK lexbuf.lex_curr_p  }
(* Punctuation *)
  | '{'                       { lexer_logger "{" ; Sparser.LBRACE lexbuf.lex_curr_p  }
  | '}'                       { lexer_logger "}" ; Sparser.RBRACE lexbuf.lex_curr_p  }
  | '('                       { lexer_logger "(" ; Sparser.LPAREN lexbuf.lex_curr_p  }
  | ')'                       { lexer_logger ")" ; Sparser.RPAREN lexbuf.lex_curr_p  }
  | '['                       { lexer_logger "[" ; Sparser.LBRACK lexbuf.lex_curr_p  }
  | ']'                       { lexer_logger "]" ; Sparser.RBRACK lexbuf.lex_curr_p  }
  | '<'                       { lexer_logger "<" ; Sparser.LABRACK lexbuf.lex_curr_p  }
  | '>'                       { lexer_logger ">" ; Sparser.RABRACK lexbuf.lex_curr_p  }
  | ','                       { lexer_logger "," ; Sparser.COMMA lexbuf.lex_curr_p  }
  | ';'                       { lexer_logger ";" ; Sparser.SEMICOLON lexbuf.lex_curr_p  }
  | '|'                       { lexer_logger "|" ; Sparser.BAR lexbuf.lex_curr_p  }
(* Control flow keywords *)
  | "return"                  { lexer_logger "return" ; Sparser.RETURN lexbuf.lex_curr_p  }
  | "if"                      { lexer_logger "if" ; Sparser.IF_ lexbuf.lex_curr_p  }
  | "else"                    { lexer_logger "else" ; Sparser.ELSE lexbuf.lex_curr_p  }
  | "while"                   { lexer_logger "while" ; Sparser.WHILE lexbuf.lex_curr_p }
  | "for"                     { lexer_logger "for" ; Sparser.FOR lexbuf.lex_curr_p  }
  | "in"                      { lexer_logger "in" ; Sparser.IN lexbuf.lex_curr_p  }
  | "break"                   { lexer_logger "break" ; Sparser.BREAK lexbuf.lex_curr_p  }
  | "continue"                { lexer_logger "continue" ; Sparser.CONTINUE lexbuf.lex_curr_p  }
(* Types *)
  | "void"                    { lexer_logger "void" ; Sparser.VOID lexbuf.lex_curr_p  }
  | "int"                     { lexer_logger "int" ; Sparser.INT lexbuf.lex_curr_p  }
  | "real"                    { lexer_logger "real" ; Sparser.REAL lexbuf.lex_curr_p  }
  | "vector"                  { lexer_logger "vector" ; Sparser.VECTOR lexbuf.lex_curr_p  }
  | "row_vector"              { lexer_logger "row_vector" ; Sparser.ROWVECTOR lexbuf.lex_curr_p  }
  | "matrix"                  { lexer_logger "matrix" ; Sparser.MATRIX lexbuf.lex_curr_p  }
  | "ordered"                 { lexer_logger "ordered" ; Sparser.ORDERED lexbuf.lex_curr_p  }
  | "positive_ordered"        { lexer_logger "positive_ordered" ;
                                Sparser.POSITIVEORDERED lexbuf.lex_curr_p  }
  | "simplex"                 { lexer_logger "simplex" ; Sparser.SIMPLEX lexbuf.lex_curr_p  }
  | "unit_vector"             { lexer_logger "unit_vector" ; Sparser.UNITVECTOR lexbuf.lex_curr_p  }
  | "cholesky_factor_corr"    { lexer_logger "cholesky_factor_corr" ;
                                Sparser.CHOLESKYFACTORCORR lexbuf.lex_curr_p  }
  | "cholesky_factor_cov"     { lexer_logger "cholesky_factor_cov" ;
                                Sparser.CHOLESKYFACTORCOV lexbuf.lex_curr_p  }
  | "corr_matrix"             { lexer_logger "corr_matrix" ; Sparser.CORRMATRIX lexbuf.lex_curr_p  }
  | "cov_matrix"              { lexer_logger "cov_matrix" ; Sparser.COVMATRIX lexbuf.lex_curr_p  }
(* Transformation keywords *)
  | "lower"                   { lexer_logger "lower" ; Sparser.LOWER lexbuf.lex_curr_p  }
  | "upper"                   { lexer_logger "upper" ; Sparser.UPPER lexbuf.lex_curr_p  }
  | "offset"                  { lexer_logger "offset" ; Sparser.OFFSET lexbuf.lex_curr_p  }
  | "multiplier"              { lexer_logger "multiplier" ; Sparser.MULTIPLIER lexbuf.lex_curr_p  }
(* Operators *)
  | '?'                       { lexer_logger "?" ; Sparser.QMARK lexbuf.lex_curr_p  }
  | ':'                       { lexer_logger ":" ; Sparser.COLON lexbuf.lex_curr_p  }
  | '!'                       { lexer_logger "!" ; Sparser.BANG lexbuf.lex_curr_p  }
  | '-'                       { lexer_logger "-" ; Sparser.MINUS lexbuf.lex_curr_p  }
  | '+'                       { lexer_logger "+" ; Sparser.PLUS lexbuf.lex_curr_p  }
  | '^'                       { lexer_logger "^" ; Sparser.HAT lexbuf.lex_curr_p  }
  | '\''                      { lexer_logger "\'" ; Sparser.TRANSPOSE lexbuf.lex_curr_p  }
  | '*'                       { lexer_logger "*" ; Sparser.TIMES lexbuf.lex_curr_p  }
  | '/'                       { lexer_logger "/" ; Sparser.DIVIDE lexbuf.lex_curr_p  }
  | '%'                       { lexer_logger "%" ; Sparser.MODULO lexbuf.lex_curr_p  }
  | "%/%"                     { lexer_logger "%/%" ; Sparser.IDIVIDE lexbuf.lex_curr_p  }
  | "\\"                      { lexer_logger "\\" ; Sparser.LDIVIDE lexbuf.lex_curr_p  }
  | ".*"                      { lexer_logger ".*" ; Sparser.ELTTIMES lexbuf.lex_curr_p  }
  | ".^"                      { lexer_logger ".^" ; Sparser.ELTPOW lexbuf.lex_curr_p  }
  | "./"                      { lexer_logger "./" ; Sparser.ELTDIVIDE lexbuf.lex_curr_p  }
  | "||"                      { lexer_logger "||" ; Sparser.OR lexbuf.lex_curr_p  }
  | "&&"                      { lexer_logger "&&" ; Sparser.AND lexbuf.lex_curr_p  }
  | "=="                      { lexer_logger "==" ; Sparser.EQUALS lexbuf.lex_curr_p  }
  | "!="                      { lexer_logger "!=" ; Sparser.NEQUALS lexbuf.lex_curr_p  }
  | "<="                      { lexer_logger "<=" ; Sparser.LEQ lexbuf.lex_curr_p  }
  | ">="                      { lexer_logger ">=" ; Sparser.GEQ lexbuf.lex_curr_p  }
  | "~"                       { lexer_logger "~" ; Sparser.TILDE lexbuf.lex_curr_p  }
(* Assignments *)
  | '='                       { lexer_logger "=" ; Sparser.ASSIGN lexbuf.lex_curr_p  }
  | "+="                      { lexer_logger "+=" ; Sparser.PLUSASSIGN lexbuf.lex_curr_p  }
  | "-="                      { lexer_logger "-=" ; Sparser.MINUSASSIGN lexbuf.lex_curr_p  }
  | "*="                      { lexer_logger "*=" ; Sparser.TIMESASSIGN lexbuf.lex_curr_p  }
  | "/="                      { lexer_logger "/=" ; Sparser.DIVIDEASSIGN lexbuf.lex_curr_p  }
  | ".*="                     { lexer_logger ".*=" ; Sparser.ELTTIMESASSIGN lexbuf.lex_curr_p  }
  | "./="                     { lexer_logger "./=" ; Sparser.ELTDIVIDEASSIGN lexbuf.lex_curr_p  }
(* Effects *)
  | "print"                   { lexer_logger "print" ; Sparser.PRINT lexbuf.lex_curr_p  }
  | "reject"                  { lexer_logger "reject" ; Sparser.REJECT lexbuf.lex_curr_p  }
  | 'T'                       { lexer_logger "T" ; Sparser.TRUNCATE lexbuf.lex_curr_p  } (* TODO: this is a hack; we should change to something like truncate and make it a reserved keyword *)
(* Constants and identifiers *)
  | integer_constant as i     { lexer_logger ("int_constant " ^ i) ;
                                Sparser.INTNUMERAL ((lexeme lexbuf), lexbuf.lex_curr_p)}
  | real_constant as r        { lexer_logger ("real_constant " ^ r) ;
                                Sparser.REALNUMERAL ((lexeme lexbuf), lexbuf.lex_curr_p) }
  | "target"                  { lexer_logger "target" ; Sparser.TARGET lexbuf.lex_curr_p  } (* NB: the stanc2 parser allows variables to be named target. I think it's a bad idea and have disallowed it. *)
  | string_literal as s       { lexer_logger ("string_literal " ^ s) ;
                                Sparser.STRINGLITERAL ((lexeme lexbuf), lexbuf.lex_curr_p ) }
  | identifier as id          { lexer_logger ("identifier " ^ id) ;
                                Sparser.IDENTIFIER ((lexeme lexbuf), lexbuf.lex_curr_p )}
(* End of file *)
  | eof                       { lexer_logger "eof" ; Sparser.EOF lexbuf.lex_curr_p }

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
