open Sparser.MenhirLibParser.Inter
open List
open C2C
open Lexing
open Sparser

exception SyntaxError of string
exception SNIY of string
exception NIY_elab of string

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

let mapo o f =
  match o with
  | None -> None
  | Some o -> Some (f o)

let rec el_e e =
  match e with
  | Stan.Econst_int i -> StanE.Econst_int (Camlcoq.Z.of_sint (int_of_string i))
  | Stan.Econst_float _ -> raise (NIY_elab "expression: float constant")
  | Stan.Evar i -> StanE.Evar (Camlcoq.intern_string i)
  | Stan.Eunop (o,e) -> StanE.Eunop (o,el_e e)
  | Stan.Ebinop (e1,o,e2) -> StanE.Ebinop (el_e e1,o,el_e e2) 
  | Stan.Ecall (i,el) -> StanE.Ecall (Camlcoq.intern_string i, List.map el_e el)
  | Stan.Econdition (e1,e2,e3) -> StanE.Econdition(el_e e1, el_e e2, el_e e3)
  | Stan.Earray el -> StanE.Earray (List.map el_e el)
  | Stan.Erow el -> StanE.Erow (List.map el_e el)
  | Stan.Eindexed (e,il) -> StanE.Eindexed (el_e e, map el_i il)
  | Stan.Edist (i,el) -> StanE.Edist (Camlcoq.intern_string i, List.map el_e el)
  | Stan.Etarget -> StanE.Etarget

and el_i i =
  match i with
  | Stan.Iall -> StanE.Iall
  | Stan.Isingle e -> StanE.Isingle (el_e e)
  | Stan.Iupfrom e -> StanE.Iupfrom (el_e e)
  | Stan.Idownfrom e -> StanE.Idownfrom (el_e e)
  | Stan.Ibetween (e1,e2) -> StanE.Ibetween (el_e e1, el_e e2)

let el_p p =
  match p with
  | Stan.Pstring s -> StanE.Pstring (Camlcoq.intern_string s)
  | Stan.Pexpr e -> StanE.Pexpr (el_e e)

let rec el_s s =
  match s with
  | Stan.Sskip -> StanE.Sskip
  | Stan.Sassign (e1,oo,e2) -> StanE.Sassign (el_e e1, oo, el_e e2)
  | Stan.Sblock sl -> List.fold_left (fun s1 s2 -> StanE.Ssequence (s1, (el_s s2))) StanE.Sskip sl
  | Stan.Sifthenelse (e,s1,s2) -> StanE.Sifthenelse (el_e e, el_s s1, el_s s2)
  | Stan.Swhile (e,s) -> StanE.Swhile (el_e e, el_s s)
  | Stan.Sfor (i,e1,e2,s) ->
    StanE.Sfor (Camlcoq.intern_string i,el_e e1, el_e e2, el_s s)
  | Stan.Sbreak -> StanE.Sbreak
  | Stan.Scontinue -> StanE.Scontinue
  | Stan.Sreturn oe -> StanE.Sreturn (mapo oe el_e)
  | Stan.Svar v -> raise (NIY_elab "statement: var")
  | Stan.Scall (i,el) -> StanE.Scall (Camlcoq.intern_string i,List.map el_e el)
  | Stan.Sprint lp -> raise (NIY_elab "statement: print")
  | Stan.Sreject lp -> raise (NIY_elab "statement: reject")
  | Stan.Sforeach (i,e,s) -> StanE.Sforeach (Camlcoq.intern_string i,el_e e, el_s s)
  | Stan.Starget e -> StanE.Starget (el_e e)
  | Stan.Stilde (e,i,el,(tr1,tr2)) ->
    StanE.Stilde (el_e e, Camlcoq.intern_string i, map el_e el, (mapo tr1 el_e,mapo tr2 el_e) )

let el_b b =
  match b with
  | Stan.Bint -> StanE.Bint
  | Stan.Breal -> StanE.Breal
  | Stan.Bvector e -> StanE.Bvector (el_e e)
  | Stan.Brow e -> StanE.Brow (el_e e)
  | Stan.Bmatrix (e1,e2) -> StanE.Bmatrix (el_e e1, el_e e2)

let elab elab_fun ol =
  match ol with
  | None -> None
  | Some l -> Some (List.map elab_fun l)

let declareVariable v =
  let id = Camlcoq.intern_string v.Stan.vd_id in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data false];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (v.Stan.vd_id,0) };
  let volatile = false in
  let readonly = false in
  let vd = {
    StanE.vd_type = el_b v.Stan.vd_type;
    StanE.vd_constraint = v.Stan.vd_constraint;
    StanE.vd_dims = List.map el_e v.Stan.vd_dims;
    StanE.vd_init = None;
    StanE.vd_global = true;
  } in
  (id,  AST.Gvar { AST.gvar_info = vd; gvar_init = [];
                   gvar_readonly = readonly; gvar_volatile = volatile})

let declareFundef name body rt params =
  let id = Camlcoq.intern_string name in
  Hashtbl.add C2C.decl_atom id {
    a_storage = C.Storage_default;
    a_alignment = None;
    a_size = None;
    a_sections = [Sections.Section_text;Sections.Section_literal;Sections.Section_jumptable];
    a_access = Sections.Access_default;
    a_inline = Noinline;
    a_loc = (name,0) };
  let body = List.fold_left (fun s1 s2 -> StanE.Ssequence (s1, (el_s s2))) StanE.Sskip body in
  let params = List.map (fun ((x,y),z) -> ((x,y),Camlcoq.intern_string z)) params in
  let fd = {
    StanE.fn_return = rt;
    StanE.fn_callconv = AST.cc_default;
    StanE.fn_params = params;
    StanE.fn_vars = [];
    StanE.fn_temps = [];
    StanE.fn_body = body} in
  (id,  AST.Gfun(Ctypes.Internal fd))

let elaborate (p: Stan.program) =
  match p with
    { Stan.pr_functions=f;
      Stan.pr_data=d;
      Stan.pr_transformed_data=td;
      Stan.pr_parameters=p;
      Stan.pr_transformed_parameters=tp;
      Stan.pr_model=m;
      Stan.pr_generated=g;
    } ->

    let get_code c =
      match c with
      | None -> [Stan.Sskip]
      | Some c -> c
    in

    let functions = [] in

    let (id_data,f_data) = declareFundef "data" [Stan.Sskip] None [] in
    let functions = (id_data,f_data) :: functions in

    let (id_tr_data,f_tr_data) = declareFundef "transformed_data" (get_code td) None [] in
    let functions = (id_tr_data,f_tr_data) :: functions in

    let (id_params,f_params) = declareFundef "parameters" [Stan.Sskip] None [] in
    let functions = (id_params,f_params) :: functions in

    let (id_tr_params,f_tr_params) = declareFundef "transformed_parameters" (get_code tp) None [] in
    let functions = (id_tr_params,f_tr_params) :: functions in

    let (id_model,f_model) = declareFundef "model" (get_code m) None [] in
    let functions = (id_model,f_model) :: functions in

    let (id_gen_quant,f_gen_quant) = declareFundef "generated_quantities" (get_code g) None [] in
    let functions = (id_gen_quant,f_gen_quant) :: functions in

    let (id_propose,f_propose) = declareFundef "propose" [Stan.Sskip] None [] in
    let functions = (id_propose,f_propose) :: functions in

    let (id_get,f_get) = declareFundef "get_state" [Stan.Sskip] None [] in
    let functions = (id_get,f_get) :: functions in

    let (id_set,f_set) = declareFundef "set_state" [Stan.Sskip] None [] in
    let functions = (id_set,f_set) :: functions in

    let unop f =
      match f with
      | None -> []
      | Some f -> f
    in

    let functions =
      List.fold_left
        (fun acc -> fun ff -> (declareFundef ff.Stan.fn_name [ff.Stan.fn_body] ff.Stan.fn_return ff.Stan.fn_params) :: acc)
        functions (unop f) in

    let variables = [] in

    let variables =
      List.fold_left
        (fun acc -> fun v -> declareVariable v :: acc)
        variables (unop d) in

    let variables =
      List.fold_left
        (fun acc -> fun v -> declareVariable v :: acc)
        variables (unop p) in    

    let gl1 = C2C.convertGlobdecls Env.empty [] (Env.initial_declarations()) in
    let _ = C2C.globals_for_strings gl1 in

    {
      StanE.pr_defs=functions @ variables;
      StanE.pr_public=List.map fst functions;
      StanE.pr_data=id_data;
      StanE.pr_transformed_data=id_tr_data;
      StanE.pr_parameters=id_params;
      StanE.pr_transformed_parameters=id_tr_params;
      StanE.pr_model=id_model;
      StanE.pr_generated=id_gen_quant;
    }    

let location t =
  match t with
  (* These four tokens have a payload we ignore *)
  | STRINGLITERAL sp | REALNUMERAL sp | INTNUMERAL sp | IDENTIFIER sp -> 
    snd sp
  (* All of the following tokens have no payload, just a position *)
  | WHILE p | VOID p | VECTOR p | UPPER p | UNITVECTOR p | TRUNCATE p 
  | TRANSPOSE p | TRANSFORMEDPARAMETERSBLOCK p | TRANSFORMEDDATABLOCK p 
  | TIMESASSIGN p | TIMES p | TILDE p | TARGET p | SIMPLEX p | SEMICOLON p 
  | RPAREN p | ROWVECTOR p | RETURN p | REJECT p | REAL p | RBRACK p 
  | RBRACE p | RABRACK p | QMARK p | PRINT p | POSITIVEORDERED p | PLUSASSIGN p 
  | PLUS p | PARAMETERSBLOCK p | ORDERED p | OR p | OFFSET p | NEQUALS p 
  | MULTIPLIER p | MODULO p | MODELBLOCK p | MINUSASSIGN p | MINUS p | MATRIX p 
  | LPAREN p | LOWER p | LEQ p | LDIVIDE p | LBRACK p | LBRACE p | LABRACK p 
  | INT p | IN p | IF_ p | IDIVIDE p | HAT p | GEQ p | GENERATEDQUANTITIESBLOCK p 
  | FUNCTIONBLOCK p | FOR p | EQUALS p | EOF p | ELTTIMESASSIGN p | ELTTIMES p 
  | ELTPOW p | ELTDIVIDEASSIGN p | ELTDIVIDE p | ELSE p | DIVIDEASSIGN p 
  | DIVIDE p | DATABLOCK p | COVMATRIX p | CORRMATRIX p | CONTINUE p | COMMA p 
  | COLON p | CHOLESKYFACTORCOV p | CHOLESKYFACTORCORR p | BREAK p | BAR p 
  | BANG p | ASSIGN p | AND p ->   
    p 

(* VERY temporary 

   This will eventually be some mapping from Sparser.state -> int
   and a call to the normal menhir messages functionality
*)

let statenum s =
  let coqstr = Sparser.Aut.int_of_state s in
  let string_state = Camlcoq.camlstring_of_coqstring coqstr
  in int_of_string string_state

(* This file was auto-generated based on "parser.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
  match s with
  | 398 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 399 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 403 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 377 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 30 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 31 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 135 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 136 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 378 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 380 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 137 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 138 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 139 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 33 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 379 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 142 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 32 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 144 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 40 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 127 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 58 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 59 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 61 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 46 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 146 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 147 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 153 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 151 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 154 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 74 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 43 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 53 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 212 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 213 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 214 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 216 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 217 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 218 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 219 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 220 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 221 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 225 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 215 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 211 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 72 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 51 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 115 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 116 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 87 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 118 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 70 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 89 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 99 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 85 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 55 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 75 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 81 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 82 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 79 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 48 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 78 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 101 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 91 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 45 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 103 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 108 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 93 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 124 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 95 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 97 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 106 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 381 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 382 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 383 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 391 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 157 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 158 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 160 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 36 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 38 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 37 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 132 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 39 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 67 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 129 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 162 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 260 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 65 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 179 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 180 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 181 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 236 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 182 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 234 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 237 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 206 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 203 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 204 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 207 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 209 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 64 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 208 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 112 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 113 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 47 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 195 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 183 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 184 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 185 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 186 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 187 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 188 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 229 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 230 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 231 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 189 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 191 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 42 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 392 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 393 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 397 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 404 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 405 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 163 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 164 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 165 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 240 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 167 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 168 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 169 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 243 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 244 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 245 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 246 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 248 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 249 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 252 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 408 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 172 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 173 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 174 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 175 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 176 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 409 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 410 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 413 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 1 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 2 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 10 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 13 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 14 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 25 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 264 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 265 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 29 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 269 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 15 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 16 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 18 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 19 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 20 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 272 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 273 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 274 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 275 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 311 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 312 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 368 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 276 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 277 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 278 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 284 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 280 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 281 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 282 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 306 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 285 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 286 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 288 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 289 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 290 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 310 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 308 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 292 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 293 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 295 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 296 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 297 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 299 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 300 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 302 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 303 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 304 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 315 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 316 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 317 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 319 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 320 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 321 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 326 | 325 | 323 ->
    "Expected \"[\" expression \"]\" for size declaration of row_vector.\n"
  | 324 ->
    "Expected identifier as part of top-level variable declaration.\n"
  | 328 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 369 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 372 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 370 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 376 ->
    "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
  | 332 | 331 | 330 ->
    "Expected \"[\" expression \"]\" for size of positive_ordered.\n"
  | 336 | 335 | 334 ->
    "Expected \"[\" expression \"]\" for size of ordered.\n"
  | 339 | 343 | 342 | 341 | 340 | 338 ->
    "Expected \"[\" expression \",\" expression \"]\" for matrix sizes as part of top-level variable declaration.\n"
  | 345 ->
    "Expected range constraint or identifier as part of top-level variable declaration.\n"
  | 346 ->
    "Expected \"lower = \" expression or \"upper = \" expression for integer bounds.\n"
  | 350 | 349 | 348 ->
    "Expected \"[\" expression \"]\" for size of cov_matrix.\n"
  | 354 | 353 | 352 ->
    "Expected \"[\" expression \"]\" for size of corr_matrix.\n"
  | 362 | 359 | 358 | 357 | 356 ->
    "Expected \"[\" expression \"]\" or \"[\" expression \",\" expression \"]\" for size of cholesky_factor_cov.\n"
  | 366 | 365 | 364 ->
    "Expected \"[\" expression \"]\" for size of cholesky_factor_corr.\n"
  | 0 ->
    "Expected \"functions {\" or \"data {\" or \"transformed data {\" or \"parameters {\" or \"transformed parameters {\" or \"model {\" or \"generated quantities {\".\n"
  | _ ->
    raise Not_found


let errmsg (s : Sparser.Aut.state) =
  let state_num = statenum s 
  in
  message state_num

(* debug code *)
let token_str = function
  | WHILE _ -> "while"
  | VOID _ -> "void"
  | VECTOR _ -> "vector"
  | UPPER _ -> "upper"
  | UNITVECTOR _ -> "unitvec"
  | TRUNCATE _ -> "trunc"
  | TRANSPOSE _ -> "trans"
  | TRANSFORMEDPARAMETERSBLOCK _ -> "tfpb"
  | TRANSFORMEDDATABLOCK _ -> "tfdb"
  | TIMESASSIGN _ -> "timeassign"
  | TIMES _ -> "times"
  | TILDE _ -> "tilde"
  | TARGET _ -> "target"
  | STRINGLITERAL _ -> "stringlit"
  | SIMPLEX _ -> "simplex"
  | SEMICOLON _ -> "semi"
  | RPAREN _ -> "rparen"
  | ROWVECTOR _ -> "rowvec"
  | RETURN _ -> "ret"
  | REJECT _ -> "rej"
  | REALNUMERAL _ -> "realn"
  | REAL _ -> "real"
  | RBRACK _ -> "rbrac"
  | RBRACE _ -> "rbrace"
  | RABRACK _ -> "rabrac"
  | QMARK _ -> "?"
  | PRINT _ -> "print"
  | POSITIVEORDERED _ -> "positiveord"
  | PLUSASSIGN _ -> "plusassign"
  | PLUS _ -> "plus"
  | PARAMETERSBLOCK _ -> "parametersblock"
  | ORDERED _ -> "ordered"
  | OR _ -> "or"
  | OFFSET _ -> "offset"
  | NEQUALS _ -> "neq"
  | MULTIPLIER _ -> "multiplier"
  | MODULO _ -> "modulo"
  | MODELBLOCK _ -> "mb"
  | MINUSASSIGN _ -> "minusassign"
  | MINUS _ -> "minus"
  | MATRIX _ -> "matrix"
  | LPAREN _ -> "lparen"
  | LOWER _ -> "lower"
  | LEQ _ -> "leq"
  | LDIVIDE _ -> "ldiv"
  | LBRACK _ -> "lbrac"
  | LBRACE _ -> "lbrace"
  | LABRACK _ -> "labrac"
  | INTNUMERAL _ -> "intn"
  | INT _ -> "int"
  | IN _ -> "in"
  | IF_ _ -> "if"
  | IDIVIDE _ -> "idiv"
  | IDENTIFIER _ -> "ident"
  | HAT _ -> "hat"
  | GEQ _ -> "geq"
  | GENERATEDQUANTITIESBLOCK _ -> "generatedquantitiesblock"
  | FUNCTIONBLOCK _ -> "functionblock"
  | FOR _ -> "for"
  | EQUALS _ -> "equals"
  | EOF _ -> "eof"
  | ELTTIMESASSIGN _ -> "elttimesassign"
  | ELTTIMES _ -> "elttimes"
  | ELTPOW _ -> "eltpow"
  | ELTDIVIDEASSIGN _ -> "eltdivass"
  | ELTDIVIDE _ -> "eltdiv"
  | ELSE _ -> "else"
  | DIVIDEASSIGN _ -> "divass"
  | DIVIDE _ -> "divide"
  | DATABLOCK _ -> "datablock"
  | COVMATRIX _ -> "covmatrix"
  | CORRMATRIX _ -> "corrmatrix"
  | CONTINUE _ -> "continue"
  | COMMA _ -> "comma"
  | COLON _ -> "colon"
  | CHOLESKYFACTORCOV _ -> "choleskycov"
  | CHOLESKYFACTORCORR _ -> "choleskycorr"
  | BREAK _ -> "break"
  | BAR _ -> "bar"
  | BANG _ -> "bang"
  | ASSIGN _ -> "ass"
  | AND _ -> "and"

let parse_stan_file sourcefile ifile =
  (*Frontend.init();*)
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;

  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  let p = match Sparser.program log_fuel (tokens_stream text) with
    | Sparser.MenhirLibParser.Inter.Fail_pr (s, tok) -> 
      let {pos_lnum; pos_cnum ; pos_bol} = location tok in
      print_endline "Syntax error:";
      Printf.printf "L%d C%d: %s\n" pos_lnum (pos_cnum - pos_bol) (errmsg s);
      print_endline (token_str tok);
      exit 0;

    | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
    | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate ast in
  print_endline "parsed"; p
