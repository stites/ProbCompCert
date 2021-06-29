open Sparser.MenhirLibParser.Inter
open List
open C2C
open Lexing
open Sparser
open Smessages

exception SNIY of string
exception NIY_elab of string

(* <><><><><><><><><><> should be moved to Sstanlib.ml <><><><><><><><><><><><> *)
let  tdouble = Stypes.Treal
let ctdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)
let  tint = Stypes.Tint
let ctint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr)
let rt = Some tdouble
let to_charlist s = List.init (String.length s) (String.get s)
let ftype = Ctypes.Tfunction (Ctypes.Tnil, (Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)), AST.cc_default)
let st_uniform_lpdf = "uniform_lpdf"
let id_uniform_lpdf = Camlcoq.intern_string st_uniform_lpdf
let ty_uniform_lpdf = Stypes.Tfunction (Stypes.Tcons (tdouble, (Stypes.Tcons (tdouble, (Stypes.Tcons (tdouble, Stypes.Tnil))))), Stypes.Treal)
let gl_uniform_lpdf = AST.Gfun
                         (Ctypes.External
                            (AST.EF_external (*external_function*)
                               (to_charlist st_uniform_lpdf, {
                                 AST.sig_args=[AST.Tfloat; AST.Tfloat; AST.Tfloat];
                                 AST.sig_res=AST.Tret AST.Tfloat;
                                 AST.sig_cc=AST.cc_default;
                               }),
                            Ctypes.Tcons (ctdouble, Ctypes.Tcons (ctdouble, (Ctypes.Tcons (ctdouble, Ctypes.Tnil)))), (* typelist for params *)
                            ctdouble, (* return type *)
                            AST.cc_default
                         ))


let st_bernoulli_lpmf = "bernoulli_lpmf"
let id_bernoulli_lpmf = Camlcoq.intern_string st_bernoulli_lpmf
let ty_bernoulli_lpmf = Stypes.Tfunction (Stypes.Tcons (tint, (Stypes.Tcons (tdouble, Stypes.Tnil))), Stypes.Treal)
let gl_bernoulli_lpmf = AST.Gfun
                         (Ctypes.External
                            (AST.EF_external (*external_function*)
                               (to_charlist st_bernoulli_lpmf, {
                                 AST.sig_args=[AST.Tint; AST.Tfloat];
                                 AST.sig_res=AST.Tret AST.Tfloat;
                                 AST.sig_cc=AST.cc_default;
                               }),
                            Ctypes.Tcons (ctint, (Ctypes.Tcons (ctdouble, Ctypes.Tnil))), (* typelist for params *)
                            ctdouble, (* return type *)
                            AST.cc_default
                         ))


let transf_dist_idents = Hashtbl.create 2;;
Hashtbl.add transf_dist_idents "uniform" (id_uniform_lpdf, ty_uniform_lpdf);
Hashtbl.add transf_dist_idents "bernoulli" (id_bernoulli_lpmf, ty_bernoulli_lpmf)
let stanlib_functions = [
    (id_uniform_lpdf,   gl_uniform_lpdf);
    (id_bernoulli_lpmf, gl_bernoulli_lpmf)
  ]


(* <><><><><><><><><> bootstrapped variable type injection <><><><><><><><><><> *)
(* let var_types = Hashtbl.create 300
 * #val my_hash : ('_weak1, '_weak2) Hashtbl.t *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)

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
  | Stan.Econst_int i -> StanE.Econst_int (Camlcoq.Z.of_sint (int_of_string i), Stypes.Tint)
  | Stan.Econst_float f -> StanE.Econst_float (Camlcoq.coqfloat_of_camlfloat (float_of_string f), Stypes.Treal)
  | Stan.Evar i -> StanE.Evar (Camlcoq.intern_string i, Stypes.Treal)
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
    let (_i, _ty) = match Hashtbl.find_opt transf_dist_idents i with
      | Some (ident, ty) -> (ident, ty)
      | None -> raise (NIY_elab ("tilde called with invalid distribution: "^ i))
    in
    StanE.Stilde (el_e e, StanE.Evar (_i, _ty), map el_e el, (mapo tr1 el_e,mapo tr2 el_e) )

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

let declareFundefWithExtras name body rt params extraVars =
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

  let blocktypeFundef = function
    | "model" -> CStan.BTModel
    | _ -> CStan.BTOther
  in

  let fd = {
    StanE.fn_return = rt;
    StanE.fn_callconv = AST.cc_default;
    StanE.fn_params = params;
    StanE.fn_blocktype = blocktypeFundef name;
    StanE.fn_vars = extraVars;
    StanE.fn_temps = [];
    StanE.fn_body = body} in
  (id,  AST.Gfun(Ctypes.Internal fd))

let declareFundef name body rt params =
  declareFundefWithExtras name body rt params []

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

    let target = (Camlcoq.intern_string "target", Stypes.Treal) in
    let (id_model,f_model) = declareFundefWithExtras "model" (get_code m) (Some Stypes.Treal) [] [target] in

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

    let data_variables = List.map declareVariable (unop d) in
    let param_variables = List.map declareVariable (unop p) in

    let gl1 = C2C.convertGlobdecls Env.empty [] (Env.initial_declarations()) in
    let _ = C2C.globals_for_strings gl1 in

    {
      StanE.pr_defs=functions @ data_variables @ param_variables @ stanlib_functions;
      StanE.pr_public=List.map fst functions @ List.map fst stanlib_functions;
      StanE.pr_data=id_data;
      StanE.pr_data_vars=List.map fst data_variables;
      StanE.pr_transformed_data=id_tr_data;
      StanE.pr_parameters=id_params;
      StanE.pr_parameters_vars=List.map fst param_variables;
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

let state_num s =
  let coq_num = Sparser.Aut.coq_N_of_state s in
  let state = Camlcoq.N.to_int coq_num
  in 
  state

let handle_syntax_error file state token =
  let (pos1, pos2) as positions = location token in
  let line = pos2.pos_lnum in
  let st_num = state_num state in
  let col_start = let {pos_cnum;pos_bol} = pos1 in 1 + pos_cnum - pos_bol in
  let col_end = let {pos_cnum;pos_bol} = pos2 in 1 + pos_cnum - pos_bol in
  let msg = try message st_num with
    | Not_found -> "Unknown error in parser state " ^ string_of_int st_num
  in
  Printf.eprintf  "Syntax error in '%s', line %d, characters %d-%d:\n%s" file line col_start col_end msg;
  exit 1

let parse_stan_file sourcefile ifile =
  (*Frontend.init();*)
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;

  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  let p = match Sparser.program log_fuel (tokens_stream text) with
    | Sparser.MenhirLibParser.Inter.Fail_pr_full (state, token) -> handle_syntax_error sourcefile state token
    | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
    | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate ast in
  p
