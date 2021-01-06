open Sparser.MenhirLibParser.Inter
open List
open C2C
   
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
                  
let rec el_s s =
  match s with
  | Stan.Sskip -> StanE.Sskip
  | Stan.Sassign (e1,oo,e2) -> StanE.Sassign (el_e e1, oo, el_e e2)
  | Stan.Sblock sl -> StanE.Sblock (map el_s sl)
  | Stan.Sifthenelse (e,s1,s2) -> StanE.Sifthenelse (el_e e, el_s s1, el_s s2)
  | Stan.Swhile (e,s) -> StanE.Swhile (el_e e, el_s s)
  | Stan.Sfor (i,e1,e2,s) ->
     StanE.Sfor (Camlcoq.intern_string i,el_e e1, el_e e2, el_s s)
  | Stan.Sbreak -> StanE.Sbreak
  | Stan.Scontinue -> StanE.Scontinue
  | Stan.Sreturn oe -> StanE.Sreturn (mapo oe el_e)
  | Stan.Svar v -> raise (NIY_elab "statement: var")
  | Stan.Scall (i,el) -> StanE.Scall (Camlcoq.intern_string i,List.map el_e el)
  | Stan.Sruntime (s,pl) -> raise (NIY_elab "statement: runtime")
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
  let body = List.map el_s body in
  let params = List.map (fun ((x,y),z) -> ((x,y),Camlcoq.intern_string z)) params in
  let fd = {
      StanE.fn_return = rt;
      StanE.fn_callconv = AST.cc_default;
      StanE.fn_params = params;
      StanE.fn_vars = [];
      StanE.fn_temps = [];
      StanE.fn_body = StanE.Sblock body} in
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
  
let parse_stan_file sourcefile ifile =
  (*Frontend.init();*)
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;

  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  let p = match Sparser.program log_fuel (tokens_stream text) with
  | Sparser.MenhirLibParser.Inter.Fail_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate ast in
  p
      
