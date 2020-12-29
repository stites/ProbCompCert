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
  | Stan.Eunop _ -> raise (NIY_elab "expression: unop")
  | Stan.Ebinop _ -> raise (NIY_elab "expression: binop")
  | Stan.Ecall _ -> raise (NIY_elab "expression: call")
  | Stan.Econdition _ -> raise (NIY_elab "expression: condition")
  | Stan.Earray _ -> raise (NIY_elab "expression: array")
  | Stan.Erow _ -> raise (NIY_elab "expression: row")
  | Stan.Eindexed (e,il) -> StanE.Eindexed (el_e e, map el_i il)
  | Stan.Edist _ -> raise (NIY_elab "expression: dist")
  | Stan.Etarget -> raise (NIY_elab "expression: target")

and el_i i =
  match i with
  | Stan.Iall -> StanE.Iall
  | Stan.Isingle e -> StanE.Isingle (el_e e)
  | Stan.Iupfrom _ -> raise (NIY_elab "index: upfrom")
  | Stan.Idownfrom _ -> raise (NIY_elab "index: downfrom")
  | Stan.Ibetween _ -> raise (NIY_elab "index: between")
                  
let rec el_s s =
  match s with
  | Stan.Sskip -> StanE.Sskip
  | Stan.Sassign _ -> raise (NIY_elab "statement: assign") 
  | Stan.Sblock sl -> StanE.Sblock (map el_s sl)
  | Stan.Sifthenelse _ -> raise (NIY_elab "statement: ifthenelse")
  | Stan.Swhile _ -> raise (NIY_elab "statement: while")
  | Stan.Sfor (i,e1,e2,s) ->
     StanE.Sfor (Camlcoq.intern_string i,el_e e1, el_e e2, el_s s)
  | Stan.Sbreak -> raise (NIY_elab "statement: break")
  | Stan.Scontinue -> raise (NIY_elab "statement: continue")
  | Stan.Sreturn _ -> raise (NIY_elab "statement: return")
  | Stan.Svar _ -> raise (NIY_elab "statement: var")
  | Stan.Scall _ -> raise (NIY_elab "statement: call")
  | Stan.Sruntime _ -> raise (NIY_elab "statement: runtime")
  | Stan.Sforeach _ -> raise (NIY_elab "statement: foreach")
  | Stan.Starget _ -> raise (NIY_elab "statement: target")
  | Stan.Stilde (e,i,el,(tr1,tr2)) ->
     StanE.Stilde (el_e e, Camlcoq.intern_string i, map el_e el, (mapo tr1 el_e,mapo tr2 el_e) )

let el_b b =
  match b with
  | Stan.Bint -> StanE.Bint
  | Stan.Breal -> StanE.Breal
  | Stan.Bvector e -> raise (NIY_elab "basic: vector")
  | Stan.Brow e -> raise (NIY_elab "basic: row")
  | Stan.Bmatrix (e1,e2) -> raise (NIY_elab "basic: matrix")

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
      StanE.vd_read_only = readonly;
      StanE.vd_volatile = volatile;
    } in
  (id, vd)
            
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
      StanE.fn_body = body} in
  (id,fd)
            
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
    
    {
      StanE.pr_functions=functions;
      StanE.pr_variables = variables;
      StanE.pr_public=List.map fst functions;
      StanE.pr_data=id_data;
      StanE.pr_transformed_data=id_tr_data;
      StanE.pr_parameters=id_params;
      StanE.pr_transformed_parameters=id_tr_params;
      StanE.pr_model=id_model;
      StanE.pr_generated=id_gen_quant;
    }    
  
let parse_stan_file sourcefile ifile =
  Frontend.init();
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;
    
  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  match Sparser.program log_fuel (tokens_stream text) with
  | Sparser.MenhirLibParser.Inter.Fail_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate ast
      
