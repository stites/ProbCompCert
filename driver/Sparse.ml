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
  | Stan.Sskip -> raise (NIY_elab "statement: skip")
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
    
let elaborate_function f = raise (NIY_elab "function")
                         
let elaborate_variable v =
  match v with
    { Stan.vd_id=id;
      Stan.vd_type=t;
      Stan.vd_constraint=c;
      Stan.vd_dims=d;
      Stan.vd_init=i;
      Stan.vd_global=g
    } ->
    { StanE.vd_id=Camlcoq.intern_string id;
      StanE.vd_type=el_b t;
      StanE.vd_constraint=c;
      StanE.vd_dims=map el_e d;
      StanE.vd_init=mapo i el_e;
      StanE.vd_global=g
    }

let elab elab_fun ol =
  match ol with
  | None -> None
  | Some l -> Some (List.map elab_fun l)

let declareFundef name body =
  let id = Camlcoq.intern_string name in
  Hashtbl.add C2C.decl_atom id {
      a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_text;Sections.Section_literal;Sections.Section_jumptable];
      a_access = Sections.Access_default;
      a_inline = Noinline;
      a_loc = ("dummy",0) };
  let body = List.map el_s body in
  let fd =  {
      StanE.fn_return = None;
      StanE.fn_callconv = AST.cc_default;
      StanE.fn_params = [];
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

    let (id_data,f_data) = declareFundef "transformed_data" [Stan.Sskip] in

    {
      StanE.pr_functions=[(id_data,f_data)];
      StanE.pr_variables = [];
      StanE.pr_data=Some id_data;
      StanE.pr_transformed_data=None;
      StanE.pr_parameters=None;
      StanE.pr_transformed_parameters=None;
      StanE.pr_model=None;
      StanE.pr_generated=None;
    }    
    
    (* {
     *   StanE.pr_functions=elab elaborate_function f;
     *   StanE.pr_data=elab elaborate_variable d;
     *   StanE.pr_transformed_data=elab el_s td;
     *   StanE.pr_parameters=elab elaborate_variable p;
     *   StanE.pr_transformed_parameters=elab el_s tp;
     *   StanE.pr_model=elab el_s m;
     *   StanE.pr_generated=elab el_s g;
     * } *)
  
      
  
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
      
