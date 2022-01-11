open Sparser.MenhirLibParser.Inter
open List
open C2C
open Lexing
open Sparser
open Smessages
open Int32


exception SNIY of string
exception NIY_elab of string

(* <><><><><><><><><><> should be moved to Sstanlib.ml <><><><><><><><><><><><> *)

let sizeof_basic t =
  begin match t with
  | StanE.Bint -> 4l
  | StanE.Breal -> 8l
  | StanE.Bvector n -> Int32.mul 8l  (Camlcoq.camlint_of_coqint n)
  | StanE.Brow n -> Int32.mul 8l  (Camlcoq.camlint_of_coqint n)
  | StanE.Bmatrix (r, c) -> Int32.mul 8l  (Int32.mul (Camlcoq.camlint_of_coqint r) (Camlcoq.camlint_of_coqint c))
  | _ -> raise (Invalid_argument "Sparse does not calculate the size of this type")
  end

let sizeof_struct vars =
  List.fold_left (fun total var -> Int32.add total (sizeof_basic (snd var))) 0l vars

let init_int = AST.Init_space (Camlcoq.coqint_of_camlint 4l)
let init_dbl = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_ptr = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_struct members = AST.Init_space (Camlcoq.coqint_of_camlint (sizeof_struct members))

let ctarray (t, sz) = Ctypes.Tarray (t, sz, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tdouble = Stypes.Treal
let bdouble = StanE.Breal
let ctdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tint = Stypes.Tint
let bint = StanE.Bint
let ctint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let rt = Some tdouble
let to_charlist s = List.init (String.length s) (String.get s)
let ftype = Ctypes.Tfunction (Ctypes.Tnil, (Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)), AST.cc_default)

let ast_to_ctype x =
  match x with
  | AST.Tfloat -> ctdouble
  | AST.Tint -> ctint
  | _ -> raise (NIY_elab "impossible")

let mk_ctypelist xs =
  List.fold_left (fun tail h -> Ctypes.Tcons (h, tail)) Ctypes.Tnil xs

let mk_ctypelist_from_astlist xs =
    mk_ctypelist (List.rev (List.map ast_to_ctype xs))

let mk_cfunc xs = Ctypes.Tfunction (mk_ctypelist_from_astlist xs, ctdouble, AST.cc_default)

let mk_global_func ret str ast_args_list =
    AST.Gfun (Ctypes.External
       (AST.EF_external
          (to_charlist str, {
            AST.sig_args=ast_args_list;
            AST.sig_res=ret;
            AST.sig_cc=AST.cc_default;
          }),
       mk_ctypelist_from_astlist ast_args_list,
       ctdouble,
       AST.cc_default
    ))

let mk_global_math_func = mk_global_func (AST.Tret AST.Tfloat)

let st_uniform_lpdf = "uniform_lpdf"
let id_uniform_lpdf = Camlcoq.intern_string st_uniform_lpdf
let ty_uniform_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), Some bdouble)
let gl_uniform_lpdf = mk_global_math_func st_uniform_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]

let st_normal_lpdf = "normal_lpdf"
let id_normal_lpdf = Camlcoq.intern_string st_normal_lpdf
let ty_normal_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), Some bdouble)
let gl_normal_lpdf = mk_global_math_func st_normal_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]                    

let st_bernoulli_lpmf = "bernoulli_lpmf"
let id_bernoulli_lpmf = Camlcoq.intern_string st_bernoulli_lpmf
let ty_bernoulli_lpmf = StanE.Bfunction (StanE.Bcons (bint, (StanE.Bcons (bdouble, StanE.Bnil))), Some StanE.Breal)
let gl_bernoulli_lpmf = mk_global_math_func st_bernoulli_lpmf [AST.Tint; AST.Tfloat]

let transf_dist_idents = Hashtbl.create 3;;
Hashtbl.add transf_dist_idents "uniform" (id_uniform_lpdf, ty_uniform_lpdf);
Hashtbl.add transf_dist_idents "bernoulli" (id_bernoulli_lpmf, ty_bernoulli_lpmf);
Hashtbl.add transf_dist_idents "normal" (id_normal_lpdf, ty_normal_lpdf)
let stanlib_functions = [
    (id_uniform_lpdf,   gl_uniform_lpdf);
    (id_bernoulli_lpmf, gl_bernoulli_lpmf);
    (id_normal_lpdf, gl_normal_lpdf)
  ]
let pr_dist_functions = [(CStan.DBernPMF, id_bernoulli_lpmf);(CStan.DUnifPDF, id_uniform_lpdf)]

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                              math functions                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let mk_fn ret args s = (s, Camlcoq.intern_string s, mk_global_func ret s args, mk_cfunc args)
let mk_math_fn = mk_fn (AST.Tret AST.Tfloat)
let mk_unary_math_fn t = mk_math_fn [t]
let unary_math_fn = mk_unary_math_fn AST.Tfloat

let (st_log, id_log, gl_log, clog)       = unary_math_fn "log"
let (st_exp, id_exp, gl_exp, cexp)       = unary_math_fn "exp"
let (st_logit, id_logit, gl_logit, clogit) = unary_math_fn "logit"
let (st_expit, id_expit, gl_expit, cexpit) = unary_math_fn "expit"

let st_init_unconstrained = "init_unconstrained"
let id_init_unconstrained = Camlcoq.intern_string st_init_unconstrained
let ty_init_unconstrained = StanE.Bfunction (StanE.Bnil, Some bdouble)
let gl_init_unconstrained = mk_global_math_func st_init_unconstrained []

(* (\* temporary printing support *\) *)
(* let (st_print_double, id_print_double, gl_print_double, cprint_double) = mk_fn AST.Tvoid [AST.Tfloat] "print_double" *)
(* let (st_print_int, id_print_int, gl_print_int, cprint_int) = mk_fn AST.Tvoid [AST.Tint] "print_int" *)
(* (\* let (st_print_array_int, id_print_array_int, gl_print_array_int, cprint_array_int) = mk_fn AST.Tvoid [AST.Tint; AST.Tany64] "print_array_int" *\) *)
(* let (st_print_start, id_print_start, gl_print_start, cprint_start) = mk_fn AST.Tvoid [] "print_start" *)
(* let (st_print_end, id_print_end, gl_print_end, cprint_end) = mk_fn AST.Tvoid [] "print_end" *)

let __math_functions = [ (CStan.MFLog, id_log, gl_log, clog);
                         (CStan.MFLogit, id_logit, gl_logit, clogit);
                         (CStan.MFExp, id_exp, gl_exp, cexp);
                         (CStan.MFExpit, id_expit, gl_expit, cexpit);
                         (CStan.MFInitUnconstrained, id_init_unconstrained, gl_init_unconstrained, mk_cfunc []);

                         (* (CStan.MFPrintStart, id_print_start, gl_print_start, cprint_start); *)
                         (* (CStan.MFPrintDouble, id_print_double, gl_print_double, cprint_double); *)
                         (* (CStan.MFPrintInt, id_print_int, gl_print_int, cprint_int); *)
                         (* (\* (CStan.MFPrintArrayInt, id_print_array_int, gl_print_array_int, cprint_array_int); *\) *)
                         (* (CStan.MFPrintEnd, id_print_end, gl_print_end, cprint_end); *)
                        ]

let _as_prog_math_functions (e, i, g, c) = ((e, i), c)
let _as_global_math_functions (e, i, g, c) = (i, g)

let pr_math_functions = List.map _as_prog_math_functions __math_functions
let all_math_fns = List.map _as_global_math_functions __math_functions

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                               Struct work                                    *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let mkGlobalStruct i members = AST.Gvar {
  AST.gvar_readonly = false;
  AST.gvar_volatile = false;
  AST.gvar_init = [init_struct members];
  AST.gvar_info = {
    StanE.vd_type = StanE.Bstruct i;
    StanE.vd_constraint = StanE.Cidentity;
    StanE.vd_dims = [];
    StanE.vd_init = None;
    StanE.vd_global = true;
  };
}

let declareStruct s members =
  let id = Camlcoq.intern_string s in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (s,0) };
  (id, mkGlobalStruct id members)

let declareGlobalStruct s =
  let id = Camlcoq.intern_string s in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (s,0) };
  id

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                               Global Arrays                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let replicate n ls =
    let rec f l = function
        | 0 -> l
        | n -> f (List.rev_append ls l) (n-1) in
    List.rev (f [] n)

let mk_global_array ty len = AST.Gvar {
  AST.gvar_readonly = false;
  AST.gvar_volatile = false;
  AST.gvar_init = replicate (to_int len) ty;
  AST.gvar_info = {
    StanE.vd_type = StanE.Bvector (Camlcoq.coqint_of_camlint len);
    StanE.vd_constraint = StanE.Cidentity;
    StanE.vd_dims = [];
    StanE.vd_init = None;
    StanE.vd_global = true;
  };
}

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                                 Type Lookup                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let type_table = Hashtbl.create 123456;;
Hashtbl.add type_table "target" StanE.Breal

module IdxTable =
  struct
    type t = BinNums.positive
    let equal i j = i=j
    let hash = Hashtbl.hash
  end
    (* let hash p = Camlcoq.P.to_int p *)

module IdxHashtbl = Hashtbl.Make(IdxTable)
let index_set = IdxHashtbl.create 123456;;

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
  | Stan.Econst_int i -> StanE.Econst_int (Camlcoq.Z.of_sint (int_of_string i), StanE.Bint)
  | Stan.Econst_float f -> StanE.Econst_float (Camlcoq.coqfloat_of_camlfloat (float_of_string f), StanE.Breal)
  | Stan.Evar i ->
    begin match Hashtbl.find_opt type_table i with
    | None -> StanE.Evar (Camlcoq.intern_string i, StanE.Breal)
    | Some ty -> StanE.Evar (Camlcoq.intern_string i, ty)
    end
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
    let isym = Camlcoq.intern_string i in
    IdxHashtbl.add index_set isym ();
    Hashtbl.add type_table i StanE.Bint;
    StanE.Sfor (isym, el_e e1, el_e e2, el_s s)
  | Stan.Sbreak -> StanE.Sbreak
  | Stan.Scontinue -> StanE.Scontinue
  | Stan.Sreturn oe -> StanE.Sreturn (mapo oe el_e)
  | Stan.Svar v -> raise (NIY_elab "statement: var")
  | Stan.Scall (i,el) -> StanE.Scall (Camlcoq.intern_string i,List.map el_e el)
  | Stan.Sprint lp -> raise (NIY_elab "statement: print")
  | Stan.Sreject lp -> raise (NIY_elab "statement: reject")
  | Stan.Sforeach (i,e,s) ->
    let isym = Camlcoq.intern_string i in
    IdxHashtbl.add index_set isym ();
    Hashtbl.add type_table i StanE.Bint;
    StanE.Sforeach (isym,el_e e, el_s s)
  | Stan.Starget e -> StanE.Starget (el_e e)
  | Stan.Stilde (e,i,el,(tr1,tr2)) ->
    let (_i, _ty) = match Hashtbl.find_opt transf_dist_idents i with
      | Some (ident, ty) -> (ident, ty)
      | None -> raise (NIY_elab ("tilde called with invalid distribution: "^ i))
    in
    StanE.Stilde (el_e e, StanE.Evar (_i, _ty), map el_e el, (mapo tr1 el_e,mapo tr2 el_e) )

let coqZ_of_string s =
  Integers.Int.intval (Camlcoq.coqint_of_camlint (of_int (int_of_string s)))

let el_b b dims =
  match (b, dims) with
  | (Stan.Bint,  []) -> StanE.Bint
  | (Stan.Breal, []) -> StanE.Breal
  | (Stan.Bint,  [Stan.Econst_int i]) -> StanE.Bvector (coqZ_of_string i) (* FIXME we don't have the ability to add int vectors? *)
  | (Stan.Breal, [Stan.Econst_int i]) -> StanE.Bvector (coqZ_of_string i) (* FIXME we don't have the ability to add int vectors? *)
  | (Stan.Bvector _, _) -> raise (NIY_elab "Use of unsupported type: vector")                                     
  | _ -> raise (NIY_elab "Use of unsupported type, please do not use matlab like expressions or types")


let elab elab_fun ol =
  match ol with
  | None -> None
  | Some l -> Some (List.map elab_fun l)

let g_init_int_zero =
  AST.Init_int32 (Integers.Int.repr (Camlcoq.coqint_of_camlint 0l))
let g_init_double_zero =
  AST.Init_float64 (Floats.Float.of_bits (Integers.Int64.repr (Camlcoq.coqint_of_camlint 0l)))

let g_init_space sz =
  AST.Init_space (Camlcoq.coqint_of_camlint (Int32.of_int sz))
let g_init_uninit_array l sz =
  g_init_space ((int_of_string l) * sz)

let transf_v_init v dims =
  match (v, dims) with
  | (Stan.Bint,  []) -> [g_init_space 4]
  | (Stan.Bint, [Stan.Econst_int l]) -> [g_init_uninit_array l 4]
  | (Stan.Breal, []) -> [g_init_space 8]
  | (Stan.Breal, [Stan.Econst_int l]) -> [g_init_uninit_array l 8]
  | _ -> []
let str_to_coqint s =
  (Camlcoq.coqint_of_camlint (of_int (int_of_string s)))

let transf_v_type v dims =
  match (v, dims) with
  | (Stan.Bint,  [Stan.Econst_int l]) -> ctarray (ctint, str_to_coqint l)
  | (Stan.Breal, [Stan.Econst_int l]) -> ctarray (ctdouble, str_to_coqint l)
  (* | (ty,  []) -> ty *)
  | _ -> raise (NIY_elab "type conversion not yet implemented")

let stype2basic s =
  match s with
  | Stypes.Tint -> StanE.Bint
  | Stypes.Treal -> StanE.Breal
  | _ -> raise (NIY_elab "do not call stype2basic on complex data representations")

let el_c c =
  match c with
  | Stan.Cidentity -> StanE.Cidentity
  | Stan.Clower e -> StanE.Clower (el_e e)
  | Stan.Cupper e -> StanE.Cupper (el_e e)
  | Stan.Clower_upper (l, u) -> StanE.Clower_upper (el_e l, el_e u)
  | Stan.Coffset e -> StanE.Coffset (el_e e)
  | Stan.Cmultiplier e -> StanE.Cmultiplier (el_e e)
  | Stan.Coffset_multiplier (l, u) -> StanE.Coffset_multiplier (el_e l, el_e u)
  | Stan.Cordered -> StanE.Cordered
  | Stan.Cpositive_ordered -> StanE.Cpositive_ordered
  | Stan.Csimplex -> StanE.Csimplex
  | Stan.Cunit_vector -> StanE.Cunit_vector
  | Stan.Ccholesky_corr -> StanE.Ccholesky_corr
  | Stan.Ccholesky_cov -> StanE.Ccholesky_cov
  | Stan.Ccorrelation -> StanE.Ccorrelation
  | Stan.Ccovariance -> StanE.Ccovariance

let mkLocal v =
  let id = Camlcoq.intern_string v.Stan.vd_id in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (v.Stan.vd_id,0) };
  let basic = el_b v.Stan.vd_type v.Stan.vd_dims in
  Hashtbl.add type_table v.Stan.vd_id basic;
  (v, id, basic)

let mkVariableFromLocal (v, id, basic) =
  let vd = {
    StanE.vd_type = basic;
    StanE.vd_constraint = el_c(v.Stan.vd_constraint);
    StanE.vd_dims = List.map el_e v.Stan.vd_dims;
    StanE.vd_init = mapo v.Stan.vd_init el_e;
    StanE.vd_global = true;
  } in
  (id,  AST.Gvar { AST.gvar_info = vd; gvar_init = transf_v_init v.Stan.vd_type v.Stan.vd_dims;
                   gvar_readonly = false; gvar_volatile = false})

let mkVariable v = mkVariableFromLocal (mkLocal v)
let declareVariable = mkVariable

let mkFunction name body rt params extraVars extraTemps =
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
  let params = List.map (fun ((x,y),z) -> ((x,y), Camlcoq.intern_string z)) params in

  let blocktypeFundef = function
    | "model" -> CStan.BTModel
    | "parameters" -> CStan.BTParameters
    | "data" -> CStan.BTData

    | "get_state" -> CStan.BTGetState (* neither of these are really blocks... *)
    | "set_state" -> CStan.BTSetState
    | "propose" -> CStan.BTPropose
    | "print_state" -> CStan.BTPrintState
    | "print_data" -> CStan.BTPrintData
    | "set_data" -> CStan.BTSetData

    | _ -> CStan.BTOther
  in

  let fd = {
    StanE.fn_return = rt;
    StanE.fn_callconv = AST.cc_default;
    StanE.fn_params = params;
    StanE.fn_blocktype = blocktypeFundef name;
    StanE.fn_vars = List.concat [extraVars; (IdxHashtbl.fold (fun k v acc -> (k,StanE.Bint)::acc) index_set [])];
    StanE.fn_temps = extraTemps;
    StanE.fn_body = body} in
  (id,  AST.Gfun(Ctypes.Internal fd))

let declareFundef name body rt params =
  mkFunction name body rt params [] []

let mapMaybe fn mval =
  match mval with
  | None -> None
  | Some v -> Some (fn v)

let fromMaybe default mval =
  match mval with
  | None -> default
  | Some v -> v

let maybe default fn mval =
  fromMaybe default (mapMaybe fn mval)

let sparam2stanEparam ((ad, ty), v) = ((ad, stype2basic ty), v)

let initOneVariable var =
  if not var.Stan.vd_global
  then Stan.Sskip
  else
    let evar = Stan.Evar var.Stan.vd_id in
    begin match var.Stan.vd_init with
    | Some e -> Stan.Sassign (evar, None, e)
    | None ->
      begin match (var.Stan.vd_type, var.Stan.vd_dims) with
      | (Stan.Bint,  []) -> Stan.Sassign (evar, None, Stan.Econst_int "0")
      | (Stan.Breal, []) -> Stan.Sassign (evar, None, Stan.Econst_float "0")
      | (Stan.Bint,  [Stan.Econst_int sz]) ->
        Stan.Sforeach ("i", evar, Stan.Sassign (Stan.Eindexed (evar, [Stan.Isingle (Stan.Evar "i")]), None, Stan.Econst_float "0"))
      | (Stan.Breal,  [Stan.Econst_int sz]) ->
        Stan.Sforeach ("i", evar, Stan.Sassign (Stan.Eindexed (evar, [Stan.Isingle (Stan.Evar "i")]), None, Stan.Econst_float "0"))
      | _ -> Stan.Sskip
      end
    end

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
    let get_code x = fromMaybe [Stan.Sskip] x in
    let unop x = fromMaybe [] x in

    let data_basics = List.map mkLocal (unop d) in
    let data_variables = List.map mkVariableFromLocal data_basics in
    let data_fields = List.map (fun tpl -> match tpl with (_, l, r) -> (l, r)) data_basics in

    let param_basics = List.map mkLocal (unop p) in
    let param_variables = List.map mkVariableFromLocal param_basics in
    let param_fields = List.map (fun tpl -> match tpl with (_, l, r) -> (l, r)) param_basics in

    let functions = [] in

    IdxHashtbl.clear index_set;
    let (id_data,f_data) = declareFundef "data" (maybe [] (List.map initOneVariable) d) None [] in
    let functions = (id_data,f_data) :: functions in

    IdxHashtbl.clear index_set;
    let (id_tr_data,f_tr_data) = declareFundef "transformed_data" (get_code td) None [] in
    let functions = (id_tr_data,f_tr_data) :: functions in

    IdxHashtbl.clear index_set;
    let (id_params,f_params) = declareFundef "parameters" (maybe [] (List.map initOneVariable) p) None [] in
    let functions = (id_params,f_params) :: functions in

    IdxHashtbl.clear index_set;
    let (id_tr_params,f_tr_params) = declareFundef "transformed_parameters" (get_code tp) None [] in
    let functions = (id_tr_params,f_tr_params) :: functions in

    IdxHashtbl.clear index_set;
    (* let target_arg = ((Stypes.Aauto_diffable, StanE.Breal), "target") in
     * let (id_model,f_model) = mkFunction "model" (get_code m) (Some StanE.Breal) [target_arg] [] in *)
    let (id_target, ty_target) = (Camlcoq.intern_string "target", StanE.Breal) in
    let target_var = (id_target, ty_target) in
    let (id_model,f_model) = mkFunction "model" (get_code m) (Some StanE.Breal) [] [] [target_var] in

    let functions = (id_model,f_model) :: functions in

    IdxHashtbl.clear index_set;
    let (id_gen_quant,f_gen_quant) = declareFundef "generated_quantities" (get_code g) None [] in
    let functions = (id_gen_quant,f_gen_quant) :: functions in

    IdxHashtbl.clear index_set;
    let (id_propose,f_propose) = declareFundef "propose" [Stan.Sskip] None [] in
    let functions = (id_propose,f_propose) :: functions in

    IdxHashtbl.clear index_set;
    let (id_get,f_get) = declareFundef "get_state" [Stan.Sskip] None [] in
    let functions = (id_get,f_get) :: functions in

    IdxHashtbl.clear index_set;
    let (id_set,f_set) = declareFundef "set_state" [Stan.Sskip] None [] in
    let functions = (id_set,f_set) :: functions in

    IdxHashtbl.clear index_set;
    let (id_print,f_print) = declareFundef "print_state" [Stan.Sskip] None [] in
    let functions = (id_print, f_print) :: functions in

    IdxHashtbl.clear index_set;
    let (id_print_data,f_print_data) = declareFundef "print_data" [Stan.Sskip] None [] in
    let functions = (id_print_data, f_print_data) :: functions in

    IdxHashtbl.clear index_set;
    let (id_set_data,f_set_data) = declareFundef "set_data" [Stan.Sskip] None [] in
    let functions = (id_set_data, f_set_data) :: functions in

    IdxHashtbl.clear index_set;
    let (id_main,f_main) = declareFundef "model_pdf" [Stan.Sskip] None [] in
    let functions = (id_main,f_main) :: functions in

    let functions =
      List.fold_left
        (fun acc -> fun ff -> (declareFundef ff.Stan.fn_name [ff.Stan.fn_body]
                                 (mapMaybe stype2basic ff.Stan.fn_return)
                                 (List.map sparam2stanEparam ff.Stan.fn_params)) :: acc)
        functions (unop f) in

    let gl1 = C2C.convertGlobdecls Env.empty [] (Env.initial_declarations()) in
    let _ = C2C.globals_for_strings gl1 in
    (* <><><><><><><><><><><><><><><> structs <><><><><><><><><><><><><><><> *)
    let (id_params_struct_typ, gl_params_struct) = declareStruct "Params" param_fields in
    let id_params_struct_global_state = declareGlobalStruct "state" in
    let id_params_struct_global_proposal = declareGlobalStruct "candidate" in
    let id_params_struct_arg = Camlcoq.intern_string "__p__" in
    let id_params_struct_tmp = Camlcoq.intern_string "__pt__" in
    let params_reserved = {
      CStan.res_params_type = id_params_struct_typ;
      CStan.res_params_global_state = id_params_struct_global_state;
      CStan.res_params_global_proposal = id_params_struct_global_proposal;
      CStan.res_params_arg = id_params_struct_arg;
      CStan.res_params_tmp = id_params_struct_tmp;
    } in

    let (id_data_struct_typ, gl_data_struct) = declareStruct "Data" data_fields in
    let id_data_struct_global = declareGlobalStruct "observation" in
    let id_data_struct_arg = Camlcoq.intern_string "__d__" in
    let id_data_struct_tmp = Camlcoq.intern_string "__dt__" in
    let data_reserved = {
      CStan.res_data_type = id_data_struct_typ;
      CStan.res_data_global = id_data_struct_global;
      CStan.res_data_arg = id_data_struct_arg;
      CStan.res_data_tmp = id_data_struct_tmp;
    } in

    let structs = [(id_params_struct_global_state, gl_params_struct); (id_params_struct_global_proposal, gl_params_struct); (id_data_struct_global, gl_data_struct)] in
    (* <><><><><><><><><><><><><><><> structs <><><><><><><><><><><><><><><> *)

    {
      StanE.pr_defs= data_variables @ param_variables @ structs @ stanlib_functions @ functions @ all_math_fns;
      StanE.pr_public=
        List.map fst functions
        @ List.map fst stanlib_functions @ List.map fst all_math_fns;
      StanE.pr_data=id_data;
      StanE.pr_data_vars=data_fields;
      StanE.pr_data_struct=data_reserved;
      StanE.pr_transformed_data=id_tr_data;
      StanE.pr_parameters=id_params;
      StanE.pr_parameters_vars=param_fields;
      StanE.pr_parameters_struct=params_reserved;
      StanE.pr_transformed_parameters=id_tr_params;
      StanE.pr_model=id_model;
      StanE.pr_target=id_target;
      StanE.pr_generated=id_gen_quant;
      StanE.pr_main=id_main;
      StanE.pr_math_functions=pr_math_functions;
      StanE.pr_dist_functions=pr_dist_functions;
    }

let location t =
  match t with
  (* These four tokens have a payload we ignore *)
  | STRINGLITERAL sp | REALNUMERAL sp | INTNUMERAL sp | IDENTIFIER sp -> snd sp
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
