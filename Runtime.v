From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.7".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macosx".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "runtime.c".
  Definition normalized := false.
End Info.

Definition _U1 : ident := $"U1".
Definition _U2 : ident := $"U2".
Definition _W : ident := $"W".
Definition _X1 : ident := $"X1".
Definition _X2 : ident := $"X2".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition _argc : ident := $"argc".
Definition _argv : ident := $"argv".
Definition _atoi : ident := $"atoi".
Definition _call : ident := $"call".
Definition _candidate : ident := $"candidate".
Definition _exit : ident := $"exit".
Definition _get_parameters_size : ident := $"get_parameters_size".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _j__2 : ident := $"j__2".
Definition _j__3 : ident := $"j__3".
Definition _log : ident := $"log".
Definition _logdensity : ident := $"logdensity".
Definition _lp_candidate : ident := $"lp_candidate".
Definition _lp_parameters : ident := $"lp_parameters".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mu : ident := $"mu".
Definition _mult : ident := $"mult".
Definition _n : ident := $"n".
Definition _p_size : ident := $"p_size".
Definition _parameters : ident := $"parameters".
Definition _pow : ident := $"pow".
Definition _printf : ident := $"printf".
Definition _rand : ident := $"rand".
Definition _randn : ident := $"randn".
Definition _runtime : ident := $"runtime".
Definition _sigma : ident := $"sigma".
Definition _sqrt : ident := $"sqrt".
Definition _u : ident := $"u".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_X1 := {|
  gvar_info := tdouble;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_X2 := {|
  gvar_info := tdouble;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_call := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_randn := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_mu, tdouble) :: (_sigma, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_U1, tdouble) :: (_U2, tdouble) :: (_W, tdouble) ::
               (_mult, tdouble) :: (_t'7, tdouble) :: (_t'6, tdouble) ::
               (_t'5, tdouble) :: (_t'4, tdouble) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Evar _call tint) (Econst_int (Int.repr 1) tint)
                 tint)
    (Ssequence
      (Sassign (Evar _call tint) (Eunop Onotbool (Evar _call tint) tint))
      (Sreturn (Some (Ebinop Oadd (Etempvar _mu tdouble)
                       (Ebinop Omul (Etempvar _sigma tdouble)
                         (Ecast (Evar _X2 tdouble) tdouble) tdouble) tdouble))))
    Sskip)
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Scall (Some _t'2) (Evar _rand (Tfunction Tnil tint cc_default))
            nil)
          (Sset _U1
            (Ebinop Oadd (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
              (Ebinop Omul
                (Ebinop Odiv (Ecast (Etempvar _t'2 tint) tdouble)
                  (Econst_int (Int.repr 2147483647) tint) tdouble)
                (Econst_int (Int.repr 2) tint) tdouble) tdouble)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3) (Evar _rand (Tfunction Tnil tint cc_default))
              nil)
            (Sset _U2
              (Ebinop Oadd (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                (Ebinop Omul
                  (Ebinop Odiv (Ecast (Etempvar _t'3 tint) tdouble)
                    (Econst_int (Int.repr 2147483647) tint) tdouble)
                  (Econst_int (Int.repr 2) tint) tdouble) tdouble)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _pow (Tfunction (Tcons tdouble (Tcons tdouble Tnil))
                             tdouble cc_default))
                ((Etempvar _U1 tdouble) :: (Econst_int (Int.repr 2) tint) ::
                 nil))
              (Scall (Some _t'5)
                (Evar _pow (Tfunction (Tcons tdouble (Tcons tdouble Tnil))
                             tdouble cc_default))
                ((Etempvar _U2 tdouble) :: (Econst_int (Int.repr 2) tint) ::
                 nil)))
            (Sset _W
              (Ebinop Oadd (Etempvar _t'4 tdouble) (Etempvar _t'5 tdouble)
                tdouble)))))
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _W tdouble)
                       (Econst_int (Int.repr 1) tint) tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Sset _t'1
            (Ecast
              (Ebinop Oeq (Etempvar _W tdouble)
                (Econst_int (Int.repr 0) tint) tint) tbool)))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'6)
            (Evar _log (Tfunction (Tcons tdouble Tnil) tdouble cc_default))
            ((Etempvar _W tdouble) :: nil))
          (Scall (Some _t'7)
            (Evar _sqrt (Tfunction (Tcons tdouble Tnil) tdouble cc_default))
            ((Ebinop Odiv
               (Ebinop Omul (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)
                 (Etempvar _t'6 tdouble) tdouble) (Etempvar _W tdouble)
               tdouble) :: nil)))
        (Sset _mult (Etempvar _t'7 tdouble)))
      (Ssequence
        (Sassign (Evar _X1 tdouble)
          (Ebinop Omul (Etempvar _U1 tdouble) (Etempvar _mult tdouble)
            tdouble))
        (Ssequence
          (Sassign (Evar _X2 tdouble)
            (Ebinop Omul (Etempvar _U2 tdouble) (Etempvar _mult tdouble)
              tdouble))
          (Ssequence
            (Sassign (Evar _call tint)
              (Eunop Onotbool (Evar _call tint) tint))
            (Sreturn (Some (Ebinop Oadd (Etempvar _mu tdouble)
                             (Ebinop Omul (Etempvar _sigma tdouble)
                               (Ecast (Evar _X1 tdouble) tdouble) tdouble)
                             tdouble)))))))))
|}.

Definition f_runtime := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: (_p_size, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_parameters, (tptr tdouble)) :: (_j, tint) ::
               (_candidate, (tptr tdouble)) :: (_i, tint) :: (_j__1, tint) ::
               (_lp_parameters, tdouble) :: (_lp_candidate, tdouble) ::
               (_u, tdouble) :: (_j__2, tint) :: (_j__3, tint) ::
               (_t'6, tint) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _p_size tint) (Esizeof tdouble tulong) tulong) ::
       nil))
    (Sset _parameters (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _p_size tint)
                         tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _parameters (tptr tdouble))
                (Etempvar _j tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul (Etempvar _p_size tint) (Esizeof tdouble tulong)
             tulong) :: nil))
        (Sset _candidate (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _j__1 (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j__1 tint)
                                   (Etempvar _p_size tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _randn (Tfunction
                                       (Tcons tdouble (Tcons tdouble Tnil))
                                       tdouble cc_default))
                        ((Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _candidate (tptr tdouble))
                            (Etempvar _j__1 tint) (tptr tdouble)) tdouble)
                        (Ebinop Oadd
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _parameters (tptr tdouble))
                              (Etempvar _j__1 tint) (tptr tdouble)) tdouble)
                          (Etempvar _t'3 tdouble) tdouble))))
                  (Sset _j__1
                    (Ebinop Oadd (Etempvar _j__1 tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _logdensity (Tfunction
                                        (Tcons (tptr tdouble)
                                          (Tcons tint Tnil)) tdouble
                                        cc_default))
                    ((Etempvar _parameters (tptr tdouble)) ::
                     (Etempvar _p_size tint) :: nil))
                  (Sset _lp_parameters (Etempvar _t'4 tdouble)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _logdensity (Tfunction
                                          (Tcons (tptr tdouble)
                                            (Tcons tint Tnil)) tdouble
                                          cc_default))
                      ((Etempvar _candidate (tptr tdouble)) ::
                       (Etempvar _p_size tint) :: nil))
                    (Sset _lp_candidate (Etempvar _t'5 tdouble)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _rand (Tfunction Tnil tint cc_default)) nil)
                      (Sset _u
                        (Ebinop Odiv (Ecast (Etempvar _t'6 tint) tdouble)
                          (Econst_int (Int.repr 2147483647) tint) tdouble)))
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _u tdouble)
                                     (Ebinop Osub
                                       (Etempvar _lp_candidate tdouble)
                                       (Etempvar _lp_parameters tdouble)
                                       tdouble) tint)
                        (Ssequence
                          (Sset _j__2 (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j__2 tint)
                                             (Etempvar _p_size tint) tint)
                                Sskip
                                Sbreak)
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _parameters (tptr tdouble))
                                    (Etempvar _j__2 tint) (tptr tdouble))
                                  tdouble)
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _candidate (tptr tdouble))
                                    (Etempvar _j__2 tint) (tptr tdouble))
                                  tdouble)))
                            (Sset _j__2
                              (Ebinop Oadd (Etempvar _j__2 tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        Sskip)
                      (Ssequence
                        (Ssequence
                          (Sset _j__3 (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j__3 tint)
                                             (Etempvar _p_size tint) tint)
                                Sskip
                                Sbreak)
                              (Scall None
                                (Evar _printf (Tfunction
                                                (Tcons (tptr tschar) Tnil)
                                                tint
                                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                ((Evar ___stringlit_1 (tarray tschar 3)) ::
                                 (Ederef
                                   (Ebinop Oadd
                                     (Etempvar _parameters (tptr tdouble))
                                     (Etempvar _j__3 tint) (tptr tdouble))
                                   tdouble) :: nil)))
                            (Sset _j__3
                              (Ebinop Oadd (Etempvar _j__3 tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint
                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_2 (tarray tschar 2)) :: nil)))))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_argc, tint) :: (_argv, (tptr (tptr tschar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p_size, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _argc tint)
                   (Econst_int (Int.repr 2) tint) tint)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_3 (tarray tschar 45)) :: nil))
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_parameters_size (Tfunction Tnil tint
                                       {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
          nil)
        (Sset _p_size (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _atoi (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
            ((Ederef
               (Ebinop Oadd (Etempvar _argv (tptr (tptr tschar)))
                 (Econst_int (Int.repr 1) tint) (tptr (tptr tschar)))
               (tptr tschar)) :: nil))
          (Scall None
            (Evar _runtime (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid
                             cc_default))
            ((Etempvar _t'2 tint) :: (Etempvar _p_size tint) :: nil)))
        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_atoi,
   Gfun(External (EF_external "atoi"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tschar) Tnil) tint cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_rand,
   Gfun(External (EF_external "rand" (mksignature nil AST.Tint cc_default))
     Tnil tint cc_default)) ::
 (_log,
   Gfun(External (EF_external "log"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (_pow,
   Gfun(External (EF_external "pow"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (_sqrt,
   Gfun(External (EF_external "sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_logdensity,
   Gfun(External (EF_external "logdensity"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tfloat
                     cc_default)) (Tcons (tptr tdouble) (Tcons tint Tnil))
     tdouble cc_default)) ::
 (_get_parameters_size,
   Gfun(External (EF_external "get_parameters_size"
                   (mksignature nil AST.Tint
                     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_X1, Gvar v_X1) :: (_X2, Gvar v_X2) :: (_call, Gvar v_call) ::
 (_randn, Gfun(Internal f_randn)) :: (_runtime, Gfun(Internal f_runtime)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _runtime :: _randn :: _get_parameters_size :: _logdensity ::
 _printf :: _sqrt :: _pow :: _log :: _rand :: _exit :: _atoi :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


