Inductive type :=
  | Tint
  | Treal
  | Tvector
  | Trow
  | Tmatrix
  | Tarray: type -> type.

(*   (* FIXME: remove Tfunction and inject in StanE *) *)
(*   | Tfunction: typelist -> option type -> type *)
(* with typelist : Type := *)
(*   | Tnil: typelist *)
(*   | Tcons: type -> typelist -> typelist. *)

Inductive autodifftype :=
  | Adata_only 
  | Aauto_diffable.
