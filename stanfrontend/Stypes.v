Inductive type :=
  | Tint
  | Treal
  | Tvector
  | Trow
  | Tmatrix
  | Tarray: type -> type
  | Tfunction: typelist -> option type -> type
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

Inductive autodifftype :=
  | Adata_only 
  | Aauto_diffable.
