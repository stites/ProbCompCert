Inductive type :=
  | Tint
  | Treal
  | Tvector
  | Trow
  | Tmatrix
  | Tarray: type -> type.

Inductive autodifftype :=
  | Adata_only 
  | Aauto_diffable.
