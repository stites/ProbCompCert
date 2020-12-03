Inductive unsizedtype :=
  | Uint
  | Ureal
  | Uvector
  | Urow_vector
  | Umatrix
  | Uarray: unsizedtype -> unsizedtype.
			 
Inductive autodifftype := 
  | Adata_only 
  | Aauto_diffable.
