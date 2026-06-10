open import Agda.Primitive using (Level; lsuc)

-- Some Aliases
module Type where

open import Agda.Primitive 
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to Type ; Setω to Typeω)
  public
