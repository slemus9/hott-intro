open import Agda.Primitive using (Level)

-- Some Aliases
module Type where

Type = Set
Type1 = Set1
Type2 = Set2
Type3 = Set3

TypeN = (n : Level) -> Set n
