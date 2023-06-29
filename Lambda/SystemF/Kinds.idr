module Lambda.SystemF.Kinds

import Data.SnocList
import Data.SnocList.Elem


public export
data Kind : Type
  where ||| Types of Types
        Star : Kind
        ||| Type of type-level functions
        Arrow : (f,a : Kind) -> Kind


public export
Exists : Kind -> SnocList Kind -> Type
Exists = Elem

public export
Exists' : SnocList Kind -> Kind -> Type
Exists' ks k = Elem k ks

public export
Kontext : Type
Kontext = SnocList Kind

public export
lift : ({l:_} -> Exists l k -> Exists l j)
    -> ({l:_} -> Exists l (k :< a) -> Exists l (j :< a))
lift f Here = Here
lift f (There x)
  = There (f x)


-- [ EOF ]
