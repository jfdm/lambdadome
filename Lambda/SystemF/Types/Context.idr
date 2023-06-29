module Lambda.SystemF.Types.Context

import Data.SnocList
import Data.SnocList.Elem
import Lambda.SystemF.Kinds
import Lambda.SystemF.Types.Model
import Lambda.SystemF.Types.Eval
import Lambda.SystemF.Types.Value

public export
data Context : Kontext -> Type where
 Empty : Context [<]
 ExtKind : Context ks -> Context (ks :< k)
 ExtType : Context ks -> Normal.Ty ks Star -> Context ks

public export
data IsVar : Context ks -> Normal.Ty ks Star -> Type
  where
    Here : IsVar (ExtType ks ty) ty

    IsKind : IsVar ks ty
          -> IsVar (ExtKind ks) (weaken ty)

    There : IsVar          ks      ty
         -> IsVar (ExtType ks ty') ty


-- [ EOF ]
