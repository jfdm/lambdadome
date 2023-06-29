module Lambda.SystemF.Types.Model

import Data.SnocList
import Data.SnocList.Elem

import Lambda.SystemF.Kinds
import Lambda.SystemF.Types.Value

%default total

namespace Types

  mutual

    namespace Neutral
      public export
      data Ty : Kontext
             -> Kind
             -> Type
        where
          TyVar : (idx : Exists     k ktxt)
                      -> Neutral.Ty ktxt k

          TyApp : {k,j : _}
               -> (fun : Neutral.Ty ktxt (Arrow k j))
               -> (arg : Normal.Ty  ktxt        k)
                      -> Neutral.Ty ktxt          j

    namespace Normal
      public export
      data Ty : Kontext
             -> Kind
             -> Type
        where
          TyFun : {k,j : _}
               -> (param : Normal.Ty (ktxt :<     k) j)
                      -> Normal.Ty  ktxt (Arrow k  j)

          NeutralTy : {k : Kind}
                   -> Neutral.Ty ktxt k
                   -> Normal.Ty ktxt k

          Fun : (arg : Normal.Ty ktxt Star)
             -> (ret : Normal.Ty ktxt Star)
                    -> Normal.Ty ktxt Star

          Forall : {k : _}
                -> (param : Normal.Ty (ktxt :< k) Star)
                         -> Normal.Ty  ktxt       Star

          Nat  : Normal.Ty ktxt Star
          Bool : Normal.Ty ktxt Star

-- [ EOF ]
