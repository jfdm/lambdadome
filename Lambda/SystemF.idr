module Lambda.SystemF

-- https://www.ioc.ee/~cneste/files/system-f-fun-and-profit.pdf

import public Lambda.SystemF.Types

%default total

public export
data Ty : (k : Kontext) -> Normal.Ty k Star -> Type where
  TyNat : Ty g Nat
  TyBool : Ty g Bool

  TyVar : (idx : Exists Star ktxt) -> Ty ktxt (NeutralTy (TyVar idx))

  TyForall : Ty (ktxt :< a) j -> Ty ktxt (Forall j)

  TyFun : (f : Ty ktxt ft)
     -> (a : Ty ktxt fa)
          -> Ty ktxt (Fun ft fa)

public export
data Term : Context k -> Normal.Ty k Star -> Type where
  Zero : Term g Nat
  Succ : Term g Nat -> Term g Nat
  True,False : Term g Bool

  Var : IsVar g ty -> Term g ty
  Fun : Ty ks a
     -> Term (ExtType g a) b
     -> Term          g    (Fun a b)

  App : Term g (Fun a b)
     -> Term g      a
     -> Term g        b

  Forall : Term (ExtKind g) b
        -> Term          g  (Forall b)

  Resolve : (body : Term      g (Forall b))
         -> (thi  : SystemF.Ty ks this)
                 -> Term      g (subst this b)


-- [ EOF ]
