module Lambda.SystemF.Types.Value

import Data.SnocList
import Data.SnocList.Elem

import Lambda.SystemF.Kinds

%default total

public export
data Ty : Kontext -> Kind -> Type
  where
    TyVar : {k : _}
         -> Exists k ktxt
         -> Ty     ktxt k

    TyFun : {k,j : _}
         -> Ty (ktxt :< k) j
         -> Ty  ktxt (Arrow k j)

    TyApp : {k,j : _}
         -> Ty ktxt (Arrow k j)
         -> Ty ktxt        k
         -> Ty ktxt          j

    Fun : (f, a : Ty ktxt Star)
               -> Ty ktxt Star

    Forall : {k : _}
          -> Ty (ktxt :< k) Star
          -> Ty  ktxt       Star

    Nat  : Ty ktxt Star
    Bool : Ty ktxt Star

public export
rename : ({l : _} -> Exists l k
                  -> Exists l j)
      -> Ty     k   a
      -> Ty       j a
rename f (TyVar x)
  = TyVar (f x)

rename f (TyFun x)
  = TyFun (rename (lift f) x)

rename f (TyApp x y)
  = TyApp (rename f x)
          (rename f y)

rename f (Fun x y)
  = Fun (rename f x)
        (rename f y)

rename f (Forall x)
  = Forall (rename (lift f) x)

rename f Nat
  = Nat
rename f Bool
  = Bool

public export
weaken : Ty k a -> Ty (k :< j) a
weaken = rename There

public export
lifts : ({j : _} -> Exists' a j
                 -> Ty      b j)
     -> ({j : _} -> Exists' (a :< k) j
                 -> Ty      (b :< k) j)
lifts f Here
  = TyVar Here
lifts f (There x)
  = weaken (f x)


public export
subst' : ({j : _} -> Exists' a j
                  -> Ty      b j)
      -> Ty a j
      -> Ty b j
subst' f (TyVar x)
  = f x

subst' f (TyFun x)
  = TyFun (subst' (lifts f) x)

subst' f (TyApp x y)
  = TyApp (subst' f x)
          (subst' f y)

subst' f (Fun x y)
  = Fun (subst' f x)
        (subst' f y)

subst' f (Forall x)
  = Forall (subst' (lifts f) x)

subst' f Nat
  = Nat
subst' f Bool
  = Bool

public export
extend : ({j : _} ->  Exists' a j
                  -> Ty      b j)
     -> Ty b k
     -> ({j : _} ->  Exists' (a :< k) j
                 -> Ty       b       j)
extend f x Here
  = x
extend f x (There y)
  = f y

public export
subst : Ty  a    k
     -> Ty (a :< k) j
     -> Ty  a       j
subst y
  = subst' (extend TyVar y)

-- [ EOF ]
