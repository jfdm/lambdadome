module Lambda.SystemF.Types.Eval

import Data.SnocList
import Data.SnocList.Elem

import Lambda.SystemF.Kinds
import Lambda.SystemF.Types.Value
import Lambda.SystemF.Types.Model

%default total

namespace Renaming
  mutual

    namespace Normal
      public export
      rename : ({l : _} -> Exists l k
                        -> Exists l j)
            -> Normal.Ty k a
            -> Normal.Ty j a
      rename f (TyFun param)
        = TyFun (rename (lift f) param)

      rename f (NeutralTy x)
        = NeutralTy (rename f x)

      rename f (Fun arg ret)
        = Fun (rename f arg)
                (rename f ret)

      rename f (Forall param)
        = Forall (rename (lift f) param)

      rename f Nat
        = Nat

      rename f Bool
        = Bool

      public export
      weaken : Normal.Ty  ktxt       k
            -> Normal.Ty (ktxt :< j) k
      weaken = rename There

    namespace Neutral
      public export
      rename : {a : _}
            -> ({l : _} -> Exists l k
                        -> Exists l j)

            -> Neutral.Ty k a
            -> Neutral.Ty j a
      rename f (TyVar idx)
        = TyVar (f idx)

      rename f (TyApp fun arg)
        = TyApp (rename f fun)
                (rename f arg)

public export
Reduce : Kontext -> Kind -> Type
Reduce sx Star
  = Normal.Ty sx Star
Reduce sx (Arrow f a)
  = Either (Neutral.Ty sx (Arrow f a))
           ({j : _} -> ({l : _} -> Exists l sx -> Exists l j)
                    -> Reduce j f
                    -> Reduce j a)

public export
reflect : {k : Kind} -- @TODO Get rid of using viiew?
       -> Neutral.Ty ktxt k
       -> Reduce     ktxt k
reflect {k = Star} x
  = NeutralTy x

reflect {k = (Arrow f a)} x
  = Left x

public export
reify : {k,ktxt : _}
     -> Reduce    ktxt k
     -> Normal.Ty ktxt k
reify {k = Star} x
  = x
reify {k = (Arrow y z)} (Left x)
  = NeutralTy x
reify {k = (Arrow y z)} (Right x)
  = TyFun (reify (x There (reflect (TyVar Here))))

public export
rename : {s : Kind}
      -> {ktxt,jtxt : Kontext}
      -> ({i : _} -> Exists' ktxt i -> Exists' jtxt i)
      -> Reduce ktxt s
      -> Reduce jtxt s
rename {s = Star} f x
  = rename f x

rename {s = (Arrow y z)} f (Left x)
  = Left (rename f x)

rename {s = (Arrow y z)} f (Right x)
  = Right (\f' => x (f' . f))

public export
weaken : {s : Kind}
      -> {k : Kind}
      -> {ktxt : Kontext}
      -> Reduce ktxt        s
      -> Reduce (ktxt :< k) s
weaken = Eval.rename There

public export
Env : Kontext -> Kontext -> Type
Env ktxt jtxt = {o : _} -> Exists o ktxt -> Reduce jtxt o

public export
ext : ({r : _} -> Exists r a -> Reduce b r)
   -> Reduce b j
   -> ({r : _ } -> Exists r (a:<j) -> Reduce b r)
ext f x Here
  = x

ext f x (There y) = f y


public export
lift : {l, ktxt, jtxt : _}
    -> ({r : _} -> Exists r ktxt -> Reduce jtxt r) -- Env ktxt jtxt
    -> ({r : _} -> Exists r (ktxt :< l) -> Reduce (jtxt :< l) r)
lift f = ext (Eval.weaken . f) (reflect (TyVar Here))

public export
apply : {k,j : _}
     -> {ktxt : _}
     -> Reduce ktxt (Arrow k j)
     -> Reduce ktxt        k
     -> Reduce ktxt          j
apply (Left x) y = reflect (TyApp x (reify y))
apply (Right x) y = x id y

public export
eval : {k : Kind}
    -> {ktxt, jtxt : _}
    -> Value.Ty ktxt k
    -> ({r : _} -> Exists r ktxt -> Reduce jtxt r) -- Env    ktxt jtxt
    -> Reduce jtxt k
eval (TyVar x) f
  =  f x

eval (TyFun x) f
  = Right (\p, v => eval x (ext (Eval.rename p . f) v))

eval {k} (TyApp x y) f
  = Eval.apply (eval x f)
              (eval y f)

eval (Fun x a) f
  = Fun (reify (eval x f))
        (reify (eval a f))

eval (Forall x) f
  = Forall (reify (eval x
                        (Eval.lift f)
           ))

eval Nat f
  = Nat
eval Bool f
  = Bool


public export
identity : {ktxt : Kontext} -> Env ktxt ktxt
identity = (reflect . Neutral.TyVar)

public export
normalise : {k : Kind}
         -> {ktxt : Kontext}
         -> Value.Ty     ktxt k
         -> Normal.Ty ktxt k
normalise x = reify (eval x (identity))


mutual
  public export
  embedNeu : {k : _} -> Neutral.Ty ktxt k -> Value.Ty ktxt k
  embedNeu (TyVar idx) = TyVar idx
  embedNeu (TyApp fun arg) = TyApp (embedNeu fun) (embed arg)

  public export
  embed : Normal.Ty ktxt k
       -> Value.Ty  ktxt k
  embed (TyFun param) = TyFun (embed param)
  embed (NeutralTy x) = embedNeu x

  embed (Fun arg ret) = Fun (embed arg) (embed ret)
  embed (Forall param) = Forall (embed param)
  embed Nat = Nat
  embed Bool = Bool


namespace Subst

  public export
  lift : ({ k : _} -> Exists k a -> Normal.Ty b k)
      -> ({ k : _} -> Exists k (a :< j) -> Normal.Ty (b :< j) k)
  lift f Here
    = NeutralTy (TyVar Here)
  lift f (There x)
    = weaken (f x)

  public export
  extend : ({ k : _} -> Exists k a -> Normal.Ty b k)
        -> Normal.Ty b j
        -> ({ k : _} -> Exists k (a :< j) -> Normal.Ty b k)
  extend f x Here
    = x
  extend f x (There y)
    = f y

  public export
  subst' : {a,b,j : _}
        -> ({ r : _} -> Exists r a -> Normal.Ty b r)
        -> Normal.Ty a j
        -> Normal.Ty b j
  subst' x f
    = normalise (subst' (embed . x) (embed f))

  public export
  subst : {k,j,a : _}
       -> Normal.Ty  a    k
       -> Normal.Ty (a :< k) j
       -> Normal.Ty  a       j
  subst x y
    = subst' (extend (NeutralTy . TyVar) x)
             y

-- [ EOF ]
