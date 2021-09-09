module Lambda.SystemF

-- https://www.ioc.ee/~cneste/files/system-f-fun-and-profit.pdf

import Decidable.Equality

%default total

infixr 6 +=

namespace Kind
  public export
  data Kind = Star | Arrow Kind Kind

  public export
  data Context : Type where
    Nil  : Context
    (::) : Kind -> Context -> Context

  public export
  (+=) : Context -> Kind -> Context
  (+=) ctxt k = k :: ctxt

  public export
  data HasKind : Kind -> Context -> Type where
    Here  : HasKind k (k::ks)
    There : HasKind k     ks
         -> HasKind k (l::ks)

  public export
  Rename : Context -> Context -> Type
  Rename k j = {l : Kind} -> HasKind l k
                          -> HasKind l j

  public export
  lift : Rename ktxt         jtxt
      -> Rename (ktxt += a) (jtxt += a)
  lift f Here = Here
  lift f (There x) = There (f x)

namespace Types
  namespace Raw
     public export
     data Ty : Context -> Kind -> Type where
       Var : {k    : Kind}
          -> {ktxt : Context}
          -> HasKind k ktxt
          -> Raw.Ty ktxt k

       Fun : Raw.Ty (ktxt += k) j
          -> Raw.Ty  ktxt (Arrow k j)

       App : {k,j : Kind}
          -> Raw.Ty ktxt (Arrow k j)
          -> Raw.Ty ktxt        k
          -> Raw.Ty ktxt          j

       FunTy : Raw.Ty ktxt Star
            -> Raw.Ty ktxt Star
            -> Raw.Ty ktxt Star

       Forall : {k : Kind}
             -> Raw.Ty (ktxt += k) Star
             -> Raw.Ty  ktxt       Star

  mutual

    namespace Neutral
      public export
      data Ty : (Kind.Context)
             -> Kind
             -> Type
        where
          Var : {k : Kind}
             -> (idx : HasKind    k ktxt)
                    -> Neutral.Ty ktxt k

          App : {k,j : Kind}
             -> (fun : Neutral.Ty ktxt (Arrow k j))
             -> (arg : Builder.Ty    ktxt        k)
                    -> Neutral.Ty ktxt          j

    namespace Builder
      public export
      data Ty : Kind.Context
             -> Kind
             -> Type
        where
          Fun : {k,j : Kind}
             -> (param : Builder.Ty (ktxt +=     k) j)
                      -> Builder.Ty  ktxt (Arrow k  j)

          NeutralTy : {k : Kind}
                   -> Neutral.Ty ktxt k
                   -> Builder.Ty ktxt k

          FunTy : (arg : Builder.Ty ktxt Star)
               -> (ret : Builder.Ty ktxt Star)
                      -> Builder.Ty ktxt Star

          Forall : {k : Kind}
                -> (param : Builder.Ty (ktxt += k) Star)
                         -> Builder.Ty  ktxt       Star

namespace Renaming
  mutual
    namespace Builder
      public export
      rename : {a : Kind}
            -> Rename ktxt jtxt
            -> Builder.Ty ktxt a
            -> Builder.Ty jtxt a
      rename f (Fun param)
        = Fun (rename (lift f) param)

      rename f (NeutralTy x)
        = NeutralTy (rename f x)

      rename f (FunTy arg ret)
        = FunTy (rename f arg)
                (rename f ret)

      rename f (Forall param)
        = Forall (rename (lift f) param)

      public export
      weaken : {k : Kind}
            -> Builder.Ty  ktxt       k
            -> Builder.Ty (ktxt += j) k
      weaken = rename There

    namespace Neutral
      public export
      rename : {a : Kind}
            -> Rename ktxt jtxt
            -> Neutral.Ty ktxt a
            -> Neutral.Ty jtxt a
      rename f (Var idx)
        = Var (f idx)

      rename f (App fun arg)
        = App (rename f fun)
              (rename f arg)

namespace NBE

  public export
  Reduce : Kind.Context
        -> Kind
        -> Type
  Reduce ktxt Star = Builder.Ty ktxt Star
  Reduce ktxt (Arrow x y) = Either (Neutral.Ty ktxt (Arrow x y))
                                   ({jtxt : Context} -> Rename ktxt jtxt
                                                     -> Reduce jtxt x
                                                     -> Reduce jtxt y)
  public export
  reflect : {k : Kind}
         -> {ktxt : Context}
         -> Neutral.Ty ktxt k
         -> Reduce     ktxt k
  reflect {k = Star} x = NeutralTy x
  reflect {k = (Arrow y z)} x = Left x

  public export
  reify : {k    : Kind}
       -> {ktxt : Context}
       -> Reduce     ktxt k
       -> Builder.Ty ktxt k
  reify {k = Star} x = x
  reify {k = (Arrow y z)} (Left x) = NeutralTy x
  reify {k = (Arrow y z)} (Right x) = Fun (reify (x There (reflect (Var Here))))

  public export
  rename : {s : Kind}
        -> {ktxt,jtxt : Context}
        -> Rename ktxt jtxt
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
        -> {ktxt : Context}
        -> Reduce ktxt        s
        -> Reduce (ktxt += k) s
  weaken = NBE.rename There


  public export
  Env : Context -> Context -> Type
  Env ktxt jtxt = {k : Kind} -> HasKind k ktxt -> Reduce jtxt k

  public export
  ext : {ktxt,jtxt : Context}
     -> Env ktxt jtxt
     -> {k : Kind}
     -> Reduce jtxt k
     -> Env (ktxt += k) jtxt
  ext f g Here {k = k} = g
  ext f g (There x) {k = k} = f x

  public export
  lift : {ktxt,jtxt : Context}
      -> Env ktxt jtxt
      -> {k : Kind}
      -> Env (ktxt += k)
             (jtxt += k)
  lift f {k} = ext (NBE.weaken . f) (reflect (Var Here))

  public export
  apply : {k,j : Kind}
       -> {ktxt : Context}
       -> Reduce ktxt (Arrow k j)
       -> Reduce ktxt        k
       -> Reduce ktxt          j
  apply (Left x) y = reflect (App x (reify y))
  apply (Right x) y = x id y

  public export
  eval : {k : Kind}
      -> {ktxt, jtxt : Context}
      -> Raw.Ty ktxt k
      -> Env    ktxt jtxt
      -> Reduce jtxt k
  eval (Var x) f = f x

  eval (Fun x) f = Right (\p, v => eval x (ext (NBE.rename p . f) v))

  eval (App x y) f = apply (eval x f) (eval y f)

  eval (FunTy x y) f = FunTy (reify (eval x f))
                             (reify (eval y f))

  eval (Forall x) f = Forall (reify (eval x (NBE.lift f)))

  public export
  identity : {ktxt : Context} -> Env ktxt ktxt
  identity = (reflect . Neutral.Var) -- (reflect . Var)

  public export
  normalise : {k : Kind}
           -> {ktxt : Context}
           -> Raw.Ty     ktxt k
           -> Builder.Ty ktxt k
  normalise x = reify (eval x (identity))


namespace Terms

  public export
  data Context : Kind.Context -> Type where
    Empty   : Context Nil
    ExtKind : (j : Kind)
           -> Context ktxt
           -> Context (ktxt += j)

    ExtTy : Builder.Ty ktxt Star
         -> Context ktxt
         -> Context ktxt

  public export
  data HasType : Builder.Ty ktxt Star
              -> Context ktxt
              -> Type
    where
      Here : {type : Builder.Ty ktxt Star}
          -> HasType type (ExtTy type ctxt)

      ThereTy : {typeA : Builder.Ty ktxt Star}
             -> {typeB : Builder.Ty ktxt Star}
             -> (rest : HasType typeA              ctxt)
                     -> HasType typeA (ExtTy typeB ctxt)

      ThereK : {typeA : Builder.Ty ktxt Star}
            -> {k    : Kind}
            -> (rest : HasType typeA ctxt)
                    -> HasType (weaken typeA) (ExtKind k ctxt)

  public export
  data Term : (ctxt : Context ktxt) -> Builder.Ty ktxt Star -> Type where
    Var : (idx  : HasType type ctxt)
               -> Term ctxt type

    Fun : (body : Term (ExtTy param ctxt) type)
               -> Term  ctxt (FunTy param type)

    App : (fun : Term ctxt (FunTy param type))
       -> (arg : Term ctxt param)
              -> Term ctxt type

    Forall : (body : Term (ExtKind Star ctxt) type)
                  -> Term               ctxt  (Forall type)

    AppTy : (fun : Term ctxt (Forall param))
         -> (arg : Builder.Ty ktxt k)
                -> Term ctxt (?subst param arg)
