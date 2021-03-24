||| A Default Calculus in which some arguments are presented with default values.
|||
||| Compile Time Safe and Runtime Unsafe
module Lambda.Classic.Default

import Decidable.Equality
import Data.List.Elem
import Data.Nat

%default total

namespace Types
  public export
  data Ty = TyParam Nat | TyNat | TyFunc Ty Ty


namespace Terms
  public export
  data Term : List Ty -> Ty -> Type where
    Var : (idx : Elem type ctxt)
              -> Term ctxt type

    Fun : (type_param : Ty)
       -> (body       : Term (type_param::ctxt) type_ret)
                     -> Term ctxt (TyFunc type_param type_ret)

    App : (func : Term ctxt (TyFunc p r))
       -> (arg  : Term ctxt         p)
               -> Term ctxt           r

    AppDef : (func : Term ctxt (TyFunc (TyParam n) r))
                  -> Term ctxt                     r

    AppOver : (fun : Term ctxt (TyFunc (TyParam n) r))
           -> (arg : Term ctxt         (TyParam m))
                  -> Term ctxt                     r

    MkNat : (n : Nat)
              -> Term ctxt TyNat

    ToNat : Term ctxt (TyParam n)
         -> Term ctxt TyNat

    MkParam : (n : Nat)
           -> Term ctxt (TyParam n)


  namespace Undecorated

    public export
    data AST = Var String
             | Fun String Ty AST
             | App AST AST
             | MkNat Nat
             | ToNat AST
             | MkParam Nat
             | AppDef AST
             | AppOver AST AST

namespace Types

  pNotN : TyParam k === TyNat -> Void
  pNotN Refl impossible

  pIdx : (contra : i === k -> Void)
      -> TyParam i === TyParam k
      -> Void
  pIdx contra Refl = contra Refl

  pNotFunc : TyParam i === TyFunc p r -> Void
  pNotFunc Refl impossible

  nNotF : TyNat === TyFunc p r -> Void
  nNotF Refl impossible

  fP : (contra : a === b -> Void)
    -> TyFunc a y === TyFunc b w
    -> Void
  fP contra Refl = contra Refl

  fR : (contra : y === w -> Void)
    -> TyFunc a y === TyFunc a w
    -> Void
  fR contra Refl = contra Refl

  export
  DecEq Ty where
    decEq (TyParam k) (TyParam j) with (decEq k j)
      decEq (TyParam k) (TyParam k) | (Yes Refl) = Yes Refl
      decEq (TyParam k) (TyParam j) | (No contra)
        = No (pIdx contra)

    decEq (TyParam k) TyNat = No pNotN

    decEq (TyParam k) (TyFunc x y)
      = No pNotFunc

    decEq TyNat (TyParam k) = No (negEqSym pNotN)
    decEq TyNat TyNat = Yes Refl

    decEq TyNat (TyFunc x y) = No nNotF

    decEq (TyFunc x y) (TyParam k) = No (negEqSym pNotFunc)
    decEq (TyFunc x y) TyNat = No (negEqSym nNotF)

    decEq (TyFunc x y) (TyFunc z w) with (decEq x z)
      decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) with (decEq y w)
        decEq (TyFunc x w) (TyFunc x w) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) | (No contra)
          = No (fR contra)
      decEq (TyFunc x y) (TyFunc z w) | (No contra)
        = No (fP contra)


namespace TypeChecking
  namespace Env

    data Item : Ty -> Type where
      MkItem : (name : String)
            -> (ty   : Ty)
                    -> Item ty

    export
    data Env : List Ty -> Type
      where
        Empty : Env Nil
        Cons : Item ty -> Env rest -> Env (ty :: rest)

    export
    empty : Env Nil
    empty = Empty

    export
    extend : (name : String)
          -> (type : Ty)
          -> (env  : Env rest)
                  -> Env (type::rest)
    extend name type env = Cons (MkItem name type) env

    export
    getType : String -> Env tys -> Maybe (type ** Elem type tys)
    getType x Empty = Nothing
    getType x (Cons (MkItem y ty) z) with (decEq x y)
      getType y (Cons (MkItem y ty) z) | (Yes Refl) = Just (ty ** Here)
      getType x (Cons (MkItem y ty) z) | (No contra) with (getType x z)
        getType x (Cons (MkItem y ty) z) | (No contra) | Nothing = Nothing
        getType x (Cons (MkItem y ty) z) | (No contra) | (Just (MkDPair fst orf)) = Just (fst ** There orf)


  namespace Checker

    export
    check : (env  : Env ctxt)
         -> (ast  : AST)
                 -> Maybe (type ** Term ctxt type)
    check env (Var x)
      = do (type ** prf) <- getType x env
           pure (type ** Var prf)

    check env (Fun name type body) with (check (extend name type env) body)
      check env (Fun name type body) | Nothing
        = Nothing
      check env (Fun name type body) | (Just (MkDPair fst snd))
        = Just (_ ** Fun type snd)

    check env (App x y) with (check env x)
      check env (App x y) | Nothing
        = Nothing

      check env (App x y) | (Just (MkDPair (TyFunc paramTy returnTy) f)) with (check env y)
        check env (App x y) | (Just (MkDPair (TyFunc paramTy returnTy) f)) | Nothing
          = Nothing
        check env (App x y) | (Just (MkDPair (TyFunc paramTy returnTy) f)) | (Just (MkDPair paramTy' a)) with (decEq paramTy paramTy')
          check env (App x y) | (Just (MkDPair (TyFunc paramTy' returnTy) f)) | (Just (MkDPair paramTy' a)) | (Yes Refl)
            = Just (_ ** App f a)
          check env (App x y) | (Just (MkDPair (TyFunc paramTy returnTy) f)) | (Just (MkDPair paramTy' a)) | (No contra)
            = Nothing
      check env (App x y) | (Just (MkDPair _ snd))
        = Nothing

    check env (MkNat k)
      = Just (_ ** MkNat k)

    check env (ToNat x) with (check env x)
      check env (ToNat x) | Nothing
        = Nothing
      check env (ToNat x) | (Just (MkDPair (TyParam k) snd))
        = Just ( _ ** ToNat snd)
      check env (ToNat x) | (Just (MkDPair _ snd))
        = Nothing

    -- 'Typing Rule'/'Rewrite' to insert
    check env (AppDef f) with (check env f)
      check env (AppDef f) | Nothing
        = Nothing
      check env (AppDef f) | (Just (MkDPair (TyFunc (TyParam k) y) snd))
        = Just (_ ** AppDef snd)

        -- Just (_ ** App snd (MkParam k))

      check env (AppDef f) | (Just (MkDPair (TyFunc _ y) snd))
        = Nothing
      check env (AppDef f) | (Just (MkDPair _ snd))
        = Nothing

    check env (AppOver forig aorig) with (check env forig)
      check env (AppOver forig aorig) | Nothing
        = Nothing
      check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) with (check env aorig)
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | Nothing
          = Nothing
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | (Just (MkDPair (TyParam m) a))
          = Just (_ ** AppOver f a)
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | (Just (MkDPair _ _))
          = Nothing

      check env (AppOver forig aorig) | (Just (MkDPair _ _))
        = Nothing

    check env (MkParam n)
      = Just (_ ** MkParam n)

example0 : AST
example0
  = App (Fun "x" (TyParam 3)
             (ToNat (Var "x")))
        ((MkParam 2))

example1 : AST
example1
  = AppDef (Fun "x" (TyParam 3)
                (ToNat (Var "x")))
