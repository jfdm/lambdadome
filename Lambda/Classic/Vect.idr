module Lambda.Classic.Vect

import Decidable.Equality
import Data.List.Elem
import Data.Nat

%default total

namespace Properties

  ||| Magic
  public export
  data ValidSlice : (alpha, omega, upper : Nat) -> Type where
    MkValidSlice : ValidSlice a o u

namespace Types
  public export
  data Ty = TyNat | TyVect Nat Ty | TyFunc Ty Ty


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

    MkNat : (n : Nat)
             -> Term ctxt TyNat

    Vec : (size : Nat)
       -> (type : Ty)
               -> Term ctxt (TyVect size type)

    Slice : (term  : Term ctxt (TyVect size type))
         -> (alpha : Nat)
         -> (omega : Nat)
         -> (prf   : ValidSlice alpha omega size)
                  -> Term ctxt
                          (TyVect (minus omega alpha) type)

  namespace Undecorated
    public export
    data AST = Ref String
             | Lam String Ty AST
             | App AST AST
             | Vec Nat Ty
             | Slice AST Nat Nat

namespace Env

  public export
  data Env : List Ty -> Type
    where
      Empty : Env Nil
      Ext : String -> (ty : Ty) -> Env rest -> Env (ty :: rest)

  export
  getType : String -> Env tys -> Maybe (type ** Elem type tys)
  getType x Empty = Nothing
  getType x (Ext y ty z) with (decEq x y)
    getType y (Ext y ty z) | (Yes Refl) = Just (ty ** Here)
    getType x (Ext y ty z) | (No contra) with (getType x z)
      getType x (Ext y ty z) | (No contra) | Nothing = Nothing
      getType x (Ext y ty z) | (No contra) | (Just (MkDPair fst orf)) = Just (fst ** There orf)

namespace TypeChecking

  DecEq Ty where
    decEq = ?as

  check : (env : Env ctxt)
       -> AST
       -> Maybe (type ** Term ctxt type)
  check env (Ref x) with (getType x env)
    check env (Ref x) | Nothing
      = Nothing
    check env (Ref x) | (Just (MkDPair fst snd))
      = Just (fst ** Var snd)

  check env (Lam n type body) with (check (Ext n type env) body)
    check env (Lam n type body) | Nothing
      = Nothing
    check env (Lam n type body) | (Just (MkDPair fst snd))
      = Just (_ ** Fun type snd)

  check env (App x y) with (check env x)
    check env (App x y) | Nothing
      = Nothing

    check env (App x y) | (Just (MkDPair (TyFunc z w) snd)) with (check env y)
      check env (App x y) | (Just (MkDPair (TyFunc z w) snd)) | Nothing
        = Nothing
      check env (App x y) | (Just (MkDPair (TyFunc z w) snd)) | (Just (MkDPair fst v)) with (decEq z fst)
        check env (App x y) | (Just (MkDPair (TyFunc fst w) snd)) | (Just (MkDPair fst v)) | (Yes Refl)
          = Just (_ ** App snd v)
        check env (App x y) | (Just (MkDPair (TyFunc z w) snd)) | (Just (MkDPair fst v)) | (No contra)
          = Nothing
    check env (App x y) | (Just (MkDPair _ snd))
      = Nothing

  check env (Vec size type)
    = Just (_ ** Vec size type)

  check env (Slice x y z) with (check env x)
    check env (Slice x y z) | Nothing
      = Nothing
    check env (Slice x y z) | (Just (MkDPair (TyVect k w) snd))
      = Just (_ ** Slice snd y z MkValidSlice)

    check env (Slice x y z) | (Just (MkDPair _  snd))
      = Nothing
