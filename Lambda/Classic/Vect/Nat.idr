module Lambda.Classic.Vect.Nat

import Decidable.Equality
import Data.List.Elem
import Data.Nat

data ValidSlice : (alpha, omega, upper : Nat) -> Type where
  MkValidSlice : ValidSlice a o u

data Ty = TyParam Nat | TyNat Nat | TyVect Nat Ty | TyFunc Ty Ty

DecEq Ty where


data Term : List Ty -> Ty -> Type where
  Var : (idx : Elem type ctxt)
            -> Term ctxt type

  Fun : (type_param : Ty)
     -> (body       : Term (type_param::ctxt) type_ret)
                   -> Term ctxt (TyFunc type_param type_ret)

  App : (func : Term ctxt (TyFunc p r))
     -> (arg  : Term ctxt         p)
             -> Term ctxt           r

  FunP : (n : Nat)
      -> (body : Term (TyParam n::ctxt) type_ret)
               -> Term ctxt (TyFunc (TyParam n) type_ret)

  AppParamOverride : (func : Term ctxt (TyFunc p r))
                  -> (p : Term ctxt (TyParam n))
                       -> Term ctxt r

  NatOpTotal : (op : Nat -> Nat -> Nat)
            -> Term ctxt (TyNat a)
            -> Term ctxt (TyNat b)
            -> Term ctxt (TyNat (op a b))

  NatOpDiv : Term ctxt (TyNat a)
          -> Term ctxt (TyNat b)
          -> IsSucc b
          -> Term ctxt (TyNat (div a b))

  MkNat : (n : Nat)
           -> Term ctxt (TyNat n)

  MkParamD : (n : Nat)
               -> Term ctxt (TyParam n)

  ToNat : Term ctxt (TyParam n) -> Term ctxt (TyNat n)

  Vec : (size : Term ctxt (TyNat n))
     -> (type : Ty)
             -> Term ctxt (TyVect n type)

  Slice : (term  : Term ctxt (TyVect size type))
       -> (alpha : Term ctxt (TyNat a))
       -> (omega : Term ctxt (TyNat o))
       -> (prf   : ValidSlice a o size)
                -> Term ctxt
                        (TyVect (minus o a) type)

data AST = Ref String
         | Lam String Ty AST
         | LamP Nat String AST
         | ApP  AST AST
         | Ap AST AST
         | Op (Nat -> Nat -> Nat) AST AST
         | Div AST AST
         | N Nat
         | MkPDef Nat
         | ToN AST
         | MVec AST Ty AST
         | Sl AST AST AST


data Env : List Ty -> Type
  where
    Empty : Env Nil
    Ext : String -> (ty : Ty) -> Env rest -> Env (ty :: rest)

getType : String -> Env tys -> Maybe (type ** Elem type tys)
getType x Empty = Nothing
getType x (Ext y ty z) with (decEq x y)
  getType y (Ext y ty z) | (Yes Refl) = Just (ty ** Here)
  getType x (Ext y ty z) | (No contra) with (getType x z)
    getType x (Ext y ty z) | (No contra) | Nothing = Nothing
    getType x (Ext y ty z) | (No contra) | (Just (MkDPair fst orf)) = Just (fst ** There orf)

check : (env : Env ctxt)
     -> AST
     -> Maybe (type ** Term ctxt type)
check env (Ref x) with (getType x env)
  check env (Ref x) | Nothing = Nothing
  check env (Ref x) | (Just (MkDPair fst snd)) = Just (fst ** Var snd)

check env (Lam n x y) with (check (Ext n x env) y)
  check env (Lam n x y) | Nothing = Nothing
  check env (Lam n x y) | (Just (MkDPair fst snd)) with (decEq x fst)
    check env (Lam n fst y) | (Just (MkDPair fst snd)) | (Yes Refl) = Just (_ ** Fun fst snd)
    check env (Lam n x y) | (Just (MkDPair fst snd)) | (No contra) = Nothing

check env (Ap f a) with (check env f)
  check env (Ap f a) | Nothing = Nothing
  check env (Ap f a) | (Just (MkDPair (TyFunc x y) snd)) with (check env a)
    check env (Ap f a) | (Just (MkDPair (TyFunc x y) snd)) | Nothing = Nothing
    check env (Ap f a) | (Just (MkDPair (TyFunc x y) snd)) | (Just (MkDPair fst z)) with (decEq x fst)
      check env (Ap f a) | (Just (MkDPair (TyFunc fst y) snd)) | (Just (MkDPair fst z)) | (Yes Refl)
        = Just (_ ** App snd z)
      check env (Ap f a) | (Just (MkDPair (TyFunc x y) snd)) | (Just (MkDPair fst z)) | (No contra) = Nothing
  check env (Ap f a) | (Just (MkDPair _            snd)) = Nothing

check env (Op f x y) = ?check_rhs_3

check env (N n) = Just (_ ** MkNat n)

check env (MkPDef n) = Just (_ ** MkParamD n)

{-
  FunP : (n : Nat)
      -> (body : Term (TyParam n::ctxt) type_ret)
               -> Term ctxt (TyFunc (TyParam n) type_ret)

  AppParamOverride : (func : Term ctxt (TyFunc p r))
                  -> (p : Term ctxt (TyNat n))
                       -> Term ctxt r

-}
--check env (MkPE) = Just (_ ** MkParamE)

check env (LamP n x b) = ?rhs_1
check env (ApP  f a)   = ?rhs_2

check env (ToN n) with (check env n)
  check env (ToN n) | Nothing = Nothing
  check env (ToN n) | (Just (MkDPair (TyParam k) snd))
    = Just (_ ** ToNat snd)
  check env (ToN n) | (Just (MkDPair _ snd)) = Nothing

check env (Div x y) with (check env x)
  check env (Div x y) | Nothing = Nothing
  check env (Div x y) | (Just (MkDPair (TyNat k) snd)) with (check env y)
    check env (Div x y) | (Just (MkDPair (TyNat k) snd)) | Nothing
      = Nothing
    check env (Div x y) | (Just (MkDPair (TyNat k) snd)) | (Just (MkDPair (TyNat j) z)) with (isItSucc j)
      check env (Div x y) | (Just (MkDPair (TyNat k) snd)) | (Just (MkDPair (TyNat (S n)) z)) | (Yes ItIsSucc)
        = Just (_ ** NatOpDiv snd z ItIsSucc)
      check env (Div x y) | (Just (MkDPair (TyNat k) snd)) | (Just (MkDPair (TyNat j) z)) | (No contra)
        = Nothing
    check env (Div x y) | (Just (MkDPair (TyNat k) snd)) | (Just (MkDPair _ z))
      = Nothing

  check env (Div x y) | (Just (MkDPair _ snd))
    = Nothing

check env (MVec x y z) = ?check_rhs_5

check env (Sl x y z) with (check env x)
  check env (Sl x y z) | Nothing = Nothing
  check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) with (check env y)
    check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | Nothing
      = Nothing
    check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | (Just (MkDPair (TyNat j) w)) with (check env z)
      check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | (Just (MkDPair (TyNat j) w)) | Nothing
        = Nothing
      check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | (Just (MkDPair (TyNat j) w)) | (Just (MkDPair (TyNat i) v))
        = Just (_ ** Slice snd w v MkValidSlice)
      check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | (Just (MkDPair (TyNat j) w)) | (Just (MkDPair _ v))
        = Nothing
    check env (Sl x y z) | (Just (MkDPair (TyVect k type) snd)) | (Just (MkDPair _ w))
      = Nothing

  check env (Sl x y z) | (Just (MkDPair _ snd))
    = Nothing
