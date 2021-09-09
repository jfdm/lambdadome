module Lambda.Dependent.Extrinsic

import Decidable.Equality
import Data.List.Elem

%default covering -- i know

namespace Names
  public export
  data Name = UDef String
            | Unknown
            | MGen String

  usNotUn : UDef x = Unknown -> Void
  usNotMg : UDef x = MGen y -> Void
  unNotMg : Unknown = MGen y -> Void

  mgNamesMismatch : (x = y -> Void) -> MGen x = MGen y -> Void
  usNamesMismatch : (x = y -> Void) -> UDef x = UDef y -> Void

  export
  total
  decEq : (a,b : Name) -> Dec (Equal a b)
  decEq (UDef x) (UDef y) with (decEq x y)
    decEq (UDef x) (UDef x) | (Yes Refl)
      = Yes Refl
    decEq (UDef x) (UDef y) | (No contra)
      = No (usNamesMismatch contra)

  decEq (UDef x) Unknown
    = No usNotUn

  decEq (UDef x) (MGen y)
    = No usNotMg

  decEq Unknown (UDef x)
    = No (negEqSym usNotUn)

  decEq Unknown Unknown = Yes Refl

  decEq Unknown (MGen x)
    = No unNotMg

  decEq (MGen x) (UDef y)
    = No (negEqSym usNotMg)

  decEq (MGen x) Unknown
    = No (negEqSym unNotMg)

  decEq (MGen x) (MGen y) with (decEq x y)
    decEq (MGen x) (MGen x) | (Yes Refl) = Yes Refl
    decEq (MGen x) (MGen y) | (No contra)
      = No (mgNamesMismatch contra)

  DecEq Name where
    decEq = Names.decEq

namespace Binders
  public export
  data Binder : Type -> Type where
    Fun : (type : term)
               -> Binder term

    Let : (type  : term)
       -> (value : term)
                -> Binder term


    FunTy : (type : term)
                 -> Binder term

namespace Env
  public export
  data Env : (type  : List Name -> Type)
          -> (names : List Name)
                   -> Type
    where
      Nil  : Env type Nil
      (::) : (bound : Binder (type vars))
          -> (rest  : Env type vars)
                   -> Env type (x::vars)

namespace Terms


  public export
  data Term : List Name -> Type where
    Var : (name : Name)
       -> (prf  : Elem name vars)
               -> Term vars

    Bound : (name  : Name)
         -> (thing : Binder (Term vars))
         -> (body  : Term (name :: vars))
                  -> Term vars

    App : (fun : Term vars)
       -> (arg : Term vars)
              -> Term vars

    TYPE : Term vars

namespace Values
  mutual
    namespace Local
      public export
      data Env : (free,vars : List Name) -> Type where
        Nil  : Local.Env free Nil
        (::) : Closure free
            -> Local.Env free vars
            -> Local.Env free (x::vars)

    public export
    data Closure : List Name -> Type where
      MkClosure : Local.Env free vars
               -> Env Term free
               -> Term (vars ++ free)
               -> Closure free
      MkClosureNF : Value free -> Closure free

    public export
    data Head : List Name -> Type where
      Var : (name : Name)
         -> Elem name vars
         -> Head vars

    public export
    data Value : List Name -> Type where
      Bound : (name  : Name)
           -> (thing : Binder (Value vars))
           -> (clos  : Closure vars -> Value vars)
                    -> Value vars

      App : (fun  : Head vars)
         -> (args : Closure vars)
                 -> Value vars

      TYPE : Value vars

namespace Eval

  export
  eval : Env Term free
      -> Term (vars ++ free)
      -> Value         free
  eval env (Var name prf) = ?eval_rhs_1

  eval env (Bound name (Fun type) body) = ?eval_rhs_4
  eval env (Bound name (Let type value) body) = ?eval_rhs_5
  eval env (Bound name (FunTy type) body) = ?eval_rhs_6

  eval env (App fun arg) = ?rhs
  eval env TYPE = TYPE

{-

namespace Env
  public

  public export
  data Env : Type -> Type where
    Empty : Env type
    Extend :
--    MkEnv : Nat -> List (Pair Name (Maybe Value)) -> Env
--
--
--  public export
--  data Elem : Pair Name (Maybe Value) -> Env -> Type where
--    Here : (prfN : Equal x y)
--                -> Elem (x,a) (MkEnv c ((y,b)::rest))
--
--    There : (contraN : Equal x y -> Void)
--         -> (later   : Elem (x,a) (MkEnv c rest))
--                    -> Elem (x,a) (MkEnv c ((y,b)::rest))
--
--  envEmpty : DPair (Maybe Value) (\type => Elem (name, type) (MkEnv c Nil)) -> Void
--  envEmpty (MkDPair _ (Here prfN)) impossible
--
--  notInRest : (name = x -> Void)
--           -> (DPair (Maybe Value) (\type => Elem (name, type) (MkEnv c xs)) -> Void)
--           -> DPair (Maybe Value) (\type => Elem (name, type) (MkEnv c ((x, type') :: xs)))
--           -> Void
--  notInRest f g (MkDPair type' (Here Refl)) = f Refl
--  notInRest f g (MkDPair fst (There contraN later)) = g (_ ** later)
--
--
--  export
--  lookup : (ctxt : Env)
--        -> (name : Name)
--                -> Dec (type ** Elem (name,type) ctxt)
--  lookup (MkEnv c []) name = No envEmpty
--  lookup (MkEnv c ((x,type') :: xs)) name with (decEq name x)
--    lookup (MkEnv c ((name,type') :: xs)) name | (Yes Refl) = Yes (MkDPair type' (Here Refl))
--    lookup (MkEnv c ((x,type') :: xs)) name | (No contra) with (lookup (MkEnv c xs) name)
--      lookup (MkEnv c ((x,type') :: xs)) name | (No contra) | (Yes (MkDPair fst snd))
--        = Yes (_ ** There contra snd)
--      lookup (MkEnv c ((x,type') :: xs)) name | (No contra) | (No f)
--        = No (notInRest contra f)

-}
--
--
--  getName' : Env -> Name -> Maybe Name
--  getName' xs Unknown = (Just Unknown)
--  getName' xs name with (lookup xs name)
--    getName' xs name | (Yes prf) = Nothing
--    getName' xs name | (No contra) = Just name
--
--  export
--  getName : Env -> Name -> Name
--  getName xs x with (getName' xs x)
--    getName xs x | Nothing = getName xs --(prime x)
--    getName xs x | (Just y) = y

--  getName env Unknown = Unknown
--
--  getName env name with (getName' env name)
--    getName env name | res with (getName env (prime res))
--      getName env name | res | with_pat = ?rhs_rhs

--  getName xs Unknown = Unknown
--  getName xs name with (lookup xs name)
--    getName xs name | (Yes _) with (_)
--      getName xs name | (Yes _) | with_pat = ?rhs_rhs
--    getName xs name | (No contra) = name

--namespace Eval
--
-- export
--  eval : Env -> Term TYPED -> Value


namespace Terms

  namespace Raw
    public export
    data Term : Type where
      Var : (name : Name) -> Raw.Term

      Bound : (name  : Name)
           -> (thing : Binder Raw.Term)
           -> (body  : Raw.Term)
                    -> Raw.Term

      App : (fun : Raw.Term)
         -> (arg : Raw.Term)
                -> Raw.Term

      TYPE : Raw.Term
