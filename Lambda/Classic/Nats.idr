||| Intrinsically-typed STLC.
|||
module Lambda.Classic.Nats

import Data.DPair
import Data.List.Elem
import Data.Fuel

import Toolkit.Decidable.Equality.Indexed

import Lambda.Common
import Lambda.Classic.Common

%default total

namespace Types

  public export
  data Ty : Type where

    TyFunc : (param, return : Ty) -> Ty
    TyNat  : Ty

  public export
  Context : Type
  Context = List Ty

namespace Terms

    public export
    data STLC : Context -> Ty -> Type where
      -- STLC

      Var : Elem type ctxt -> STLC ctxt type

      Func : (paramTy : Ty)
          -> (term : STLC (ctxt +=         paramTy) bodyTy)

                  -> STLC  ctxt    (TyFunc paramTy  bodyTy)

      App : {bodyTy, paramTy : Ty}
         -> (func  : STLC ctxt (TyFunc paramTy bodyTy))
         -> (value : STLC ctxt         paramTy)
                  -> STLC ctxt                 bodyTy

      MkNat : Nat -> STLC ctxt TyNat

namespace AST

  public export
  data AST = Var String
           | Func String Ty AST
           | App AST AST
           | N Nat

Rename Ty STLC where
  var = Var

  -- STLC
  rename f (Var idx) = Var (f idx)

  rename f (Func ty body)
    = Func ty (rename (weaken f) body)

  rename f (App func param)
    = App (rename f func) (rename f param)

  rename f (MkNat n)
    = MkNat n

Substitute Ty STLC where
  subst f (Var idx) = f idx

  subst f (Func type body)
    = Func type
           (subst (weakens f) body)


  subst f (App func var)
    = App (subst f func) (subst f var)

  subst f (MkNat n)
    = MkNat n

public export
data Value : STLC ctxt type -> Type where

  FuncV : {body : STLC (ctxt += type) bodyTy}
               -> Value (Func type body)

  MkNat : Value (MkNat n)

public export
data Redux : {type      : Ty}
          -> {ctxt      : List Ty}
          -> (this,that : STLC ctxt type)
                       -> Type
  where
    -- Functions reduce
    SimplifyFuncAppFunc : (func : Redux this that)
                               -> Redux (App this var)
                                        (App that var)

    SimplifyFuncAppVar : {this, that : STLC ctxt type}
                      -> {func       : STLC ctxt (TyFunc type return)}
                      -> (value      : Value func)
                      -> (var        : Redux this that)
                                    -> Redux (App func this)
                                             (App func that)

    ReduceFuncApp : {type : Ty}
                 -> {body : STLC (ctxt += type) return}
                 -> {var  : STLC  ctxt    type}
                 -> (value : Value var)
                          -> Redux (App (Func type body) var)
                                   (Single.subst var body)

namespace Progress
  public export
  data Progress : (term : STLC Nil type)
                       -> Type
    where
      Done : forall mty . {term : STLC Nil mty}
                        -> Value term
                        -> Progress term
      Step : {this, that : STLC Nil type}
          -> (prf        : Redux this that)
                        -> Progress this

  export
  progress : {ty   : Ty}
          -> (term : STLC Nil ty)
                  -> Progress term

  progress (Var _) impossible

  progress (Func type body) = Done FuncV

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Func typ b) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  progress (MkNat n) = Done MkNat

namespace Evaluation

  public export
  data Reduces : (this : STLC ctxt type)
              -> (that : STLC ctxt type)
              -> Type
    where
      Refl  : {this : STLC ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : STLC ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : STLC ctxt type)
                       -> Type
    where
      Normalised : {term : STLC ctxt type}
                        -> Value term
                        -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : STLC Nil type) -> Type where
    RunEval : {this, that : STLC Nil type}
           -> (steps      : Inf (Reduces this that))
           -> (result     : Finished that)
                         -> Evaluate this

  public export
  compute : {type : Ty}
         -> (fuel : Fuel)
         -> (term : STLC Nil type)
         -> Evaluate term
  compute Dry term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

covering
run : {type : Ty}
   -> (this : STLC Nil type)
           -> Maybe (Subset (STLC Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

namespace Types

  fP : (contra : a === b -> Void)
    -> TyFunc a y === TyFunc b w
    -> Void
  fP contra Refl = contra Refl

  fR : (contra : y === w -> Void)
    -> TyFunc a y === TyFunc a w
    -> Void
  fR contra Refl = contra Refl

  nNotF : TyNat === TyFunc p r -> Void
  nNotF Refl impossible

  export
  DecEq Ty where

    decEq (TyNat) (TyNat) = Yes Refl

    decEq TyNat (TyFunc a r) = No nNotF
    decEq (TyFunc a r) (TyNat) = No (negEqSym  nNotF)

    decEq (TyFunc x y) (TyFunc z w) with (decEq x z)
      decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) with (decEq y w)
        decEq (TyFunc x w) (TyFunc x w) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) | (No contra)
          = No (fR contra)
      decEq (TyFunc x y) (TyFunc z w) | (No contra)
        = No (fP contra)

namespace TypeChecking

  export
  check : (env  : Env Ty ctxt)
       -> (ast  : AST)
               -> Maybe (type ** STLC ctxt type)
  check env (Var x)
    = do (type ** prf) <- getType x env
         pure (type ** Var prf)

  check env (Func name type body) with (check (extend name type env) body)
    check env (Func name type body) | Nothing
      = Nothing
    check env (Func name type body) | (Just (MkDPair fst snd))
      = Just (_ ** Func type snd)

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

  check env (N n) = Just (MkDPair _ (MkNat n))

public export
data Result : Type
  where
    Error : Result

    MkRes : (  this : STLC Nil type)
         -> (  that : STLC Nil type)
         -> (0 prf  : Reduces this that)
                   -> Result
export
covering
compile : (ast : AST)
       -> Result
compile ast with (check empty ast)
  compile ast | Nothing
    = Error
  compile ast | (Just (MkDPair type term)) with (run term)
    compile ast | (Just (MkDPair type term)) | Nothing
      = Error
    compile ast | (Just (MkDPair type term)) | (Just (Element result trace))
      = MkRes term result trace

-- --------------------------------------------------------------------- [ EOF ]
