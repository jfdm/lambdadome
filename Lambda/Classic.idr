||| Intrinsically-typed STLC.
|||
module Lambda.Classic

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

Rename Ty STLC where
  var = Var

  -- STLC
  rename f (Var idx) = Var (f idx)

  rename f (Func ty body)
    = Func ty (rename (weaken f) body)

  rename f (App func param)
    = App (rename f func) (rename f param)


Substitute Ty STLC where
  subst f (Var idx) = f idx

  subst f (Func type body)
    = Func type
           (subst (weakens f) body)


  subst f (App func var)
    = App (subst f func) (subst f var)

namespace Values

  public export
  data Value : STLC ctxt type -> Type where

    FuncV : {body : STLC (ctxt += type) bodyTy}
                 -> Value (Func type body)


namespace Reduction

  public export
  data Redux : (this : STLC ctxt type)
            -> (that : STLC ctxt type)
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

  public export
  progress : (term : STLC Nil type)
          -> Progress term
  -- STLC
  progress {type} (Var _) impossible

  progress (Func type body) = Done FuncV

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Func ty b) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

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
  compute : forall type
          . (fuel : Fuel)
         -> (term : STLC Nil type)
         -> Evaluate term
  compute Dry term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : forall type
    . (this : STLC Nil type)
           -> Maybe (Subset (STLC Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

-- --------------------------------------------------------------------- [ EOF ]
