||| Intrinsically-typed STLC.
|||
module Lambda.Classic.Full

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

      Func : {ctxt : List Ty}
           -> (paramTy : Ty)
          -> (term : STLC (ctxt +=         paramTy) bodyTy)

                  -> STLC  ctxt    (TyFunc paramTy  bodyTy)

      App : {bodyTy, paramTy : Ty}
         -> (func  : STLC ctxt (TyFunc paramTy bodyTy))
         -> (value : STLC ctxt         paramTy)
                  -> STLC ctxt                 bodyTy

namespace AST

  public export
  data AST = Var String
           | Func String Ty AST
           | App AST AST

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



namespace Terms
  mutual
    namespace Neutral
      public export
      data Term : STLC ctxt type -> Type where
        Var : Neutral.Term (Var idx)
        App : Neutral.Term func
           -> Normal.Term  var
           -> Neutral.Term (App func var)

    namespace Normal
      public export
      data Term : STLC ctxt type -> Type where
        Neutral : Neutral.Term m
               -> Normal.Term  m

        Fun : {body : STLC (type::ctxt) typeB}
           -> Normal.Term body
           -> Normal.Term (Func type body)

namespace Reduction

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
                        -> (var        : Redux this that)
                                      -> Redux (App func this)
                                               (App func that)

      ReduceFuncApp : {ctxt : List Ty}
                   -> {type : Ty}
                   -> {body : STLC (ctxt += type) return}
                   -> {var  : STLC  ctxt    type}
                            -> Redux (App (Func type body) var)
                                     (Single.subst var body)

      SimplifyFuncBody : Redux this that
                      -> Redux (Func type this)
                               (Func type that)


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

namespace Progress

  public export
  data Progress : STLC ctxt type -> Type where

      Done : forall mty
           . {term : STLC ctxt mty}
                  -> Normal.Term term
                  -> Progress term

      Step : {this, that : STLC ctxt type}
          -> (prf        : Redux this that)
                        -> Progress this

  export
  progress : {type : Ty}
          -> (term : STLC ctxt type)
                  -> Progress term
  progress (Var x) = Done (Neutral Var)
  progress (Func paramTy term) with (progress term)
    progress (Func paramTy term) | (Done x)
      = Done (Fun x)
    progress (Func paramTy term) | (Step prf)
      = Step (SimplifyFuncBody prf)

  progress (App (Var x) value) with (progress value)
    progress (App (Var x) value) | (Done y)
      = Done (Neutral (App Var y))
    progress (App (Var x) value) | (Step prf)
      =  Step (SimplifyFuncAppVar prf)

  progress (App (Func paramTy term) value)
    = Step ReduceFuncApp

  progress (App f@(App func x) value) with (progress f)
    progress (App f@(App func x) value) | (Done (Neutral y)) with (progress value)
      progress (App f@(App func x) value) | (Done (Neutral y)) | (Done z)
        = Done (Neutral (App y z))
      progress (App f@(App func x) value) | (Done (Neutral y)) | (Step prf)
        = Step (SimplifyFuncAppVar prf)
    progress (App f@(App func x) value) | (Step prf)
      = Step (SimplifyFuncAppFunc prf)

namespace Evaluation

  public export
  data Finished : (term : STLC ctxt type)
                       -> Type
    where
      Normalised : {term : STLC ctxt type}
                        -> Normal.Term term
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

-- --------------------------------------------------------------------- [ EOF ]
