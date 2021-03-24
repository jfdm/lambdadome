||| An approach to intrinsically-typed STLC with types as terms.
|||
||| We use this razor to demonstrate succintly how Type universes are
||| used to separate descriptions of how types are formed and their
||| use to type values.
|||
||| Standard constructions are used to represent the language as an
||| EDSL, together with proof of progress taken from PLFA Part 2.
|||
||| This module compliments Appendix 2 of the Functional Pearl.
|||
||| Although the code appears to be total, there is a known issues
||| with Idris2 totality checker that causes it to slow down when
||| dealing with mutually defined terms.
|||
module Lambda.Classic

import Data.DPair
import Data.List.Elem
import Data.Fuel

import Toolkit.Decidable.Equality.Indexed

import Lambda.Common

%default total

namespace Types

  public export
  data Ty : Type where
    TyBool : Ty

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

      -- Base Values
      True  : STLC ctxt TyBool
      False : STLC ctxt TyBool

namespace Renaming

  public export
  weaken : (func : Contains old type
                -> Contains new type)
        -> (Contains (old += type') type
         -> Contains (new += type') type)

  weaken func Here = Here
  weaken func (There rest) = There (func rest)

  public export
  rename : (f : {type  : Ty} -> Contains old type
                             -> Contains new type)
        -> ({type : Ty} -> STLC old type
                        -> STLC new type)

  -- STLC
  rename f (Var idx) = Var (f idx)

  rename f (Func ty body)
    = Func ty (rename (weaken f) body)

  rename f (App func param)
    = App (rename f func) (rename f param)

  -- Base Values
  rename f True  = True
  rename f False = False

namespace Substitution
  public export
  weakens : (f : {type  : Ty}
                       -> Contains old type
                       -> STLC     new type)
         -> ({type  : Ty}
                   -> Contains (old += type') type
                   -> STLC     (new += type') type)
  weakens f Here = Var Here
  weakens f (There rest) = rename There (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {type  : Ty}
                       -> Contains old type
                       -> STLC     new type)
         -> ({type  : Ty}
                   -> STLC old type
                   -> STLC new type)

    -- STLC
    subst f (Var idx) = f idx

    subst f (Func type body)
      = Func type
             (subst (weakens f) body)


    subst f (App func var)
      = App (subst f func) (subst f var)

    -- Base Values
    subst f True  = True
    subst f False = False

  namespace Single
    public export
    apply : {typeA  : Ty}
         -> (this   : STLC      ctxt    typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> STLC      ctxt           typeA
    apply this Here = this
    apply this (There rest) = Var rest

    public export
    subst : {typeA         : Ty}
         -> {typeB         : Ty}
         -> (this          : STLC  ctxt           typeB)
         -> (inThis        : STLC (ctxt += typeB) typeA)
                          -> STLC  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis
      = General.subst (apply this) inThis


namespace Values

  public export
  data Value : STLC ctxt type -> Type where
    TrueV  : Value True
    FalseV : Value False

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

  -- Base Values
  progress True  = Done TrueV
  progress False = Done FalseV

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
