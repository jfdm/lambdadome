||| An approach to intrinsically-typed STLC with types as terms.
|||
||| We use this razor to demonstrate succintly how Type universes are
||| used to separate descriptions of how types are formed and their
||| use to type values.
|||
||| Standard constructions are used to represent the language as an
||| EDSL, together with proof of progress taken from PLFA Part 2.
|||
module Lambda.NewWave

import Data.DPair
import Data.List.Elem
import Data.Fuel

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem
import Toolkit.Decidable.Equality.Indexed

import Lambda.Common

%default total

namespace Types

  ||| Levels at which types and their types are defined in our type
  ||| universes.
  public export
  data Level = TYPE -- Build types here
             | VALUE -- Use types here.

  ||| Our types are meta types...
  public export
  data MTy : Level -> Type where

    FuncTy : MTy level -> MTy level -> MTy level


  ||| A predicate to type check types against type formers.
  public export
  data TyCheck : (type : MTy TYPE)
              -> (value : MTy VALUE)
              -> Type
    where

      ChkFunc : TyCheck paramTy  paramValue
             -> TyCheck returnTy returnValue
             -> TyCheck (FuncTy paramTy    returnTy)
                        (FuncTy paramValue returnValue)

  ||| A context is a list of types in different universes.
  public export
  Context : List Level -> Type
  Context = DList Level MTy

  public export
  Elem : Context lvls -> MTy level -> Type
  Elem g ty = Elem Level MTy ty g

namespace Terms

    public export
    data STLC : Context lvls -> MTy level -> Type where
      -- STLC

      Var : Elem Level MTy type ctxt -> STLC ctxt type

      Func : {paramTyType     : MTy TYPE}
          -> {paramTy, bodyTy : MTy VALUE}
          -> (type : STLC ctxt paramTyType)
          -> (term : STLC (ctxt +=         paramTy) bodyTy)
          -> (prf  : TyCheck paramTyType paramTy)
                  -> STLC  ctxt    (FuncTy paramTy  bodyTy)

      App : {paramTy, bodyTy : MTy VALUE}
         -> (func  : STLC ctxt (FuncTy paramTy bodyTy))
         -> (value : STLC ctxt         paramTy)
                  -> STLC ctxt                 bodyTy

      -- Type Constructors
      TyFunc : {paramMTy, returnMTy : MTy TYPE}
            -> (paramTy  : STLC ctxt paramMTy)
            -> (returnTy : STLC ctxt returnMTy)
                        -> STLC ctxt (FuncTy paramMTy returnMTy)

namespace Renaming

  public export
  weaken : (func : Types.Elem old type
                -> Types.Elem new type)
        -> (Elem (old += type') type
         -> Types.Elem (new += type') type)
  weaken func (H (Same Refl Refl)) = H (Same Refl Refl)
  weaken func (T rest) = T (func rest)

  public export
  rename : (f : {level : Level}
             -> {type  : MTy level}
                      -> Types.Elem old type
                      -> Types.Elem new type)
        -> ({level : Level}
         -> {type : MTy level}
         -> STLC old type
         -> STLC new type)

  -- STLC
  rename f (Var idx) = Var (f idx)

  rename f (Func ty body prf)
    = Func (rename f ty) (rename (weaken f) body) prf

  rename f (App func param)
    = App (rename f func) (rename f param)

  -- Type Constructors
  rename f (TyFunc param body)
    = TyFunc (rename f param) (rename f body)


namespace Substitution
  public export
  weakens : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> STLC new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> Types.Elem (old += type') type
                   -> STLC (new += type') type)
  weakens f (H (Same Refl Refl)) = Var (H (Same Refl Refl))
  weakens f (T rest) = rename T (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> STLC new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> STLC old type
                   -> STLC new type)

    -- STLC
    subst f (Var idx) = f idx

    subst f (Func type body prf)
      = Func (subst f type)
             (subst (weakens f) body)
             prf

    subst f (App func var)
      = App (subst f func) (subst f var)

    -- Types
    subst f (TyFunc param return)
      = TyFunc (subst f param) (subst f return)

  namespace Single
    public export
    apply : {levelA : Level}
         -> {typeA  : MTy levelA}
         -> (this   : STLC ctxt typeB)
         -> (idx    : Elem (ctxt += typeB) typeA)
                   -> STLC ctxt typeA
    apply this (H (Same Refl Refl)) = this
    apply this (T rest) = Var rest

    public export
    subst : {levelA,levelB : Level}
         -> {typeA         : MTy levelA}
         -> {typeB         : MTy levelB}
         -> (this          : STLC  ctxt           typeB)
         -> (inThis        : STLC (ctxt += typeB) typeA)
                          -> STLC  ctxt           typeA
    subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
      = General.subst (apply this) inThis


namespace Values

  public export
  data Value : STLC ctxt type -> Type where
    FuncV : {body : STLC (ctxt += paramTy) bodyTy}
                 -> Value (Func type body prf)

    TyFuncV : {param : STLC ctxt pty}
           -> {return : STLC ctxt rty}
           -> Value param
           -> Value return
           -> Value (TyFunc param return)

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
                        -> {func       : STLC ctxt (FuncTy type return)}
                        -> (value      : Value func)
                        -> (var        : Redux this that)
                                      -> Redux (App func this)
                                               (App func that)

      ReduceFuncApp : (value : Value var)
                            -> Redux (App (Func type body prf) var)
                                     (subst var body)

      -- Simplify Function Types
      SimplifyTyFuncParam : (param : Redux this that)
                                  -> Redux (TyFunc this body)
                                           (TyFunc that body)

      SimplifyTyFuncBody : {this, that : STLC ctxt type}
                        -> {param      : STLC ctxt paramTy}
                        -> (value      : Value param)
                        -> (body       : Redux this that)
                                      -> Redux (TyFunc param this)
                                               (TyFunc param that)


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

  progress (Func type body prf) = Done FuncV

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Func ty b prf) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  -- Type Constructors

  progress (TyFunc param return) with (progress param)
    progress (TyFunc param return) | (Done valueP) with (progress return)
      progress (TyFunc param return) | (Done valueP) | (Done valueR)
        = Done (TyFuncV valueP valueR)
      progress (TyFunc param return) | (Done valueP) | (Step prfR)
        = Step (SimplifyTyFuncBody valueP prfR)
    progress (TyFunc param return) | (Step prfP)
      = Step (SimplifyTyFuncParam prfP)

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
