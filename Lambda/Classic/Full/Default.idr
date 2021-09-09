||| Intrinsically-typed STLC.
|||
module Lambda.Classic.Full.Default

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
    TyFuncD : (param, return : Ty) -> Ty
    TyNat : Ty
    TyBool : Ty

  public export
  Context : Type
  Context = List Ty

  public export
  data NotNat : Ty -> Type where
    IsBool  : NotNat TyBool
    IsFunc  : NotNat b -> NotNat (TyFunc  TyBool b)
    IsFuncD : NotNat b -> NotNat (TyFuncD TyNat  b)

namespace Terms

    public export
    data STLC : Context -> Ty -> Type where
      -- STLC

      Var : Elem type ctxt -> STLC ctxt type

      MkNat : Nat ->  STLC ctxt TyNat
      MkBool : Bool -> STLC ctxt TyBool

      Func : {ctxt : List Ty}
          -> (term : STLC (ctxt +=         TyBool) bodyTy)
          -> (prf  : NotNat  bodyTy)
                  -> STLC  ctxt    (TyFunc TyBool  bodyTy)

      FuncD : {ctxt : List Ty}
           -> (def     : STLC ctxt TyNat)
           -> (term : STLC (ctxt +=         TyNat) bodyTy)
           -> (prf  : NotNat  bodyTy)
                  -> STLC  ctxt    (TyFuncD TyNat  bodyTy)

      App : {bodyTy : Ty}
         -> (func   : STLC ctxt (TyFunc TyBool bodyTy))
         -> (value  : STLC ctxt         TyBool)
                   -> STLC ctxt                 bodyTy

      AppOver : {bodyTy : Ty}
             -> (func   : STLC ctxt (TyFuncD TyNat bodyTy))
             -> (value  : STLC ctxt TyNat)
                       -> STLC ctxt                  bodyTy

      AppDef : {bodyTy : Ty}
           -> (func  : STLC ctxt (TyFuncD TyNat bodyTy))
                    -> STLC ctxt                  bodyTy
namespace AST

  public export
  data AST = Var String
           | Func String Ty AST
           | App AST AST

Rename Ty STLC where
  var = Var

  -- STLC
  rename f (Var idx) = Var (f idx)
  rename f (MkNat n) = MkNat n
  rename f (MkBool b) = MkBool b

  rename f (Func body prf)
    = Func  (rename (weaken f) body) prf

  rename f (FuncD def body prf)
    = FuncD  (rename f def) (rename (weaken f) body) prf

  rename f (App func param)
    = App (rename f func) (rename f param)

  rename f (AppOver func param)
    = AppOver (rename f func) (rename f param)

  rename f (AppDef func)
    = AppDef (rename f func)


Substitute Ty STLC where
  subst f (Var idx) = f idx
  subst f (MkBool b) = MkBool b
  subst f (MkNat n)  = MkNat n
  subst f (Func  body prf)
    = Func
           (subst (weakens f) body)
           prf

  subst f (FuncD  def body prf)
    = FuncD
           (subst f def)
           (subst (weakens f) body)
           prf

  subst f (App func var)
    = App (subst f func) (subst f var)

  subst f (AppOver func var)
    = AppOver (subst f func) (subst f var)

  subst f (AppDef func)
    = AppDef (subst f func)



namespace Terms

  mutual
    namespace Neutral

      public export
      data IsVar : Ty -> Type where
        IsB : Neutral.IsVar TyNat
        IsF : Neutral.IsVar (TyFuncD TyNat b)

      public export
      data Term : STLC ctxt type -> Type where

        Var : {idx : Elem type ctxt}
           -> (prf : Neutral.IsVar type)
                  -> Neutral.Term (Var idx)

        AppDef : Neutral.Term func
              -> Neutral.Term (AppDef func)

        AppOver : Neutral.Term func
               -> Normal.Term  var
               -> Neutral.Term (AppOver func var)

    namespace Normal

      public export
      data IsVar : Ty -> Type where
        IsB : Normal.IsVar TyBool
        IsF : Normal.IsVar b -> Normal.IsVar (TyFunc TyBool b)

      public export
      data Term : STLC ctxt type -> Type where
        Neutral : Neutral.Term m
               -> Normal.Term  m

        Var : {idx : Elem type ctxt}
           -> (prf : Normal.IsVar type)
                  -> Normal.Term (Var idx)

        App : {func : STLC ctxt (TyFunc TyBool type)}
           -> {var  : STLC ctxt TyBool}
           -> Normal.Term func
           -> Normal.Term var
           -> Normal.Term (App func var)

        MkNat : Normal.Term (MkNat n)
        MkBool : Normal.Term (MkBool b)

        Fun : {body : STLC (TyBool::ctxt) typeB}
           -> Normal.Term body
           -> Normal.Term (Func body prf)

        FuncD : Normal.Term (FuncD def body prf)

  export
  varType : (type : Ty) -> Either (Neutral.IsVar type)
                                  (Normal.IsVar  type)
namespace Reduction

  public export
  data Redux : {type      : Ty}
            -> {ctxt      : List Ty}
            -> (this,that : STLC ctxt type)
                         -> Type
    where
      -- Functions with Defaults reduce
      SimplifyFuncDAppFunc : (func : Redux this that)
                                  -> Redux (AppDef this)
                                           (AppDef that)

      ReduceFuncDApp : {ctxt : List Ty}
                    -> {body : STLC (ctxt += TyNat) return}
                    -> {def  : STLC  ctxt    TyNat}
                            -> Redux (AppDef (FuncD def body prf))
                                     (Single.subst def body)

      RewriteAppDef : {body : STLC (ctxt += TyNat) return}
                   -> {def : STLC ctxt TyNat}
                   -> Redux (AppDef (FuncD def body prf))
                            (AppOver (FuncD def body prf) def)

      -- Functions with Defaults can be overridden
      SimplifyFuncAppFunc : (func : Redux this that)
                                 -> Redux (AppOver this var)
                                          (AppOver that var)

      SimplifyFuncAppVar : {this, that : STLC ctxt TyNat}
                        -> {func       : STLC ctxt (TyFuncD TyNat return)}
                        -> (var        : Redux this that)
                                      -> Redux (AppOver func this)
                                               (AppOver func that)

      ReduceFuncApp : {ctxt : List Ty}
                   -> {body : STLC (ctxt += TyNat) return}
                   -> {var  : STLC  ctxt    TyNat}
                   -> {def  : STLC  ctxt    TyNat}

                            -> Redux (AppOver (FuncD def body prf) var)
                                     (Single.subst var body)

      SimplifyAppFunc : Redux this that
                     -> Redux (App this var)
                              (App this var)
      SimplifyAppVar : Redux this that
                    -> Redux (App func this)
                             (App func that)
      SimplifyFuncBody : Redux this that
                      -> Redux (Func this prf)
                               (Func that prf)


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
  progress {type = type} (Var idx) with (varType type)
    progress {  type = type} (Var idx) | (Left x) = Done (Neutral (Var x))
    progress {  type = type} (Var idx) | (Right x) = Done (Var x)

  progress {type = TyNat} (MkNat k) = Done MkNat
  progress {type = TyBool} (MkBool x) = Done MkBool

  progress {type = (TyFunc TyBool bodyTy)} (Func term prf) with (progress term)
    progress {type = (TyFunc TyBool bodyTy)} (Func term prf) | (Done x)
      = Done (Fun x)

    progress {type = (TyFunc TyBool bodyTy)} (Func term prf) | (Step s)
      = Step (SimplifyFuncBody s)

  progress {type = (TyFuncD TyNat bodyTy)} (FuncD def term prf)
    = Done FuncD

  progress {type = type} (App func value) with (progress func)
    progress {type = type} (App func value) | (Done x) with (progress value)
      progress {type = type} (App func value) | (Done x) | (Done y)
        = Done (App x y)
      progress {type = type} (App func value) | (Done x) | (Step prf)
        = Step (SimplifyAppVar prf)
    progress {type = type} (App func value) | (Step prf)
      = Step (SimplifyAppFunc prf)

  progress {type = type} (AppOver func value) with (progress func)
    progress {type = type} (AppOver func value) | (Done (Neutral x)) with (progress value)
      progress {type = type} (AppOver func value) | (Done (Neutral x)) | (Done y)
        = Done (Neutral (AppOver x y))
      progress {type = type} (AppOver func value) | (Done (Neutral x)) | (Step prf)
        = Step (SimplifyFuncAppVar prf)

    progress {type = type} (AppOver (Var idx) value) | (Done (Var prf)) with (prf)
      progress {type = type} (AppOver (Var idx) value) | (Done (Var prf)) | _ impossible

    progress {type = type} (AppOver (App func var) value) | (Done (App x y)) with (progress value)
      progress {  type = type} (AppOver (App func var) value) | (Done (App x y)) | (Done z) = ?rhs_appover_app --Done (Neutral (AppOver (App x y) z))
      progress {  type = type} (AppOver (App func var) value) | (Done (App x y)) | (Step prf)
        = Step (SimplifyFuncAppVar prf)
--      = Done (Neutral (AppOver (App x y) value))

    progress {type = type} (AppOver (FuncD def body prf) value) | (Done FuncD) with (progress value)
      progress {type = type} (AppOver (FuncD def body prf) value) | (Done FuncD) | (Done x)
        = Step ReduceFuncApp
      progress {type = type} (AppOver (FuncD def body prf) value) | (Done FuncD) | (Step x)
        = Step (SimplifyFuncAppVar x)
    progress {type = type} (AppOver func value) | (Step prf)
      = Step (SimplifyFuncAppFunc prf)


  progress {type = type} (AppDef func) with (progress func)
    progress {type = type} (AppDef func) | (Done (Neutral x))
      = Done (Neutral (AppDef x))
    progress {type = type} (AppDef (Var idx)) | (Done (Var prf)) with (prf)

      progress {type = type} (AppDef (Var idx)) | (Done (Var prf)) | _ impossible

    progress {type = type} (AppDef (App func var)) | (Done (App x y))
      = ?rhs_appdef_app
--      = Done (Neutral ?rhs_app)

    progress {type = type} (AppDef (FuncD def body prf)) | (Done FuncD)
      = Step ReduceFuncDApp
    progress {type = type} (AppDef func) | (Step prf)
      = Step (SimplifyFuncDAppFunc prf)

  -- progress (App f@(App func x) value) with (progress f)                            --
  --   progress (App f@(App func x) value) | (Done (Neutral y)) with (progress value) --
  --     progress (App f@(App func x) value) | (Done (Neutral y)) | (Done z)          --
  --       = Done (Neutral (App y z))                                                 --
  --     progress (App f@(App func x) value) | (Done (Neutral y)) | (Step prf)        --
  --       = Step (SimplifyFuncAppVar prf)                                            --
  --   progress (App f@(App func x) value) | (Step prf)                               --
  --     = Step (SimplifyFuncAppFunc prf)                                             --

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
