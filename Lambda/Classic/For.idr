||| Intrinsically-typed STLC.
|||
module Lambda.Classic.For

import Data.Vect
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
    TyUnit : Ty
    TyNat  : Ty
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

      MkNat  : (n : Nat) -> STLC ctxt TyNat
      MkUnit : STLC ctxt TyUnit

      Seq : STLC ctxt TyUnit
         -> STLC ctxt type
         -> STLC ctxt type

      For : STLC ctxt TyNat
         -> STLC ctxt (TyFunc TyNat TyUnit)
         -> STLC ctxt TyUnit


namespace AST

  public export
  data AST = Var String
           | Func String Ty AST
           | App AST AST
           | MkNat Nat
           | For AST AST
           | Seq AST AST
           | MkUnit

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

  rename f (MkUnit) = MkUnit

  rename f (Seq left right) = Seq (rename f left) (rename f right)
  rename f (For n body) = For (rename f n) (rename f body)


Substitute Ty STLC where
  subst f (Var idx) = f idx

  subst f (Func type body)
    = Func type
           (subst (weakens f) body)


  subst f (App func var)
    = App (subst f func) (subst f var)

  subst f (MkNat n) = MkNat n
  subst f MkUnit = MkUnit
  subst f (Seq left right) = Seq (subst f left) (subst f right)
  subst f (For n body) = For (subst f n) (subst f body)

public export
data Value : STLC ctxt type -> Type where

  Func : {body : STLC (ctxt += type) bodyTy}
              -> Value (Func type body)

  MkNat : Value (MkNat n)
  MkUnit : Value MkUnit
  Seq : Value left -> Value right -> Value (Seq left right)

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

    SimplifyFuncAppFuncSeq : Redux this that
                          -> Redux (App (Seq left this)
                                        var)
                                   (App (Seq left that)
                                        var)

    RewriteFuncAppFuncSeqSeq : Redux (App (Seq left (Seq x y))
                                          var)
                                     (Seq left (Seq x (App y var)))

    RewriteFuncAppFuncSeq : Redux (App (Seq left (Func type body))
                                       var)
                                  (Seq left (App (Func type body) var))

    ReduceFuncApp : {type : Ty}
                 -> {body : STLC (ctxt += type) return}
                 -> {var  : STLC  ctxt    type}
                 -> (value : Value var)
                          -> Redux (App (Func type body) var)
                                   (Single.subst var body)

    SimplifySeqLeft : Redux this that
                   -> Redux (Seq this right) (Seq that right)

    SimplifySeqRight : Value left
                    -> Redux this that
                    -> Redux (Seq left this) (Seq left that)

    RewriteSeqLeft : Redux (Seq (Seq x y) right)
                           (Seq x (Seq y right))

    SimplifyForCounter : Redux this that
                      -> Redux (For this body) (For that body)

    RewriteForCounter : Redux (For (Seq left right) body)
                              (Seq left (For right body))

    RewriteForZ : Redux (For (MkNat Z) body)
                        (App body (MkNat Z))

    RewriteForS : Redux (For (MkNat (S n)) body)
                        (Seq (For (MkNat n) body)
                             (App body (MkNat (S n)))
                             )

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

  progress (Func type body) = Done Func

  progress (App func var) with (progress func)
    progress (App (Func paramTy body) var) | (Done Func) with (progress var)

      progress (App (Func paramTy body) var) | (Done Func) | (Done varV)
        = Step (ReduceFuncApp varV)

      progress (App (Func paramTy body) var) | (Done Func) | (Step step)
        = Step (SimplifyFuncAppVar Func step)

    progress (App (Seq left right) var) | (Done (Seq x y)) with (progress right)
      progress (App (Seq left (Func paramTy body)) var) | (Done (Seq x y)) | (Done Func)
        = Step (RewriteFuncAppFuncSeq)

      progress (App (Seq urgh (Seq left right)) var) | (Done (Seq x y)) | (Done (Seq z w))
        = Step (RewriteFuncAppFuncSeqSeq)

      progress (App (Seq left right) var) | (Done (Seq x y)) | (Step prf)
        = Step (SimplifyFuncAppFuncSeq prf)

    progress (App func var) | (Step step)
      = Step (SimplifyFuncAppFunc step)

  progress (MkNat n) = Done MkNat
  progress MkUnit = Done MkUnit

  progress (For counter body) with (progress counter)
    progress (For (MkNat Z) body) | (Done MkNat)
      = Step RewriteForZ

    progress (For (MkNat (S k)) body) | (Done MkNat)
      = Step RewriteForS

    progress (For (Seq left right) body) | (Done (Seq x y))
      = Step RewriteForCounter

    progress (For counter body) | (Step step)
      = (Step (SimplifyForCounter step))

  progress (Seq left right) with (progress left)
    progress (Seq MkUnit right) | (Done MkUnit) with (progress right)
      progress (Seq MkUnit right) | (Done MkUnit) | (Done val)
        = Done (Seq MkUnit val)

      progress (Seq MkUnit right) | (Done MkUnit) | (Step step)
        = Step (SimplifySeqRight MkUnit step)

    progress (Seq (Seq x y) right) | (Done (Seq xV yV))
      = Step RewriteSeqLeft

    progress (Seq left right) | (Step step)
      = Step (SimplifySeqLeft step)

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

  nNotU : TyNat === TyUnit -> Void
  nNotU Refl impossible

  nNotF : TyNat === TyFunc p r -> Void
  nNotF Refl impossible

  uNotF : TyUnit === TyFunc p r -> Void
  uNotF Refl impossible

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
    decEq TyNat TyNat = Yes Refl
    decEq TyNat (TyFunc z w) = No nNotF
    decEq TyNat TyUnit = No nNotU

    decEq TyUnit TyUnit = Yes Refl
    decEq TyUnit TyNat = No (negEqSym nNotU)
    decEq TyUnit (TyFunc p r) = No uNotF

    decEq (TyFunc p r) TyUnit = No (negEqSym uNotF)
    decEq (TyFunc p r) TyNat = No (negEqSym nNotF)

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

  check env (MkNat n) = Just (_ ** MkNat n)
  check env MkUnit = Just (_ ** MkUnit)

  check env (Seq l r) with (check env l)
    check env (Seq l r) | Nothing
      = Nothing

    check env (Seq l r) | (Just (MkDPair TyUnit lTerm)) with (check env r)
      check env (Seq l r) | (Just (MkDPair TyUnit lTerm)) | Nothing
        = Nothing
      check env (Seq l r) | (Just (MkDPair TyUnit lTerm)) | (Just (MkDPair type rterm))
        = Just (_ ** Seq lTerm rterm)

    check env (Seq l r) | (Just (MkDPair fst snd))
      = Nothing

  --check env (App (Func "()" TyUnit r) l)

  check env (For n body) with (check env n)
    check env (For n body) | Nothing
      = Nothing
    check env (For n body) | (Just (MkDPair TyNat snd)) with (check env body)
      check env (For n body) | (Just (MkDPair TyNat nterm)) | Nothing
        = Nothing
      check env (For n body) | (Just (MkDPair TyNat nterm)) | (Just (MkDPair (TyFunc TyNat TyUnit) bodyTerm))
        = Just (_ ** For nterm bodyTerm)

      check env (For n body) | (Just (MkDPair TyNat nterm)) | (Just (MkDPair _ x))
        = Nothing


    check env (For n body) | (Just (MkDPair _ snd))
      = Nothing
  --check env (rep n body)

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

namespace Example

  export
  example0 : AST
  example0 = For (MkNat 5) (Func "i" TyNat (Seq MkUnit MkUnit))

  export
  example1 : AST
  example1 = App (Func "i" TyNat (Seq MkUnit MkUnit)) (MkNat 3)

  export
  example2 : AST
  example2 = (Seq (Seq MkUnit MkUnit) (Seq MkUnit MkUnit))

  export
  example3 : AST
  example3 = Seq (For (MkNat Z) (Func "i" TyNat (Seq MkUnit MkUnit)))
                 (App (Func "i" TyNat (Seq MkUnit MkUnit)) (MkNat 3))


-- --------------------------------------------------------------------- [ EOF ]
