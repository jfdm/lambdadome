||| A Default Calculus in which some arguments are presented with default values.
|||
||| Compile Time Safe and Runtime Unsafe
module Lambda.Classic.Default

import Decidable.Equality

import Data.List.Elem
import Data.Nat
import Data.DPair
import Data.Fuel

import Toolkit.Decidable.Equality.Indexed

import Lambda.Common
import Lambda.Classic.Common

%default total

namespace Types
  public export
  data Ty =  TyNat
           | TyFunc  Ty Ty
           | TyFuncD Ty Ty

namespace Terms
  public export
  data Term : List Ty -> Ty -> Type where
    Var : (idx : Elem type ctxt)
              -> Term ctxt type

    Fun : (type_param : Ty)
       -> (body       : Term (type_param::ctxt) type_ret)
                     -> Term ctxt (TyFunc type_param type_ret)

    App : {p,r  : Ty}
       -> (func : Term ctxt (TyFunc p r))
       -> (arg  : Term ctxt         p)
               -> Term ctxt           r

    FunD : (type_param : Ty)
        -> (def        : Term  ctxt    type_param)
        -> (body       : Term (ctxt += type_param) type_ret)
                      -> Term  ctxt (TyFuncD type_param type_ret)

    AppDef : {param,r : Ty}
          -> (func : Term ctxt (TyFuncD param r))
                  -> Term ctxt                r

    AppOver : {param,r : Ty}
           -> (func    : Term ctxt (TyFuncD param r))
           -> (arg     : Term ctxt          param   )
                      -> Term ctxt                r

    MkNat : (n : Nat)
              -> Term ctxt TyNat


  namespace Undecorated

    public export
    data AST = Var String
             | Fun  String Ty AST
             | FunD String Ty AST AST
             | App AST AST
             | MkNat Nat
             | AppDef AST

namespace Types

  nNotF : TyNat === TyFunc p r -> Void
  nNotF Refl impossible

  nNotFd : TyNat === TyFuncD p r -> Void
  nNotFd Refl impossible

  fP : (contra : a === b -> Void)
    -> TyFunc a y === TyFunc b w
    -> Void
  fP contra Refl = contra Refl

  fR : (contra : y === w -> Void)
    -> TyFunc a y === TyFunc a w
    -> Void
  fR contra Refl = contra Refl

  fdP : (contra : a === b -> Void)
     -> TyFuncD a y === TyFuncD b w
     -> Void
  fdP contra Refl = contra Refl

  fdR : (contra : y === w -> Void)
     -> TyFuncD a y === TyFuncD a w
     -> Void
  fdR contra Refl = contra Refl

  fNotD : TyFunc x y === TyFuncD a b
       -> Void
  fNotD Refl impossible

  export
  DecEq Ty where
    decEq TyNat TyNat = Yes Refl
    decEq TyNat (TyFunc  x y) = No nNotF
    decEq TyNat (TyFuncD x y) = No nNotFd

    decEq (TyFunc x y) (TyFuncD a b) = No fNotD

    decEq (TyFunc x y) TyNat = No (negEqSym nNotF)

    decEq (TyFunc x y) (TyFunc z w) with (decEq x z)
      decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) with (decEq y w)
        decEq (TyFunc x w) (TyFunc x w) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) | (No contra)
          = No (fR contra)
      decEq (TyFunc x y) (TyFunc z w) | (No contra)
        = No (fP contra)

    decEq (TyFuncD x y) TyNat = No (negEqSym nNotFd)
    decEq (TyFuncD x y) (TyFunc a b) = No (negEqSym fNotD)

    decEq (TyFuncD x y) (TyFuncD z w) with (decEq x z)
      decEq (TyFuncD x y) (TyFuncD x w) | (Yes Refl) with (decEq y w)
        decEq (TyFuncD x w) (TyFuncD x w) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (TyFuncD x y) (TyFuncD x w) | (Yes Refl) | (No contra)
          = No (fdR contra)
      decEq (TyFuncD x y) (TyFuncD z w) | (No contra)
        = No (fdP contra)

namespace TypeChecking

  export
  check : (env  : Env Ty ctxt)
       -> (ast  : AST)
               -> Maybe (type ** Term ctxt type)
  check env (Var x)
    = do (type ** prf) <- getType x env
         pure (type ** Var prf)

  check env (Fun name type body) with (check (extend name type env) body)
    check env (Fun name type body) | Nothing
      = Nothing
    check env (Fun name type body) | (Just (MkDPair fst snd))
      = Just (_ ** Fun type snd)

  check env (FunD name type def body) with (check env def)
    check env (FunD name type def body) | Nothing
      = Nothing
    check env (FunD name type def body) | (Just (MkDPair fst def')) with (decEq type fst)
      check env (FunD name fst def body) | (Just (MkDPair fst def')) | (Yes Refl) with (check (extend name fst env) body)
        check env (FunD name fst def body) | (Just (MkDPair fst def')) | (Yes Refl) | Nothing
          = Nothing
        check env (FunD name fst def body) | (Just (MkDPair fst def')) | (Yes Refl) | (Just (MkDPair x body'))
          = Just (_ ** FunD fst def' body')
      check env (FunD name type def body) | (Just (MkDPair fst def')) | (No contra)
        = Nothing

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

    check env (App x y) | (Just (MkDPair (TyFuncD paramTy returnTy) f)) with (check env y)
      check env (App x y) | (Just (MkDPair (TyFuncD paramTy returnTy) f)) | Nothing
        = Nothing
      check env (App x y) | (Just (MkDPair (TyFuncD paramTy returnTy) f)) | (Just (MkDPair paramTy' a)) with (decEq paramTy paramTy')
        check env (App x y) | (Just (MkDPair (TyFuncD paramTy' returnTy) f)) | (Just (MkDPair paramTy' a)) | (Yes Refl)
          = Just (_ ** AppOver f a)
        check env (App x y) | (Just (MkDPair (TyFuncD paramTy returnTy) f)) | (Just (MkDPair paramTy' a)) | (No contra)
          = Nothing

    check env (App x y) | (Just (MkDPair _ snd))
      = Nothing

  check env (MkNat k)
    = Just (_ ** MkNat k)

  -- 'Typing Rule'/'Rewrite' to insert
  check env (AppDef f) with (check env f)
    check env (AppDef f) | Nothing
      = Nothing
    check env (AppDef f) | (Just (MkDPair (TyFuncD k y) snd))
      = Just (_ ** AppDef snd)

    check env (AppDef f) | (Just (MkDPair (TyFunc _ y) snd))
      = Nothing
    check env (AppDef f) | (Just (MkDPair _ snd))
      = Nothing

namespace Renaming
  -- Term

  export
  Rename Ty Term where
    var = Var

    rename f (Var idx)
      = Var (f idx)

    rename f (Fun ty body)
      = Fun ty (rename (weaken f) body)

    rename f (App func param)
      = App (rename f func) (rename f param)

    rename f (FunD ty def body)
      = FunD ty (rename         f  def)
                (rename (weaken f) body)

    rename f (AppDef func)
      = AppDef (rename f func)

    rename f (AppOver func param)
      = AppOver (rename f func) (rename f param)

    rename f (MkNat n)
      = MkNat n


namespace Substitution

  subst : {old, new : List Ty}
       -> (f : {type  : Ty}
                     -> Contains old type
                     -> Term     new type)
       -> ({type  : Ty}
                 -> Term old type
                 -> Term new type)

  -- Term
  subst f (Var idx) = f idx

  subst f (Fun type body)
    = Fun type
          (subst (weakens f) body)

  subst f (App func var)
    = App (subst f func) (subst f var)

  subst f (FunD type def body)
    = FunD type
           (subst          f  def)
           (subst (weakens f) body)

  subst f (AppDef func)
    = AppDef (subst f func)

  subst f (MkNat n)
    = MkNat n

  subst f (AppOver func var)
    = AppOver (subst f func) (subst f var)

  export
  Substitute Ty Term where
    subst = Default.Substitution.subst

namespace Values

  public export
  data Value : Term ctxt type -> Type where

    Fun : {body : Term (ctxt += type) bodyTy}
                -> Value (Fun type body)

    FunD : {body : Term (ctxt += type) bodyTy}
                -> Value (FunD type def body)

    MkNat : Value (MkNat n)

namespace Reduction

  public export
  data Redux : (this : Term ctxt type)
            -> (that : Term ctxt type)
            -> Type
    where
      -- Functions reduce
      SimplifyFuncAppFunc : (func : Redux this that)
                                 -> Redux (App this var)
                                          (App that var)

      SimplifyFuncAppVar : {this, that : Term ctxt type}
                        -> {func       : Term ctxt (TyFunc type return)}
                        -> (value      : Value func)
                        -> (var        : Redux this that)
                                      -> Redux (App func this)
                                               (App func that)

      ReduceFuncApp : {type : Ty}
                   -> {body : Term (ctxt += type) return}
                   -> {var  : Term  ctxt    type}
                   -> (value : Value var)
                            -> Redux (App (Fun type body) var)
                                     (Single.subst var body)

      SimplifyAppOver : Redux this that
                     -> Redux (AppOver this var) (AppOver that var)

      RewriteAppOver : Redux (AppOver (FunD type def body) var)
                             (App (Fun type body) var)


      SimplifyAppDef : Redux this that
                    -> Redux (AppDef this) (AppDef that)

      RewriteAppDef : Redux (AppDef (FunD type def body))
                            (App (Fun type body) def)


namespace Progress
  public export
  data Progress : (term : Term Nil type)
                       -> Type
    where
      Done : forall mty . {term  : Term Nil mty}
                       -> (value : Value term)
                                -> Progress term

      Step : {this, that : Term Nil type}
          -> (step       : Redux this that)
                        -> Progress this

  public export
  progress : (term : Term Nil type)
          -> Progress term
  -- Term
  progress {type} (Var _) impossible

  progress (Fun  type     body) = Done Fun
  progress (FunD type def body) = Done FunD

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Fun ty b) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  progress (AppDef func) with (progress func)
    progress (AppDef (FunD ty def body)) | (Done FunD)
      = Step RewriteAppDef

    progress (AppDef func) | (Step step)
      = Step (SimplifyAppDef step)

  progress (AppOver func var) with (progress func)
    progress (AppOver (FunD ty def body) var) | (Done FunD)
      = Step RewriteAppOver

    progress (AppOver func var) | (Step step)
      = Step (SimplifyAppOver step)

  progress (MkNat n) = Done MkNat

namespace Evaluation

  public export
  data Reduces : (this : Term ctxt type)
              -> (that : Term ctxt type)
              -> Type
    where
      Refl  : {this : Term ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : Term ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : Term ctxt type)
                       -> Type
    where
      Normalised : {term : Term ctxt type}
                        -> Value term
                        -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : Term Nil type) -> Type where
    RunEval : {this, that : Term Nil type}
           -> (steps      : Inf (Reduces this that))
           -> (result     : Finished that)
                         -> Evaluate this

  export
  compute : forall type
          . (fuel : Fuel)
         -> (term : Term Nil type)
         -> Evaluate term
  compute Dry term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result


covering
run : forall type
    . (this : Term Nil type)
           -> Maybe (Subset (Term Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

data Result : Type
  where
    Error : Result

    MkRes : (  this : Term Nil type)
         -> (  that : Term Nil type)
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

namespace Examples
  export
  example0 : AST
  example0
    = App (Fun "x" (TyNat)
               ((Var "x")))
          (MkNat 2)

  export
  example1 : AST
  example1
    = AppDef (FunD "x" (TyNat) (MkNat 4)
                   (Var "x"))

  export
  example2 : AST
  example2
    = App (FunD "x" TyNat (MkNat 4)
                (Var "x"))
                (MkNat 2)
