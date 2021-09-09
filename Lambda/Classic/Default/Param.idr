||| A Default Calculus in which some arguments are presented with default values.
|||
||| Compile Time Safe and Runtime Unsafe
module Lambda.Classic.Default.Param

import Decidable.Equality

import Data.List.Elem
import Data.Nat
import Data.DPair
import Data.Fuel

import Toolkit.Decidable.Equality.Indexed

import Lambda.Common

%default total

namespace Types
  public export
  data Ty = TyParam Nat | TyNat | TyFunc Ty Ty


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

    AppDef : {n : Nat}
          -> {r  : Ty}
          -> (func : Term ctxt (TyFunc (TyParam n) r))
                  -> Term ctxt                     r

    AppOver : {n,m : Nat}
           -> {r   : Ty}
           -> (fun : Term ctxt (TyFunc (TyParam n) r))
           -> (arg : Term ctxt         (TyParam m))
                  -> Term ctxt                     r

    MkNat : (n : Nat)
              -> Term ctxt TyNat

    ToNat : {n : Nat}
              -> Term ctxt (TyParam n)
              -> Term ctxt TyNat

    MkParam : (n : Nat)
                -> Term ctxt (TyParam n)

    -- The trick and only appears at runtime or as args in AppOver
    Override : (n : Nat)
                 -> Term ctxt (TyParam m)


  namespace Undecorated

    public export
    data AST = Var String
             | Fun String Ty AST
             | App AST AST
             | MkNat Nat
             | ToNat AST
             | MkParam Nat
             | AppDef AST
             | AppOver AST AST

namespace Types

  pNotN : TyParam k === TyNat -> Void
  pNotN Refl impossible

  pIdx : (contra : i === k -> Void)
      -> TyParam i === TyParam k
      -> Void
  pIdx contra Refl = contra Refl

  pNotFunc : TyParam i === TyFunc p r -> Void
  pNotFunc Refl impossible

  nNotF : TyNat === TyFunc p r -> Void
  nNotF Refl impossible

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
    decEq (TyParam k) (TyParam j) with (decEq k j)
      decEq (TyParam k) (TyParam k) | (Yes Refl) = Yes Refl
      decEq (TyParam k) (TyParam j) | (No contra)
        = No (pIdx contra)

    decEq (TyParam k) TyNat = No pNotN

    decEq (TyParam k) (TyFunc x y)
      = No pNotFunc

    decEq TyNat (TyParam k) = No (negEqSym pNotN)
    decEq TyNat TyNat = Yes Refl

    decEq TyNat (TyFunc x y) = No nNotF

    decEq (TyFunc x y) (TyParam k) = No (negEqSym pNotFunc)
    decEq (TyFunc x y) TyNat = No (negEqSym nNotF)

    decEq (TyFunc x y) (TyFunc z w) with (decEq x z)
      decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) with (decEq y w)
        decEq (TyFunc x w) (TyFunc x w) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) | (No contra)
          = No (fR contra)
      decEq (TyFunc x y) (TyFunc z w) | (No contra)
        = No (fP contra)


namespace TypeChecking
  namespace Env

    data Item : Ty -> Type where
      MkItem : (name : String)
            -> (ty   : Ty)
                    -> Item ty

    export
    data Env : List Ty -> Type
      where
        Empty : Env Nil
        Cons : Item ty -> Env rest -> Env (ty :: rest)

    export
    empty : Env Nil
    empty = Empty

    export
    extend : (name : String)
          -> (type : Ty)
          -> (env  : Env rest)
                  -> Env (type::rest)
    extend name type env = Cons (MkItem name type) env

    export
    getType : String -> Env tys -> Maybe (type ** Elem type tys)
    getType x Empty = Nothing
    getType x (Cons (MkItem y ty) z) with (decEq x y)
      getType y (Cons (MkItem y ty) z) | (Yes Refl) = Just (ty ** Here)
      getType x (Cons (MkItem y ty) z) | (No contra) with (getType x z)
        getType x (Cons (MkItem y ty) z) | (No contra) | Nothing = Nothing
        getType x (Cons (MkItem y ty) z) | (No contra) | (Just (MkDPair fst orf)) = Just (fst ** There orf)


  namespace Checker

    export
    check : (env  : Env ctxt)
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

    check env (MkNat k)
      = Just (_ ** MkNat k)

    check env (ToNat x) with (check env x)
      check env (ToNat x) | Nothing
        = Nothing
      check env (ToNat x) | (Just (MkDPair (TyParam k) snd))
        = Just ( _ ** ToNat snd)
      check env (ToNat x) | (Just (MkDPair _ snd))
        = Nothing

    -- 'Typing Rule'/'Rewrite' to insert
    check env (AppDef f) with (check env f)
      check env (AppDef f) | Nothing
        = Nothing
      check env (AppDef f) | (Just (MkDPair (TyFunc (TyParam k) y) snd))
        = Just (_ ** AppDef snd)

        -- Just (_ ** App snd (MkParam k))

      check env (AppDef f) | (Just (MkDPair (TyFunc _ y) snd))
        = Nothing
      check env (AppDef f) | (Just (MkDPair _ snd))
        = Nothing

    check env (AppOver forig aorig) with (check env forig)
      check env (AppOver forig aorig) | Nothing
        = Nothing
      check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) with (check env aorig)
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | Nothing
          = Nothing
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | (Just (MkDPair (TyParam m) a))
          = Just (_ ** AppOver f a)
        check env (AppOver forig aorig) | (Just (MkDPair (TyFunc (TyParam n) r) f)) | (Just (MkDPair _ _))
          = Nothing

      check env (AppOver forig aorig) | (Just (MkDPair _ _))
        = Nothing

    check env (MkParam n)
      = Just (_ ** MkParam n)


namespace Renaming

  public export
  rename : (f : {type  : Ty} -> Contains old type
                             -> Contains new type)
        -> ({type : Ty} -> Term old type
                        -> Term new type)

  -- Term
  rename f (Var idx)
    = Var (f idx)

  rename f (Fun ty body)
    = Fun ty (rename (weaken f) body)

  rename f (App func param)
    = App (rename f func) (rename f param)

  rename f (AppDef func)
    = AppDef (rename f func)

  rename f (AppOver func param)
    = AppOver (rename f func) (rename f param)

  rename f (MkNat n)
    = MkNat n

  rename f (ToNat p)
    = ToNat (rename f p)

  rename f (MkParam n)
    = MkParam n

  rename f (Override n)
    = Override n

namespace Substitution
  public export
  weakens : (f : {type  : Ty}
                       -> Contains old type
                       -> Term     new type)
         -> ({type  : Ty}
                   -> Contains (old += type') type
                   -> Term     (new += type') type)
  weakens f Here = Var Here
  weakens f (There rest) = rename There (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {type  : Ty}
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

    subst f (AppDef func)
      = AppDef (subst f func)

    subst f (AppOver func arg)
      = AppOver (subst f func) (subst f arg)

    subst f (MkNat n)
      = MkNat n

    subst f (ToNat m)
      = ToNat (subst f m)

    subst f (MkParam n)
      = MkParam n

    subst f (Override m)
      = Override m


  namespace Single
    public export
    apply : {typeA  : Ty}
         -> (this   : Term      ctxt    typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> Term      ctxt           typeA
    apply this Here = this
    apply this (There rest) = Var rest

    public export
    subst : {typeA         : Ty}
         -> {typeB         : Ty}
         -> (this          : Term  ctxt           typeB)
         -> (inThis        : Term (ctxt += typeB) typeA)
                          -> Term  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis
      = General.subst (apply this) inThis


namespace Values

  public export
  data Value : Term ctxt type -> Type where

    Fun : {body : Term (ctxt += type) bodyTy}
                -> Value (Fun type body)

    MkNat : Value (MkNat n)
    MkParam : Value (MkParam n)
    Override : Value (Override m)

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

      SimplifyAppDef : Redux this that
                    -> Redux (AppDef this) (AppDef that)

      RewriteAppDef : Redux (AppDef (Fun (TyParam n) body))
                            (App (Fun (TyParam n) body) (MkParam n))

      SimplifyAppOverFunc : Redux this that
                         -> Redux (AppOver this arg)
                                  (AppOver that arg)

      SimplifyAppOverArg : Value func
                        -> Redux this that
                        -> Redux (AppOver func this) (AppOver func that)

      ReduceFuncAppOverP : Redux (AppOver (Fun (TyParam a) body) (MkParam m))
                                 (Single.subst (Override {m=a} m) body)

      ReduceFuncAppOverO : Redux (AppOver (Fun (TyParam n) body) (Override m))
                                 (Single.subst (Override m) body)

      SimplifyToNat : Redux this that
                   -> Redux (ToNat this) (ToNat that)

      ReduceToNatP : Redux (ToNat (MkParam  p)) (MkNat p)
      ReduceToNatO : Redux (ToNat (Override p)) (MkNat p)

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

  progress (Fun type body) = Done Fun

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Fun ty b) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  progress (AppDef func) with (progress func)
    progress (AppDef (Fun (TyParam n) body)) | (Done Fun)
      = Step RewriteAppDef

    progress (AppDef func) | (Step step)
      = Step (SimplifyAppDef step)

  progress (AppOver func param) with (progress func)
    progress (AppOver func param) | (Done valueD) with (progress param)
      progress (AppOver (Fun (TyParam n) body) (MkParam m)) | (Done Fun) | (Done MkParam)
        = Step (ReduceFuncAppOverP)
      progress (AppOver (Fun (TyParam n) body) (Override m)) | (Done Fun) | (Done Override)
        = Step ReduceFuncAppOverO

      progress (AppOver func param) | (Done valueD) | (Step step)
        = Step (SimplifyAppOverArg valueD step)

    progress (AppOver func param) | (Step step)
      = Step (SimplifyAppOverFunc step)

  progress (MkNat n) = Done MkNat

  progress (ToNat p) with (progress p)
    progress (ToNat (MkParam n)) | (Done MkParam)
      = Step ReduceToNatP
    progress (ToNat (Override m)) | (Done Override)
      = Step ReduceToNatO
    progress (ToNat p) | (Step step)
      = Step (SimplifyToNat step)

  progress (MkParam n) = Done MkParam

  progress (Override n) = Done Override

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
    = App (Fun "x" (TyParam 3)
               (ToNat (Var "x")))
          (MkParam 2) -- Fails

  export
  example1 : AST
  example1
    = AppDef (Fun "x" (TyParam 3)
                  (ToNat (Var "x")))

  export
  example2 : AST
  example2
    = AppOver (Fun "x" (TyParam 3)
                  (ToNat (Var "x")))
              (MkParam 2)
