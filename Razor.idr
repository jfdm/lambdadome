module Razor

import Data.List.Elem
import Data.Fuel

%default total

namespace Types

  public export
  data Ty = BOOL | NAT


namespace Terms

  public export
  data Term : List Ty -> Ty -> Type where
    Var : Elem type ctxt
       -> Term ctxt type

    B : Bool -> Term ctxt BOOL
    N : Nat  -> Term ctxt NAT

    Add : (l,r : Term ctxt NAT)
              -> Term ctxt NAT

    And : (l,r : Term ctxt BOOL)
              -> Term ctxt BOOL

    Let : {typeT,typeB : Ty}
       -> (this : Term ctxt typeT)
       -> (body : Term (typeT :: ctxt) typeB)
               -> Term ctxt typeB

  export
  example : Term Nil BOOL
  example
    = And (B True) (B False)

  -- export                         --
  -- example1 : Term Nil NAT        --
  -- example1                       --
  --   = Let example                --
  --         (Add (N 1) (Var Here)) --

  export
  example2 : Term Nil BOOL
  example2
    = Let example
          (And (B False) (Var Here))


namespace Renaming

  public export
  weaken : (func : Elem type old
                -> Elem type new )
        -> (Elem type (type' :: old)
         -> Elem type (type' :: new))

  weaken func Here = Here
  weaken func (There rest) = There (func rest)


  public export
  rename : {old, new : List Ty}

        -> (f : {ty : Ty} -> Elem ty old
                          -> Elem ty new)

        -> ({ty : Ty} -> Term old ty
                      -> Term new ty)

  rename f (Var x)
    = Var (f x)
  rename f (B x)
    = B x
  rename f (N k)
    = N k
  rename f (Add l r)
    = Add (rename f l) (rename f r)

  rename f (And l r)
    = And (rename f l) (rename f r)

  rename f (Let this body)
    = Let (rename f this) (rename (weaken f) body)

namespace Substitution

  public export
  weakens : {old, new : List Ty}

         -> (f : {ty : Ty}
               -> Elem ty old
               -> Term new ty)

         -> ({ty,type' : Ty}
                -> Elem ty  (type' :: old)
                -> Term     (type' :: new) ty)

  weakens f Here = Var Here
  weakens f (There rest) = rename There (f rest)

  namespace General

    public export
    subst : {old, new : List Ty}
         -> (f : {ty : Ty}
               -> Elem ty old
               -> Term new ty)
         -> ({ty : Ty}
                -> Term old ty
                -> Term new ty)
    subst f (Var x)
      = f x
    subst f (B x)
      = B x
    subst f (N k)
      = N k
    subst f (Add l r)
      = Add (subst f l) (subst f r)
    subst f (And l r)
      = And (subst f l) (subst f r)
    subst f (Let this body)
      = Let (subst f this) (subst (weakens f) body)

  namespace Single

    public export
    subst : {typeA,typeB : Ty}
         -> {ctxt : List Ty}
         -> (this          : Term           ctxt  typeB)
         -> (inThis        : Term (typeB :: ctxt) typeA)
                          -> Term           ctxt  typeA
    subst {ctxt} {typeA} {typeB} this inThis
        = General.subst (apply this) inThis

      where
        apply : {typeA,typeB : Ty}
             -> {ctxt        : List Ty}
             -> (this   : Term ctxt typeB)
             -> (idx    : Elem typeA (typeB :: ctxt))
                       -> Term ctxt typeA
        apply this Here = this
        apply this (There rest) = Var rest

namespace Value
  public export
  data Value : (term : Term ctxt type) -> Type where
    N : Value (N n)
    B : Value (B b)

namespace Reductions
  public export
  data Reduce : (this, that : Term ctxt type)
                           -> Type
    where
      -- Add
      SimplifyAddL : Reduce this that
                -> Reduce (Add this right) (Add that right)

      SimplifyAddR : Value left
                  -> Reduce this that
                  -> Reduce (Add left this) (Add left that)

      ReduceAdd : Reduce (Add (N a) (N b))
                         (N (a + b))

      -- And
      SimplifyAndL : Reduce this that
                -> Reduce (And this right) (And that right)

      SimplifyAndR : Value left
                  -> Reduce this that
                  -> Reduce (And left this) (And left that)

      ReduceAnd : Reduce (And (B a) (B b))
                         (B (a && b))

      -- Binders
      SimplifyLet : Reduce this that
                 -> Reduce (Let this body)
                           (Let that body)

      ReduceLet : Value this
               -> Reduce (Let this body)
                         (Single.subst this body)

namespace Progress

  public export
  data Progress : (term : Term Nil type)
                       -> Type
    where
      Stop : (value : Value term)
                   -> Progress term

      Step : {this,that : Term Nil type}
          -> (step : Reduce this that)
                  -> Progress this

  export
  progress : (term : Term Nil type)
                  -> Progress term
  progress (Var _) impossible

  progress (B x) = Stop B
  progress (N k) = Stop N

  progress (Add l r) with (progress l)
    progress (Add (N n) r) | (Stop N) with (progress r)
      progress (Add (N n) (N m)) | (Stop N) | (Stop N)
        = Step ReduceAdd
      progress (Add (N n) r) | (Stop N) | (Step step)
        = Step (SimplifyAddR N step)
    progress (Add l r) | (Step step)
      = Step (SimplifyAddL step)

  progress (And l r) with (progress l)
    progress (And (B n) r) | (Stop B) with (progress r)
      progress (And (B n) (B m)) | (Stop B) | (Stop B)
        = Step ReduceAnd
      progress (And (B n) r) | (Stop B) | (Step step)
        = Step (SimplifyAndR B step)
    progress (And l r) | (Step step)
      = Step (SimplifyAndL step)

  progress (Let this body) with (progress this)
    progress (Let this body) | (Stop value)
      = Step (ReduceLet value)
    progress (Let this body) | (Step step)
      = Step (SimplifyLet step)

namespace Evaluation

  public export
  data Reduces : (this,that : Term ctxt type)
                           -> Type
    where
      Refl : Reduces this this

      Trans : Reduce  this that
           -> Reduces      that end
           -> Reduces this      end

  public export
  data Finished : (term : Term ctxt type)
                       -> Type
    where
      IsValue : Value term
             -> Finished term

      NoFuel : Finished term

  public export
  data Evaluation : (term : Term Nil type)
                         -> Type
    where
      Eval : {this, that : Term Nil type}
          -> (steps  : Inf (Reduces this that))
          -> (result : Finished that)
                    -> Evaluation this

  public export
  evaluate : (fuel : Fuel)
          -> (term : Term Nil type)
                  -> Evaluation term
  evaluate Dry term = Eval Refl NoFuel
  evaluate (More fuel) term with (progress term)
    evaluate (More fuel) term | (Stop value)
      = Eval Refl (IsValue value)
    evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
      evaluate (More fuel) term | (Step step {that = that}) | (Eval steps result)
        = Eval (Trans step steps) result

namespace Run
  export covering
  run : {type : Ty}
     -> (this : Term Nil type)
             -> Maybe (that : Term Nil type ** Reduces this that)
  run this with (evaluate forever this)
    run this | (Eval steps (IsValue {term} x))
      = Just (term ** steps)
    run this | (Eval steps NoFuel)
      = Nothing
