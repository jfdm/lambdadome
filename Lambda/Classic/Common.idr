module Lambda.Classic.Common

import Decidable.Equality

import Data.List.Elem
import Data.Nat
import Data.DPair

import Lambda.Common

%default total

namespace Renaming

  public export
  weaken : (func : Contains old type
                -> Contains new type)
        -> (Contains (old += type') type
         -> Contains (new += type') type)

  weaken func Here = Here
  weaken func (There rest) = There (func rest)

  public export
  interface Rename (type : Type) (term : List type -> type -> Type) | term where
    rename : {old, new : List type}
          -> (f : {ty : type} -> Contains old ty
                              -> Contains new ty)
          -> ({ty : type} -> term old ty
                          -> term new ty)

    var : {ty   : type}
       -> {ctxt : List type}
               -> Elem ty ctxt
               -> term ctxt ty


    weakens : {old, new : List type}
           -> (f : {ty  : type}
                       -> Contains old ty
                       -> term     new ty)
           -> ({ty,type' : type}
                  -> Contains (old += type') ty
                  -> term     (new += type') ty)
    weakens f Here = var Here
    weakens f (There rest) = rename There (f rest)

namespace Substitution

  namespace General
    public export
    interface Rename type term => Substitute (type : Type) (term : List type -> type -> Type) | term where

      subst : {old, new : List type}
           -> (f : {ty  : type}
                       -> Contains old ty
                       -> term     new ty)
           -> ({ty : type}
                  -> term old ty
                  -> term new ty)

  namespace Single

    apply : {type : Type}
         -> {term : List type -> type -> Type}
         -> Rename type term
         => {ctxt   : List type}
         -> {typeA  : type}
         -> {typeB  : type}
         -> (this   : term      ctxt    typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> term      ctxt           typeA
    apply this Here = this
    apply this (There rest) = var rest

    export
    subst : {type : Type}
         -> {term : List type -> type -> Type}
         -> Rename type term
         => Substitute type term
         => {ctxt          : List type}
         -> {typeA         : type}
         -> {typeB         : type}
         -> (this          : term  ctxt           typeB)
         -> (inThis        : term (ctxt += typeB) typeA)
                          -> term  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis
      = subst (apply this) inThis

namespace Env
  data Item : (type : Type) -> (ty : type) -> Type where
    MkItem : (name : String)
          -> (ty   : type)
                  -> Item type ty

  export
  data Env : (type : Type) -> List type -> Type
    where
      Empty : Env type Nil
      Cons : Item type ty -> Env type rest -> Env type (ty :: rest)

  export
  empty : Env type Nil
  empty = Empty

  export
  extend : (name : String)
        -> (ty   : type)
        -> (env  : Env type rest)
                -> Env type (ty::rest)
  extend name type env = Cons (MkItem name type) env

  export
  getType : String -> Env type tys -> Maybe (ty ** Elem ty tys)
  getType x Empty = Nothing
  getType x (Cons (MkItem y ty) z) with (decEq x y)
    getType y (Cons (MkItem y ty) z) | (Yes Refl) = Just (ty ** Here)
    getType x (Cons (MkItem y ty) z) | (No contra) with (getType x z)
      getType x (Cons (MkItem y ty) z) | (No contra) | Nothing = Nothing
      getType x (Cons (MkItem y ty) z) | (No contra) | (Just (MkDPair fst orf)) = Just (fst ** There orf)
