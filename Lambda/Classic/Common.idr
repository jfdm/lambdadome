module Lambda.Classic.Common

import Decidable.Equality

import Data.List.Elem
import Data.Nat
import Data.DPair

import public Lambda.Common

%default total

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
