||| A collection of utlities shared accross the Razors.
|||
||| This consists of:
|||
|||  + some syntactic sugar to make functions detailing renaming,
|||    weakening, and substitution more like those seen in PLFA.
|||
|||  + Some data structures to make working with collections of
|||    dependent types easier.
module Lambda.Common

import Data.List.Elem

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

%default total

-- A reverse cons operator.
infixr 6 +=

namespace List

  ||| Proof that the given list (`xs`) contains the given element
  ||| (`x`).
  |||
  |||
  public export
  Contains : List a -> a -> Type
  Contains xs x = Elem x xs

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs

namespace DList

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : forall v
       . (xs : DList a e vs)
      -> (x  : e v)
            -> DList a e (v::vs)
  (+=) xs x = x :: xs

-- --------------------------------------------------------------------- [ EOF ]
