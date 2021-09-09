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

import public Decidable.Equality

import Data.List.Elem

import public Toolkit.Data.List.DeBruijn
import public Toolkit.Data.DList

%default total

namespace DList

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : {v : a}
      -> (xs : DList a e vs)
      -> (x  : e v)
            -> DList a e (v::vs)
  (+=) xs x = x :: xs

-- --------------------------------------------------------------------- [ EOF ]
