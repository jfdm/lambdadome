module Lambda.BiDirectional

import Decidable.Equality

%default total

public export
Name : Type
Name = String -- I know.

namespace Types
  public export
  data Ty = TyNat | TyFunc Ty Ty | TyProd Ty Ty


  export
  natIsNotFunc : TyNat = TyFunc x y -> Void
  natIsNotFunc Refl impossible

  export
  natIsNotPair : TyNat = TyProd x y -> Void
  natIsNotPair Refl impossible

  export
  funcIsNotProd : TyFunc x y = TyProd z w -> Void
  funcIsNotProd Refl impossible

  funcArgsNotSame : (x = z -> Void) -> TyFunc x y = TyFunc z w -> Void
  funcArgsNotSame f Refl = f Refl

  funcRetsNotSame : (y = w -> Void) -> TyFunc x y = TyFunc x w -> Void
  funcRetsNotSame f Refl = f Refl

  fstNotSame : (x = z -> Void) -> TyProd x y = TyProd z w -> Void
  fstNotSame f Refl = f Refl

  sndNotSame : (y = w -> Void) -> TyProd x y = TyProd x w -> Void
  sndNotSame f Refl = f Refl

  export
  decEq : (a,b : Ty) -> Dec (Equal a b)
  decEq TyNat TyNat = Yes Refl
  decEq TyNat (TyFunc x y)
    = No natIsNotFunc
  decEq TyNat (TyProd x y)
    = No natIsNotPair

  decEq (TyFunc x y) TyNat = No (negEqSym natIsNotFunc)
  decEq (TyFunc x y) (TyFunc z w) with (decEq x z)
    decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) with (decEq y w)
      decEq (TyFunc x w) (TyFunc x w) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (TyFunc x y) (TyFunc x w) | (Yes Refl) | (No contra)
        = No (funcRetsNotSame contra)
    decEq (TyFunc x y) (TyFunc z w) | (No contra)
      = No (funcArgsNotSame contra)

  decEq (TyFunc x y) (TyProd z w) = No funcIsNotProd

  decEq (TyProd x y) TyNat
    = No (negEqSym natIsNotPair)
  decEq (TyProd x y) (TyFunc z w)
    = No (negEqSym funcIsNotProd)
  decEq (TyProd x y) (TyProd z w) with (decEq x z)
    decEq (TyProd x y) (TyProd x w) | (Yes Refl) with (decEq y w)
      decEq (TyProd x w) (TyProd x w) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (TyProd x y) (TyProd x w) | (Yes Refl) | (No contra)
        = No (sndNotSame contra)
    decEq (TyProd x y) (TyProd z w) | (No contra)
      = No (fstNotSame contra)

  export
  DecEq Ty where
    decEq = Types.decEq

  export
  domain : {a, b, x, y : Ty}
        -> (prf : Equal (TyFunc a b)
                        (TyFunc x y))
               -> Equal a x
  domain {a = a} {b = b} {x = a} {y = b} Refl = Refl

  export
  range : {a, b, x, y : Ty}
       -> (prf : Equal (TyFunc a b)
                       (TyFunc x y))
              -> Equal b y
  range {a = a} {b = b} {x = a} {y = b} Refl = Refl

namespace Context

  public export
  Context : Type
  Context = List (Pair String Ty)

  public export
  data Elem : Pair String Ty -> Context -> Type where
    Here : (prfN : Equal x y)
        -> (prfT : Equal a b)
                -> Elem (x,a) ((y,b)::rest)

    There : (contraN : Equal x y -> Void)
         -> (later   : Elem (x,a) rest)
                    -> Elem (x,a) ((y,b)::rest)

  contextEmpty : DPair Ty (\type => Elem (name, type) []) -> Void
  contextEmpty (MkDPair _ (Here prfN prfT)) impossible

  notInRest : (name = x -> Void)
           -> (DPair Ty (\type => Elem (name, type) xs) -> Void)
           -> DPair Ty (\type => Elem (name, type) ((x, type') :: xs))
           -> Void
  notInRest f g (MkDPair type' (Here Refl Refl)) = f Refl
  notInRest f g (MkDPair fst (There contraN later)) = g (_ ** later)


  export
  lookup : (ctxt : Context)
        -> (name : String)
                -> Dec (type ** Elem (name,type) ctxt)
  lookup [] name = No contextEmpty
  lookup ((x,type') :: xs) name with (decEq name x)
    lookup ((name,type') :: xs) name | (Yes Refl) = Yes (MkDPair type' (Here Refl Refl))
    lookup ((x,type') :: xs) name | (No contra) with (lookup xs name)
      lookup ((x,type') :: xs) name | (No contra) | (Yes (MkDPair fst snd))
        = Yes (_ ** There contra snd)
      lookup ((x,type') :: xs) name | (No contra) | (No f)
        = No (notInRest contra f)

namespace Syntax

  mutual
     namespace Synth

       {-

        L⁺, M⁺, N⁺ ::=                      terms with synthesized type
        x                                   variable
        L⁺ · M⁻                             application
        M⁻ ↓ A                              switch to inherited

       -}
       public export
       data Syntax : Type where
         Var : (name : Name)
                    -> Synth.Syntax

         App : (func  : Synth.Syntax)
            -> (param : Check.Syntax)
                     -> Synth.Syntax

         Check : (this : Check.Syntax)
              -> (type : Ty)
                      -> Synth.Syntax


     namespace Check

       {-
       L⁻, M⁻, N⁻ ::=                      terms with inherited type
         ƛ x ⇒ N⁻                            abstraction
         `zero                               zero
         `suc M⁻                             successor
         case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     case
         μ x ⇒ N⁻                            fixpoint
         M⁺ ↑                                switch to synthesized
       -}
       public export
       data Syntax : Type where
         Fun : (name : Name)
            -> (body : Check.Syntax)
                    -> Check.Syntax

         N : (value : Nat)
                   -> Check.Syntax

         Prim : (op   : Nat -> Nat -> Nat)
             -> (land : Check.Syntax)
             -> (rand : Check.Syntax)
                     -> Check.Syntax

         MkPair : (first  : Check.Syntax)
               -> (second : Check.Syntax)
                         -> Check.Syntax

--         Split : (pair   : Synth.Syntax)
--              -> (first  : Name)
--              -> (second : Name)
--              -> (body   : Check.Syntax)
--                        -> Check.Syntax

         First : (pair : Synth.Syntax)
                      -> Check.Syntax

         Second : (pair : Synth.Syntax)
                       -> Check.Syntax

         Rec : (name : Name)
            -> (body : Check.Syntax)
                    -> Check.Syntax

         Synth : (this : Synth.Syntax)
                      -> Check.Syntax


namespace Terms

  mutual
    namespace Synth
      public export
      data Term : Context -> Synth.Syntax -> Ty -> Type where
        Var : (prf : Elem (x,ty) ctxt)
                  -> Synth.Term ctxt (Var x) ty

        App : {tyA,tyB : Ty}
           -> (fun : Synth.Term ctxt f (TyFunc tyA tyB))
           -> (arg : Check.Term ctxt a tyA)
                  -> Synth.Term ctxt (App f a) tyB

        Check : {type : Ty}
             -> (this : Check.Term ctxt term type)
                     -> Synth.Term ctxt (Check term type) type

    namespace Check
      public export
      data Term : Context -> Check.Syntax -> Ty -> Type where

        Fun : {typeA,typeB : Ty}
           -> (body : Check.Term ((x,typeA) :: ctxt)        term typeB)
                   -> Check.Term               ctxt  (Fun x term) (TyFunc typeA typeB)

        N : Check.Term ctxt (N n) TyNat

        Prim : (lop : Check.Term ctxt land TyNat)
            -> (rop : Check.Term ctxt rand TyNat)
                   -> Check.Term ctxt (Prim op land rand) TyNat

        MkPair : (fst : Check.Term ctxt land typeA)
              -> (snd : Check.Term ctxt rand typeB)
                     -> Check.Term ctxt (MkPair land rand) (TyProd typeA typeB)

--        Split : {typeA, typeB : Ty}
--             -> (pair : Synth.Term                            ctxt  tuple (TyProd typeA typeB))
--             -> (body : Check.Term ((b,typeB) :: (a,typeA) :: ctxt) rest  type)
--                     -> Check.Term                            ctxt  (Split tuple a b rest) type

        First : {typeA,typeB : Ty}
             -> (pair : Synth.Term ctxt tuple         (TyProd typeA typeB))
                     -> Check.Term ctxt (First tuple)         typeA

        Second : {typeA,typeB : Ty}
              -> (pair : Synth.Term ctxt tuple         (TyProd typeA typeB))
                      -> Check.Term ctxt (Second tuple)              typeB

        Rec : (body : Check.Term ((x,type) :: ctxt)        term  type)
                   -> Check.Term              ctxt  (Rec x term) type

        Synth : {typeA,typeB : Ty}
             -> (this : Synth.Term ctxt term typeA)
             -> (prf  : Equal typeA typeB)
                     -> Check.Term ctxt (Synth term) typeB

namespace Unique
  export
  lookup : {a,b : Ty}
        -> Elem (x,a) ctxt
        -> Elem (x,b) ctxt
        -> Equal a b
  lookup (Here Refl Refl) (Here Refl Refl) = Refl

  lookup (Here Refl Refl) (There contraN _)
    = absurd (contraN Refl)

  lookup (There contraN _) (Here Refl Refl)
    = absurd (contraN Refl)

  lookup (There _ lA) (There _ lB)
    = lookup lA lB

  export
  synthesis : {a,b : Ty}
           -> (tA : Synth.Term ctxt term a)
           -> (tB : Synth.Term ctxt term b)
                 -> Equal a b
  synthesis (Var prfA) (Var prfB)
    = lookup prfA prfB
  synthesis (App fa aa) (App fb ab)
    = range (synthesis fa fb)
  synthesis (Check tA) (Check tB)
    = Refl

namespace Helpers
  export
  funcArgFails : {typeA, typeB : Ty}
              -> (fun    : Synth.Term ctxt f  (TyFunc typeA typeB))
              -> (contra : Check.Term ctxt a  typeA -> Void)
              -> (this   : (typeB' ** Synth.Term ctxt (App f a) typeB'))
                        -> Void
  funcArgFails fun contra (MkDPair typeB' (App fun' a)) with (domain (Unique.synthesis fun fun'))
    funcArgFails fun contra (MkDPair typeB' (App fun' a)) | Refl = contra a

  export
  switchFailFails : {typeA : Ty}
                 -> (tm     : Synth.Term ctxt term typeA)
                 -> (contra : Equal typeA typeB -> Void)
                 -> (this   : Check.Term ctxt (Synth term) typeB)
                           -> Void
  switchFailFails {typeA} tm contra (Synth this Refl) with (Unique.synthesis tm this)
    switchFailFails tm contra (Synth this Refl) | Refl = contra Refl

notBound : (DPair Ty (\t => Elem (name, t) ctxt) -> Void)
        -> DPair Ty (\type => Term ctxt (Var name) type)
        -> Void
notBound f x with (x)
  notBound f x | (MkDPair fst snd) with (snd)
    notBound f x | (MkDPair fst snd) | (Var prf) = f (MkDPair fst prf)

synthAppFuncNot : (DPair Ty (\type => Synth.Term ctxt func type) -> Void)
                -> DPair Ty (\type => Term ctxt (App func param) type)
                -> Void
synthAppFuncNot f x with (x)
  synthAppFuncNot f x | (MkDPair fst (App fun arg)) = f (MkDPair (TyFunc _ fst) fun)

synthAppFuncWrongTypeNat : Term ctxt func TyNat
                        -> DPair Ty (\type => Term ctxt (App func param) type)
                        -> Void
synthAppFuncWrongTypeNat given (MkDPair fst (App fun arg))
  = natIsNotFunc (Unique.synthesis given fun)

synthAppFuncWrongTypePair : {x,y : Ty}
                         -> Term ctxt func (TyProd x y)
                         -> DPair Ty (\type => Term ctxt (App func param) type)
                         -> Void
synthAppFuncWrongTypePair given (MkDPair fst (App fun arg))
  = (negEqSym funcIsNotProd) (Unique.synthesis given fun)

synthCheckFailed : (Term ctxt this type' -> Void)
                 -> DPair Ty (\type => Term ctxt (Check this type') type)
                 -> Void
synthCheckFailed f (MkDPair type' (Check x)) = f x

export
synthesise : (ctxt : Context)
          -> (term : Synth.Syntax)
                  -> Dec (type ** Synth.Term ctxt term type)

export
check : (ctxt : Context)
     -> (term : Check.Syntax)
     -> (type : Ty)
             -> Dec (Check.Term ctxt term type)

-- [ Synthesise ]

synthesise ctxt (Var name) with (lookup ctxt name)
  synthesise ctxt (Var name) | (Yes (MkDPair type idx))
    = Yes (MkDPair type (Var idx))

  synthesise ctxt (Var name) | (No contra)
    = No (notBound contra)

synthesise ctxt (App func param) with (synthesise ctxt func)
  synthesise ctxt (App func param) | (Yes (MkDPair (TyFunc x y) term)) with (check ctxt param x)
    synthesise ctxt (App func param) | (Yes (MkDPair (TyFunc x y) term)) | (Yes prf)
      = Yes (MkDPair y (App term prf))
    synthesise ctxt (App func param) | (Yes (MkDPair (TyFunc x y) term)) | (No contra)
      = No (funcArgFails term contra)

  synthesise ctxt (App func param) | (Yes (MkDPair TyNat term))
    = No (synthAppFuncWrongTypeNat term)
  synthesise ctxt (App func param) | (Yes (MkDPair (TyProd x y) term))
    = No (synthAppFuncWrongTypePair term)

  synthesise ctxt (App func param) | (No contra)
    = No (synthAppFuncNot contra)

synthesise ctxt (Check this type') with (check ctxt this type')
  synthesise ctxt (Check this type') | (Yes prf)
    = Yes (MkDPair type' (Check prf))
  synthesise ctxt (Check this type') | (No contra)
    = No (synthCheckFailed contra)


checkFunNotNat : Term ctxt (Fun name body) TyNat -> Void
checkFunNotNat (Fun x) impossible
checkFunNotNat N impossible
checkFunNotNat (Prim lop rop) impossible
checkFunNotNat (MkPair fst snd) impossible
--checkFunNotNat (Split pair x) impossible
checkFunNotNat (Rec x) impossible
checkFunNotNat (Synth this prf) impossible

checkFunNotPair : Term ctxt (Fun name body) (TyProd x y) -> Void
checkFunNotPair (Fun z) impossible
checkFunNotPair N impossible
checkFunNotPair (Prim lop rop) impossible
checkFunNotPair (MkPair fst snd) impossible
--checkFunNotPair (Split pair z) impossible
checkFunNotPair (Rec z) impossible
checkFunNotPair (Synth this prf) impossible

checkFunReturn : (Term ((name, x) :: ctxt) body y -> Void) -> Term ctxt (Fun name body) (TyFunc x y) -> Void
checkFunReturn f (Fun z) = f z

checkNatNotFunc : Term ctxt (N value) (TyFunc x y) -> Void
checkNatNotFunc (Fun body) impossible
checkNatNotFunc N impossible
checkNatNotFunc (Prim lop rop) impossible
checkNatNotFunc (MkPair fst snd) impossible
--checkNatNotFunc (Split pair body) impossible
checkNatNotFunc (Rec body) impossible
checkNatNotFunc (Synth this prf) impossible

checkNatNotPair : Term ctxt (N value) (TyProd x y) -> Void
checkNatNotPair (Fun body) impossible
checkNatNotPair N impossible
checkNatNotPair (Prim lop rop) impossible
checkNatNotPair (MkPair fst snd) impossible
--checkNatNotPair (Split pair body) impossible
checkNatNotPair (Rec body) impossible
checkNatNotPair (Synth this prf) impossible

checkPrimNotFunc : Term ctxt (Prim op land rand) (TyFunc x y) -> Void
checkPrimNotFunc (Fun body) impossible
checkPrimNotFunc N impossible
checkPrimNotFunc (Prim lop rop) impossible
checkPrimNotFunc (MkPair fst snd) impossible
--checkPrimNotFunc (Split pair body) impossible
checkPrimNotFunc (Rec body) impossible
checkPrimNotFunc (Synth this prf) impossible

checkPrimNotPair : Term ctxt (Prim op land rand) (TyProd x y) -> Void
checkPrimNotPair (Fun body) impossible
checkPrimNotPair N impossible
checkPrimNotPair (Prim lop rop) impossible
checkPrimNotPair (MkPair fst snd) impossible
--checkPrimNotPair (Split pair body) impossible
checkPrimNotPair (Rec body) impossible
checkPrimNotPair (Synth this prf) impossible

checkPrimLand : (Term ctxt land TyNat -> Void) -> Term ctxt (Prim op land rand) TyNat -> Void
checkPrimLand f (Prim lop rop) = f lop

checkPrimRand : (Term ctxt rand TyNat -> Void) -> Term ctxt (Prim op land rand) TyNat -> Void
checkPrimRand f (Prim lop rop) = f rop


checkPairNotNat : Term ctxt (MkPair first second) TyNat -> Void
checkPairNotNat (Fun body) impossible
checkPairNotNat N impossible
checkPairNotNat (Prim lop rop) impossible
checkPairNotNat (MkPair fst snd) impossible
--checkPairNotNat (Split pair body) impossible
checkPairNotNat (Rec body) impossible
checkPairNotNat (Synth this prf) impossible

checkPairNotFunc : Term ctxt (MkPair first second) (TyFunc x y) -> Void
checkPairNotFunc (Fun body) impossible
checkPairNotFunc N impossible
checkPairNotFunc (Prim lop rop) impossible
checkPairNotFunc (MkPair fst snd) impossible
--checkPairNotFunc (Split pair body) impossible
checkPairNotFunc (Rec body) impossible
checkPairNotFunc (Synth this prf) impossible

checkPairFirst : (Term ctxt first x -> Void) -> Term ctxt (MkPair first second) (TyProd x y) -> Void
checkPairFirst f (MkPair fst snd) = f fst

checkPairSecond : (Term ctxt second y -> Void) -> Term ctxt (MkPair first second) (TyProd x y) -> Void
checkPairSecond f (MkPair fst snd) = f snd


checkRecFailed : (Term ((name, type) :: ctxt) body type -> Void) -> Term ctxt (Rec name body) type -> Void
checkRecFailed f (Rec x) = f x

checkSynthFailed : (DPair Ty (\type => Synth.Term ctxt this type) -> Void) -> Term ctxt (Synth this) type -> Void
checkSynthFailed f (Synth x Refl) = f (_ ** x)

--checkSplitPairFailed : (contra : (type ** Synth.Term ctxt pair type) -> Void) -> Term ctxt (Split pair first second body) type -> Void
--checkSplitPairFailed contra (Split x y) = contra (_ ** x)

--checkSplitPairNotFunc : {a,b : Ty}
--                     -> Term ctxt pair (TyFunc a b)
--                     -> Term ctxt (Split pair first second body) type
--                     -> Void
--checkSplitPairNotFunc given (Split x y)
--  = funcIsNotProd (Unique.synthesis given x)
--
--checkSplitPairNotNat : Term ctxt pair TyNat
--                    -> Term ctxt (Split pair first second body) type
--                    -> Void
--checkSplitPairNotNat given (Split x y)
--  = natIsNotPair (Unique.synthesis given x)

--checkSplitBody : (Check.Term ((second, typeB') :: ((first, typeA') :: ctxt)) body type -> Void)
--              -> Term ctxt (Split pair first second body) type
--              -> Void
--checkSplitBody f (Split {typeA} {typeB} x y) = f y -- fails

checkFirstTupleFailed : (DPair Ty (\type => Synth.Term ctxt tuple type) -> Void) -> Term ctxt (First tuple) type -> Void
checkFirstTupleFailed f x with (x)
  checkFirstTupleFailed f x | (First pair)
    = f (_ ** pair)

checkFirstNotNat : Term ctxt tuple TyNat -> Term ctxt (First tuple) type -> Void
checkFirstNotNat given (First pair)
  = natIsNotPair (Unique.synthesis given pair)

checkFirstNotFunc : {x,y : Ty} -> Term ctxt tuple (TyFunc x y) -> Term ctxt (First tuple) type -> Void
checkFirstNotFunc given (First pair)
  = funcIsNotProd (Unique.synthesis given pair)

checkFirstFails : {type,x,y : Ty} -> Term ctxt tuple (TyProd x y) -> (x = type -> Void) -> Term ctxt (First tuple) type -> Void
checkFirstFails {type = type} {x = x} {y = y} tm f (First pair) with (Unique.synthesis tm pair)
  checkFirstFails {  type = type} {  x = type} {  y = typeB} tm f (First pair) | Refl = f Refl

checkSecondTupleFailed : (DPair Ty (\type => Synth.Term ctxt tuple type) -> Void) -> Term ctxt (Second tuple) type -> Void
checkSecondTupleFailed f x with (x)
  checkSecondTupleFailed f x | (Second pair) = f (_ ** pair)

checkSecondNotNat : Term ctxt tuple TyNat -> Term ctxt (Second tuple) type -> Void
checkSecondNotNat given (Second pair)
  = natIsNotPair (Unique.synthesis given pair)

checkSecondNotFunc : {x,y : Ty} -> Term ctxt tuple (TyFunc x y) -> Term ctxt (Second tuple) type -> Void
checkSecondNotFunc given (Second pair)
  = funcIsNotProd (Unique.synthesis given pair)

checkSecondFails : {type,x,y : Ty} -> Term ctxt tuple (TyProd x y) -> (y = type -> Void) -> Term ctxt (Second tuple) type -> Void
checkSecondFails {type} {x} {y} tm f (Second pair) with (Unique.synthesis tm pair)
  checkSecondFails {type = type} {x = typeA} {y = type} tm f (Second pair) | Refl = f Refl

-- [ Check ]

check ctxt (Fun name body) TyNat
  = No checkFunNotNat
check ctxt (Fun name body) (TyFunc x y) with (check ((name,x)::ctxt) body y)
  check ctxt (Fun name body) (TyFunc x y) | (Yes prf)
    = Yes (Fun prf)
  check ctxt (Fun name body) (TyFunc x y) | (No contra)
    = No (checkFunReturn contra)
check ctxt (Fun name body) (TyProd x y)
  = No checkFunNotPair

check ctxt (N value) TyNat
  = Yes N

check ctxt (N value) (TyFunc x y)
  = No checkNatNotFunc

check ctxt (N value) (TyProd x y)
  = No checkNatNotPair

check ctxt (Prim op land rand) TyNat with (check ctxt land TyNat)
  check ctxt (Prim op land rand) TyNat | (Yes prfL) with (check ctxt rand TyNat)
    check ctxt (Prim op land rand) TyNat | (Yes prfL) | (Yes prfR)
      = Yes (Prim prfL prfR)
    check ctxt (Prim op land rand) TyNat | (Yes prfL) | (No contra)
      = No (checkPrimRand contra)
  check ctxt (Prim op land rand) TyNat | (No contra)
   = No (checkPrimLand contra)

check ctxt (Prim op land rand) (TyFunc x y)
  = No checkPrimNotFunc
check ctxt (Prim op land rand) (TyProd x y)
  = No checkPrimNotPair

check ctxt (MkPair first second) TyNat
  = No checkPairNotNat
check ctxt (MkPair first second) (TyFunc x y)
  = No checkPairNotFunc
check ctxt (MkPair first second) (TyProd x y) with (check ctxt first x)
  check ctxt (MkPair first second) (TyProd x y) | (Yes prfFirst) with (check ctxt second y)
    check ctxt (MkPair first second) (TyProd x y) | (Yes prfFirst) | (Yes prfSecond)
      = Yes (MkPair prfFirst prfSecond)
    check ctxt (MkPair first second) (TyProd x y) | (Yes prfFirst) | (No contra)
      = No (checkPairSecond contra)
  check ctxt (MkPair first second) (TyProd x y) | (No contra)
    = No (checkPairFirst contra)

--check ctxt (Split pair first second body) type with (synthesise ctxt pair)
--  check ctxt (Split pair first second body) type | (Yes (MkDPair (TyProd x y) term)) with (check ((second,y)::(first,x)::ctxt) body type)
--    check ctxt (Split pair first second body) type | (Yes (MkDPair (TyProd x y) term)) | (Yes prf)
--      = Yes (Split term prf)
--    check ctxt (Split pair first second body) type | (Yes (MkDPair (TyProd x y) term)) | (No contra)
--      = No (checkSplitBody contra)
--
--  check ctxt (Split pair first second body) type | (Yes (MkDPair TyNat term))
--    = No (checkSplitPairNotNat term)
--
--  check ctxt (Split pair first second body) type | (Yes (MkDPair (TyFunc _ _) term))
--    = No (checkSplitPairNotFunc term)
--
--  check ctxt (Split pair first second body) type | (No contra)
--    = No (checkSplitPairFailed contra)

check ctxt (First tuple) type with (synthesise ctxt tuple)
  check ctxt (First tuple) type | (Yes (MkDPair (TyProd x y) term)) with (Types.decEq x type)
    check ctxt (First tuple) x | (Yes (MkDPair (TyProd x y) term)) | (Yes Refl)
      = Yes (First term)
    check ctxt (First tuple) type | (Yes (MkDPair (TyProd x y) term)) | (No contra)
      = No (checkFirstFails term contra)

  check ctxt (First tuple) type | (Yes (MkDPair TyNat term))
    = No (checkFirstNotNat term)
  check ctxt (First tuple) type | (Yes (MkDPair (TyFunc x y) term))
    = No (checkFirstNotFunc term)
  check ctxt (First tuple) type | (No contra)
    = No (checkFirstTupleFailed contra)

check ctxt (Second tuple) type with (synthesise ctxt tuple)
  check ctxt (Second tuple) type | (Yes (MkDPair (TyProd x y) term)) with (Types.decEq y type)
    check ctxt (Second tuple) y | (Yes (MkDPair (TyProd x y) term)) | (Yes Refl)
      = Yes (Second term)
    check ctxt (Second tuple) type | (Yes (MkDPair (TyProd x y) term)) | (No contra)
      = No (checkSecondFails term contra)

  check ctxt (Second tuple) type | (Yes (MkDPair TyNat term))
    = No (checkSecondNotNat term)
  check ctxt (Second tuple) type | (Yes (MkDPair (TyFunc x y) term))
    = No (checkSecondNotFunc term)
  check ctxt (Second tuple) type | (No contra)
    = No (checkSecondTupleFailed contra)


check ctxt (Rec name body) type with (check ((name,type)::ctxt) body type)
  check ctxt (Rec name body) type | (Yes prf)
    = Yes (Rec prf)
  check ctxt (Rec name body) type | (No contra)
    = No (checkRecFailed contra)

check ctxt (Synth this) type with (synthesise ctxt this)
  check ctxt (Synth this) type | (Yes (MkDPair type' term)) with (Types.decEq type' type)
    check ctxt (Synth this) type' | (Yes (MkDPair type' term)) | (Yes Refl)
      = Yes (Synth term Refl)
    check ctxt (Synth this) type | (Yes (MkDPair type' term)) | (No contra)
      = No (switchFailFails term contra)

  check ctxt (Synth this) type | (No contra)
    = No (checkSynthFailed contra)

namespace Examples

  export
  two : Check.Syntax
  two = N 2

  export
  double' : Synth.Syntax
  double' = Check (Prim (+) (N 2) (N 2)) TyNat

  export
  doublePair : Synth.Syntax
  doublePair = Check (Fun "x"
                          (MkPair (Prim (+)
                                        (First  (Var "x"))
                                        (First  (Var "x"))
                                  )
                                  (Prim (+)
                                        (Second (Var "x"))
                                        (Second (Var "x"))
                                  )
                          )
                     )
                     (TyFunc (TyProd TyNat TyNat) (TyProd TyNat TyNat))

  export
  toy : Synth.Syntax
  toy
    = App (Check (Fun "x"
                      (Prim (+) (Synth (Var "x")) (N 1))) (TyFunc TyNat TyNat))
          (N 5)
-- [ EOF ]
