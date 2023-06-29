module Lambda.SystemF.Examples

import Lambda.SystemF


identity : Term Empty (Forall (Fun (NeutralTy (TyVar Here))
                                   (NeutralTy (TyVar Here))))
identity
  = Forall
    $ Fun
        (TyVar Here)
        (Var Here)

natIdentity : Term Empty (Fun Nat Nat)
natIdentity
  = Resolve identity TyNat

inc : Term (ExtType Empty Nat) (Fun Nat Nat)
inc
  = Fun TyNat (Succ (Var Here))

-- [ EOF ]
