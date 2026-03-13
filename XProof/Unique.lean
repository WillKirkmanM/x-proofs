/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Unique

structure Place where
  owner : Nat
  projection : List Nat
deriving DecidableEq

def Overlap (left right : Place) : Prop :=
  left.owner = right.owner ∧
    (left.projection.IsPrefix right.projection ∨ right.projection.IsPrefix left.projection)

instance (left right : Place) : Decidable (Overlap left right) := inferInstanceAs
  (Decidable (left.owner = right.owner ∧
    (left.projection.IsPrefix right.projection ∨ right.projection.IsPrefix left.projection)))

theorem overlap_symm {left right : Place} (h : Overlap left right) : Overlap right left :=
  ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩

end XProof.Unique
