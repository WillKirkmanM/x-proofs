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

structure Loan where
  place : Place
  unique : Bool
deriving DecidableEq

def Compatible (left right : Loan) : Prop :=
  Overlap left.place right.place → left.unique = false ∧ right.unique = false

instance (left right : Loan) : Decidable (Compatible left right) := inferInstanceAs
  (Decidable (Overlap left.place right.place → left.unique = false ∧ right.unique = false))

def Safe (active : List Loan) : Prop := active.Pairwise Compatible

end XProof.Unique
