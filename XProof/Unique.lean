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

def acquire (active : List Loan) (loan : Loan) : Option (List Loan) :=
  if ∀ old ∈ active, Compatible loan old then some (loan :: active) else none

def release (active : List Loan) (loan : Loan) : List Loan :=
  active.filter fun old => decide (old ≠ loan)

theorem acquire_preserves_safe {active next : List Loan} {loan : Loan}
    (safe : Safe active) (accepted : acquire active loan = some next) : Safe next := by
  unfold acquire at accepted
  split at accepted
  next allowed =>
    cases Option.some.inj accepted
    exact List.pairwise_cons.mpr ⟨allowed, safe⟩
  next => contradiction

end XProof.Unique
