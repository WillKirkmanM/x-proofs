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

theorem acquire_rejects_unique_overlap {active : List Loan} {loan old : Loan}
    (live : old ∈ active) (overlap : Overlap loan.place old.place)
    (exclusive : loan.unique = true ∨ old.unique = true) : acquire active loan = none := by
  have denied : ¬ Compatible loan old := by
    intro compatible
    have shared := compatible overlap
    rcases exclusive with exclusive | exclusive
    · simp [exclusive] at shared
    · simp [exclusive] at shared
  simp only [acquire]
  split
  next allowed => exact False.elim (denied (allowed old live))
  next => rfl

theorem release_preserves_safe {active : List Loan} (safe : Safe active) (loan : Loan) :
    Safe (release active loan) := List.Pairwise.filter _ safe

theorem released_not_live (active : List Loan) (loan : Loan) :
    loan ∉ release active loan := by simp [release]

inductive Reachable : List Loan → Prop
  | empty : Reachable []
  | acquire {active next : List Loan} {loan : Loan} :
      Reachable active → XProof.Unique.acquire active loan = some next → Reachable next
  | release {active : List Loan} (loan : Loan) :
      Reachable active → Reachable (XProof.Unique.release active loan)

theorem reachable_safe {active : List Loan} (reachable : Reachable active) : Safe active := by
  induction reachable with
  | empty => exact List.Pairwise.nil
  | acquire _ accepted ih => exact acquire_preserves_safe ih accepted
  | release loan _ ih => exact release_preserves_safe ih loan

end XProof.Unique
