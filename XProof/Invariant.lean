/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Invariant

variable {α : Type}

/-- Predicates supplied for the affected owner chain, from inner owner to outer owner. -/
abbrev Contracts (α : Type) := List (α → Bool)

def Valid (contracts : Contracts α) (state : α) : Prop :=
  ∀ predicate ∈ contracts, predicate state = true

instance (contracts : Contracts α) (state : α) : Decidable (Valid contracts state) :=
  inferInstanceAs (Decidable (∀ predicate ∈ contracts, predicate state = true))

inductive Outcome (α : Type) where
  | success (state : α)
  | trap (state : α)
deriving DecidableEq

def check (contracts : Contracts α) (state : α) : Outcome α :=
  if Valid contracts state then .success state else .trap state

def mutate (contracts : Contracts α) (update : α → α) (state : α) : Outcome α :=
  check contracts (update state)

theorem check_success_iff (contracts : Contracts α) (state result : α) :
    check contracts state = .success result ↔ state = result ∧ Valid contracts state := by
  unfold check
  split
  next valid => simp [valid]
  next invalid => simp [invalid]

end XProof.Invariant
