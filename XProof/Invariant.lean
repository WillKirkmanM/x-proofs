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

theorem mutate_success_valid {contracts : Contracts α} {update : α → α} {state result : α}
    (success : mutate contracts update state = .success result) : Valid contracts result := by
  obtain ⟨rfl, valid⟩ := (check_success_iff contracts (update state) result).mp success
  exact valid

theorem invalid_mutation_traps {contracts : Contracts α} {update : α → α} {state : α}
    (invalid : ¬ Valid contracts (update state)) :
    mutate contracts update state = .trap (update state) := by
  simp [mutate, check, invalid]

theorem invalid_check_cannot_continue {contracts : Contracts α} {state result : α}
    (invalid : ¬ Valid contracts state) : check contracts state ≠ .success result := by
  simp [check, invalid]

def run (contracts : Contracts α) : List (α → α) → α → Outcome α
  | [], state => .success state
  | update :: updates, state =>
    match mutate contracts update state with
    | .success committed => run contracts updates committed
    | .trap committed => .trap committed

theorem run_preserves_valid {contracts : Contracts α} {updates : List (α → α)}
    {state result : α} (initial : Valid contracts state)
    (success : run contracts updates state = .success result) : Valid contracts result := by
  induction updates generalizing state with
  | nil =>
    cases Outcome.success.inj success
    exact initial
  | cons update updates ih =>
    unfold run at success
    cases mutation : mutate contracts update state with
    | success committed =>
      simp only [mutation] at success
      exact ih (mutate_success_valid mutation) success
    | trap committed => simp [mutation] at success

theorem run_stops_at_invalid {contracts : Contracts α} {update : α → α}
    (updates : List (α → α)) (state : α) (invalid : ¬ Valid contracts (update state)) :
    run contracts (update :: updates) state = .trap (update state) := by
  simp [run, invalid_mutation_traps invalid]

end XProof.Invariant
