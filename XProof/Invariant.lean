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

end XProof.Invariant
