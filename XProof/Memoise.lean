/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Memoise

abbrev Key := List UInt64
abbrev Slot := Fin 64
abbrev Cache := Slot → Option (Key × Nat)

def Valid (function : Key → Nat) (cache : Cache) : Prop :=
  ∀ slot key value, cache slot = some (key, value) → value = function key

def empty : Cache := fun _ => none

def lookup (index : Key → Slot) (cache : Cache) (key : Key) : Option Nat :=
  match cache (index key) with
  | none => none
  | some (storedKey, value) => if storedKey = key then some value else none

def store (index : Key → Slot) (cache : Cache) (key : Key) (value : Nat) : Cache :=
  fun slot => if slot = index key then some (key, value) else cache slot

theorem empty_valid (function : Key → Nat) : Valid function empty := by
  intro slot key value entry
  simp [empty] at entry

theorem lookup_sound (function : Key → Nat) (index : Key → Slot)
    (cache : Cache) (valid : Valid function cache) (key : Key) (value : Nat)
    (hit : lookup index cache key = some value) : value = function key := by
  cases entry : cache (index key) with
  | none => simp [lookup, entry] at hit
  | some pair =>
    rcases pair with ⟨storedKey, storedValue⟩
    by_cases equal : storedKey = key
    · subst storedKey
      have values : storedValue = value := by simpa [lookup, entry] using hit
      subst storedValue
      exact valid _ _ _ entry
    · simp [lookup, entry, equal] at hit

end XProof.Memoise
