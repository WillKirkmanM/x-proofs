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

theorem store_valid (function : Key → Nat) (index : Key → Slot)
    (cache : Cache) (valid : Valid function cache) (key : Key) :
    Valid function (store index cache key (function key)) := by
  intro slot storedKey value entry
  by_cases sameSlot : slot = index key
  · have pairEq : (key, function key) = (storedKey, value) := by
      simpa [store, sameSlot] using entry
    cases pairEq
    rfl
  · exact valid slot storedKey value (by simpa [store, sameSlot] using entry)

def invoke (function : Key → Nat) (index : Key → Slot) (cache : Cache)
    (key : Key) : Nat × Cache :=
  match lookup index cache key with
  | some value => (value, cache)
  | none => (function key, store index cache key (function key))

theorem invoke_correct (function : Key → Nat) (index : Key → Slot)
    (cache : Cache) (valid : Valid function cache) (key : Key) :
    (invoke function index cache key).1 = function key ∧
    Valid function (invoke function index cache key).2 := by
  cases hit : lookup index cache key with
  | none =>
    simpa [invoke, hit] using
      And.intro (Eq.refl (function key)) (store_valid function index cache valid key)
  | some value =>
    simpa [invoke, hit] using
      And.intro (lookup_sound function index cache valid key value hit) valid

theorem lookup_after_store (index : Key → Slot) (cache : Cache) (key : Key)
    (value : Nat) : lookup index (store index cache key value) key = some value := by
  simp [lookup, store]

theorem collision_misses (index : Key → Slot) (cache : Cache)
    (storedKey requestedKey : Key) (value : Nat)
    (collision : index storedKey = index requestedKey)
    (different : storedKey ≠ requestedKey) :
    lookup index (store index cache storedKey value) requestedKey = none := by
  simp [lookup, store, collision, different]

def invokeMany (function : Key → Nat) (index : Key → Slot) :
    List Key → Cache → List Nat × Cache
  | [], cache => ([], cache)
  | key :: keys, cache =>
    let result := invoke function index cache key
    let remaining := invokeMany function index keys result.2
    (result.1 :: remaining.1, remaining.2)

theorem invokeMany_correct (function : Key → Nat) (index : Key → Slot)
    (keys : List Key) (cache : Cache) (valid : Valid function cache) :
    (invokeMany function index keys cache).1 = keys.map function ∧
    Valid function (invokeMany function index keys cache).2 := by
  induction keys generalizing cache with
  | nil => exact ⟨rfl, valid⟩
  | cons key keys ih =>
    have current := invoke_correct function index cache valid key
    have remaining := ih _ current.2
    simp only [invokeMany, List.map_cons]
    exact ⟨by rw [current.1, remaining.1], remaining.2⟩

theorem stores_valid (function : Key → Nat) (index : Key → Slot)
    (keys : List Key) (cache : Cache) (valid : Valid function cache) :
    Valid function (keys.foldl (fun c key => store index c key (function key)) cache) := by
  induction keys generalizing cache with
  | nil => exact valid
  | cons key keys ih => exact ih _ (store_valid function index cache valid key)

end XProof.Memoise
