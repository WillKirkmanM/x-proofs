/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Multi

abbrev Signature := List Nat

structure Candidate where
  symbol : Nat
  parameters : Signature
deriving DecidableEq, Repr

def matching (candidates : List Candidate) (actual : Signature) : List Candidate :=
  candidates.filter (fun c => decide (c.parameters = actual))

inductive Resolution where
  | missing
  | selected (candidate : Candidate)
  | ambiguous
deriving DecidableEq, Repr

def resolve (candidates : List Candidate) (actual : Signature) : Resolution :=
  match matching candidates actual with
  | [] => .missing
  | [c] => .selected c
  | _ => .ambiguous

theorem mem_matches_iff (c : Candidate) (cs : List Candidate) (actual : Signature) :
    c ∈ matching cs actual ↔ c ∈ cs ∧ c.parameters = actual := by
  simp [matching]

theorem selected_iff (cs : List Candidate) (actual : Signature) (c : Candidate) :
    resolve cs actual = .selected c ↔ matching cs actual = [c] := by
  unfold resolve
  cases h : matching cs actual with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp
    | cons second tail => simp

theorem selection_sound (cs : List Candidate) (actual : Signature) (c : Candidate)
    (h : resolve cs actual = .selected c) : c ∈ cs ∧ c.parameters = actual := by
  apply (mem_matches_iff c cs actual).mp
  rw [(selected_iff cs actual c).mp h]
  simp

theorem selection_unique (cs : List Candidate) (actual : Signature) (c d : Candidate)
    (h : resolve cs actual = .selected c) (hd : d ∈ cs) (ht : d.parameters = actual) :
    d = c := by
  have hm := (mem_matches_iff d cs actual).mpr ⟨hd, ht⟩
  rw [(selected_iff cs actual c).mp h] at hm
  simpa using hm

theorem missing_iff (cs : List Candidate) (actual : Signature) :
    resolve cs actual = .missing ↔ ∀ c ∈ cs, c.parameters ≠ actual := by
  have empty : matching cs actual = [] ↔ ∀ c ∈ cs, c.parameters ≠ actual := by
    simp [matching, List.filter_eq_nil_iff]
  rw [← empty]
  unfold resolve
  cases h : matching cs actual with
  | nil => simp
  | cons c rest => cases rest <;> simp

theorem duplicate_rejected (c d : Candidate) (rest : List Candidate)
    (h : c.parameters = d.parameters) :
    resolve (c :: d :: rest) c.parameters = .ambiguous := by
  simp [resolve, matching, h]

theorem different_signature_rejected (c : Candidate) (actual : Signature)
    (h : c.parameters ≠ actual) : resolve [c] actual = .missing := by
  simp [resolve, matching, h]

end XProof.Multi
