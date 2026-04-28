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

end XProof.Multi
