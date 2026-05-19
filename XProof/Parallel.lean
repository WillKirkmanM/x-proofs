/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Parallel

def indices (start finish : Int) : List Int :=
  (List.range (finish - start).toNat).map (fun (offset : Nat) => start + (offset : Int))

theorem mem_indices (start finish index : Int) :
    index ∈ indices start finish ↔ start ≤ index ∧ index < finish := by
  simp only [indices, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, bound, rfl⟩
    omega
  · intro bounds
    refine ⟨(index - start).toNat, ?_, ?_⟩ <;> omega

theorem indices_nodup (start finish : Int) : (indices start finish).Nodup := by
  apply List.Pairwise.map _ _ List.nodup_range
  intro a b different equal
  apply different
  omega

theorem schedule_exactly_once (start finish : Int) (schedule : List Int)
    (scheduled : schedule.Perm (indices start finish)) (index : Int) :
    schedule.count index = if start ≤ index ∧ index < finish then 1 else 0 := by
  rw [scheduled.count_eq index, (indices_nodup start finish).count]
  simp [mem_indices]

end XProof.Parallel
