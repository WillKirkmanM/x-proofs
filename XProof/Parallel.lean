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

end XProof.Parallel
