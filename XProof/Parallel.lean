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

def execute {Env World : Type} (worker : Env → Int → World → Int × World)
    (environment : Env) : List Int → World → List (Int × Int) × World
  | [], world => ([], world)
  | index :: remaining, world =>
    let result := worker environment index world
    let rest := execute worker environment remaining result.2
    ((index, result.1) :: rest.1, rest.2)

def PureWorker {Env World : Type} (worker : Env → Int → World → Int × World)
    (value : Env → Int → Int) : Prop :=
  ∀ environment index world, worker environment index world = (value environment index, world)

theorem execute_pure {Env World : Type}
    (worker : Env → Int → World → Int × World) (value : Env → Int → Int)
    (pure : PureWorker worker value) (environment : Env) (schedule : List Int)
    (world : World) : execute worker environment schedule world =
      (schedule.map (fun index => (index, value environment index)), world) := by
  induction schedule generalizing world with
  | nil => rfl
  | cons index remaining ih => simp [execute, pure environment index world, ih]

end XProof.Parallel
