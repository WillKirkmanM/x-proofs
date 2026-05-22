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

theorem schedule_correct {Env World : Type}
    (worker : Env → Int → World → Int × World) (value : Env → Int → Int)
    (pure : PureWorker worker value) (environment : Env) (start finish : Int)
    (schedule : List Int) (scheduled : schedule.Perm (indices start finish))
    (world : World) :
    ((execute worker environment schedule world).1).Perm
      ((indices start finish).map (fun index => (index, value environment index))) ∧
    (execute worker environment schedule world).2 = world := by
  rw [execute_pure worker value pure]
  exact ⟨scheduled.map _, rfl⟩

def dispatch {Env World : Type} (capture : World → Env × World)
    (worker : Env → Int → World → Int × World) (schedule : List Int)
    (world : World) : World :=
  let captured := capture world
  (execute worker captured.1 schedule captured.2).2

theorem capture_once {Env World : Type} (capture : World → Env × World)
    (worker : Env → Int → World → Int × World) (value : Env → Int → Int)
    (pure : PureWorker worker value) (schedule : List Int) (world : World) :
    dispatch capture worker schedule world = (capture world).2 := by
  simp [dispatch, execute_pure worker value pure]

theorem reversed_range_empty (start finish : Int) (reversed : finish ≤ start) :
    indices start finish = [] := by
  have nonpositive : finish - start ≤ 0 := by omega
  simp [indices, Int.toNat_eq_zero.mpr nonpositive]

end XProof.Parallel
