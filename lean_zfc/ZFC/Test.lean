import Mathlib.SetTheory.ZFC.Basic

open SetTheory

def example1 : Prop :=
  Set.zero ∈ Set.succ Set.zero

example : example1 := by
  change Set.zero ∈ (Set.zero ∪ {Set.zero})
  right
  apply Set.mem_singleton
