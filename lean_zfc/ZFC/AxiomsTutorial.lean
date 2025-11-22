import Mathlib.SetTheory.ZFC.Basic

namespace ZFC

theorem extensionality_axiom (A B : ZFSet) :
  ( ∀ x, x ∈ A ↔ x ∈ B) → A = B := by
  intro h
  apply ZFSet.ext
  exact h

theorem empty_set_exists : ∃ (empty :ZFSet), ∀ x, x ∉ empty := by
  use ZFSet.empty
  intro x
  exact ZFSet.notMem_empty x

theorem pairing_axiom(x y : ZFSet) :
  ∃ p : ZFSet, ∀ z, z ∈ p ↔ z = x ∨ z = y := by
  use {x, y}
  intro x
  exact ZFSet.mem_pair

theorem union_axiom(A : ZFSet):
  ∃ U :ZFSet, ∀ x, x ∈ U ↔ ∃ B ∈ A, x ∈ B := by
  use ZFSet.sUnion A
  intro x
  exact ZFSet.mem_sUnion

theorem power_set_axiom(A : ZFSet):
  ∃ (P : ZFSet), ∀x, x ∈ P ↔ x ⊆ A := by
  use ZFSet.powerset A
  intro x
  exact ZFSet.mem_powerset

theorem separation_axiom(A : ZFSet) (P : ZFSet → Prop):
  ∃ (B : ZFSet), ∀ x, (x ∈ B ↔ x ∈ A ∧ P x) := by
  use ZFSet.sep P A
  intro x
  exact ZFSet.mem_sep

theorem replacement_axiom(A : ZFSet) (φ : ZFSet → ZFSet → Prop):
  (∀ x y_1 y_2, φ x y_1 → φ x y_2 → y_1 = y_2) →
  ∃ (B : ZFSet), ∀ y, y ∈ B ↔ ∃ x ∈ A, φ x y := by
  intro h_func_unique
  sorry

theorem infinity_axiom :
  ∃(A : ZFSet), ZFSet.empty ∈ A ∧ ∀ x ∈ A, insert x x ∈ A := by
  use ZFSet.omega
  constructor
  · exact ZFSet.omega_zero
  · intro x hx
    exact ZFSet.omega_succ hx

theorem regularity_axiom (A : ZFSet) :
  A ≠ ZFSet.empty → ∃ x ∈ A, x ∩ A = ZFSet.empty := by
  intro h_nonempty
  -- h_nonempty 是前提：A ≠ ZFSet.empty
  -- 正則公設在 mathlib 中可能需要更複雜的實作
  sorry

theorem choice_axiom (X : ZFSet) :
  (∀ x ∈ X, x ≠ ZFSet.empty) →
  ∃ (f : ZFSet → ZFSet), (∀ x ∈ X, f x ∈ x) := by
  intro h_nonempty
  -- h_nonempty 表示：對於所有 x ∈ X，x 不是空集
  -- 選擇公設在 mathlib 中通常通過其他方式實作
  -- 例如使用 Classical.choose 或 ZFSet.choice
  sorry
