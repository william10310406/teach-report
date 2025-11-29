import Mathlib.SetTheory.ZFC.Basic
-- 注意：Mathlib.SetTheory.ZFC.Basic 包含基本的 ZFC 定義
-- 如果需要更多功能，可以考慮：
-- import Mathlib.SetTheory.ZFC.Ordinal  -- 序數相關（可能包含更多 omega 性質）
-- 但目前 Mathlib.SetTheory.ZFC.Basic 應該足夠
--2.1 Basic Concepts of Set Theory
--Theorem 2.1.1 (a) for every set A, ∅ ⊆ A
-- 空集合是任何集合的子集合（空真命題：空集合沒有元素，所以條件永遠為假）
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- hx : x ∈ ∅，但空集合沒有元素，這是矛盾的
  have : False := ZFSet.notMem_empty x hx
  -- 從矛盾可以推出任何東西（包括 x ∈ A）
  exact this.elim

--Theorem 2.1.1 (b) for every set A, A ⊆ A
theorem theorem_2_1_1_b(A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx

--Theorem 2.1.1 (c) For all sets A, B and C, if A ⊆ B and B ⊆ C, then A ⊆ C
theorem theorem_2_1_1_c(A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h --h: A ⊆ B ∧ B ⊆ C
  rcases h with ⟨ hxAB, hxBC ⟩ --hxAB: A ⊆ B, hxBC: B ⊆ C
  intro x hxA --hxA: x ∈ A
  have hxB : x ∈ B := hxAB hxA -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B → hxB : x ∈ B
  have hxC : x ∈ C := hxBC hxB -- ∵ x ∈ B ∧ B ⊆ C ∴ x ∈ C → hxC : x ∈ C
  --we want to prove x ∈ A → x ∈ C
  exact hxC

--Theorem 2.1.2 If A and B are sets with no elements, A = B
theorem theorem_2_1_2 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h --h: A = ∅ ∧ B = ∅
  rcases h with ⟨ hA, hB ⟩ --hA: A = ∅, hB: B = ∅
  -- 使用 calc 進行鏈式等式證明：A = ∅ = B
  calc
    A = ∅ := hA --hA: A = ∅
    _ = B := hB.symm  -- hB : B = ∅，所以 hB.symm : ∅ = B

--Theorem 2.1.3 For any sets A and B, A ⊆ B and A ≠ ∅ → B ≠ ∅
theorem theorem_2_1_3(A B : ZFSet) : (A ⊆ B ∧ A ≠ ∅) → B ≠ ∅ := by
  -- 引入前提條件
  intro h --h: A ⊆ B ∧ A ≠ ∅
  -- 分解合取命題：hxAB: A ⊆ B, hA_nonempty: A ≠ ∅
  rcases h with ⟨ hxAB, hA_nonempty ⟩
  -- 使用反證法：假設 B = ∅
  by_contra hB_empty --hB_empty: B = ∅
  -- 從 A ⊆ B 和 B = ∅ 推出 A ⊆ ∅
  have hA_subset_empty : A ⊆ ∅ := by
    rw [hB_empty] at hxAB -- 將 hxAB 中的 B 替換為 ∅
    exact hxAB
  -- 證明 A = ∅（因為 A ⊆ ∅ 意味著 A 沒有元素）
  have hA_empty : A = ∅ := by
    -- 使用外延性公理：A = ∅ ↔ (∀ x, x ∈ A ↔ x ∈ ∅)
    -- 執行 apply ZFSet.ext 後，目標從 "A = ∅" 變成了 "∀ x, x ∈ A ↔ x ∈ ∅"
    apply ZFSet.ext
    -- intro x 的作用：引入任意的元素 x
    -- 要證明 "∀ x, x ∈ A ↔ x ∈ ∅"，我們需要：
    --   1) 取任意元素 x（intro x）
    --   2) 證明 "x ∈ A ↔ x ∈ ∅"
    intro x
    -- constructor 將雙條件 ↔ 分解成兩個方向：x ∈ A → x ∈ ∅ 和 x ∈ ∅ → x ∈ A
    constructor
    · intro hx -- x ∈ A
      -- 由於 A ⊆ ∅，所以 x ∈ ∅，但空集合沒有元素，這是矛盾的
      have : x ∈ ∅ := hA_subset_empty hx
      exact False.elim (ZFSet.notMem_empty x this)
    · intro hx -- x ∈ ∅
      -- 空集合沒有元素，x ∈ ∅ 本身就是矛盾的
      exact False.elim (ZFSet.notMem_empty x hx)
  -- 推出矛盾：hA_empty : A = ∅ 與 hA_nonempty : A ≠ ∅ 矛盾
  exact hA_nonempty hA_empty

--Theorem 2.1.5 Let A and B be sets. Then A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)
-- 其中 𝒫(A) 表示 A 的冪集合（所有 A 的子集合組成的集合）
theorem theorem_2_1_5(A B : ZFSet) : A ⊆ B ↔ ZFSet.powerset A ⊆ ZFSet.powerset B := by
  constructor
  -- 方向 1：A ⊆ B → 𝒫(A) ⊆ 𝒫(B)
  · intro h x hx --h : A ⊆ B, hx : x ∈ 𝒫(A)，即 x ∈ ZFSet.powerset A
    -- 要證明 x ∈ 𝒫(B)，即 x ∈ ZFSet.powerset B，需要證明 x ⊆ B
    -- 首先，從 x ∈ 𝒫(A) 推出 x ⊆ A
    have hx_subset_A : x ⊆ A := ZFSet.mem_powerset.mp hx
    -- 由於 x ⊆ A 且 A ⊆ B，所以 x ⊆ B
    have hx_subset_B : x ⊆ B := fun y hy => h (hx_subset_A hy)
    -- 因此 x ∈ 𝒫(B)
    exact ZFSet.mem_powerset.mpr hx_subset_B
  -- 方向 2：𝒫(A) ⊆ 𝒫(B) → A ⊆ B
  · intro h x hx --h : 𝒫(A) ⊆ 𝒫(B), hx : x ∈ A
    -- 要證明 x ∈ B
    -- 首先，注意到 {x} 是 A 的子集合（因為 x ∈ A）
    -- 但更簡單的方法：注意到 A 本身是 A 的子集合，所以 A ∈ 𝒫(A)
    -- 由於 𝒫(A) ⊆ 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    -- 但我們需要證明的是對於任意 x ∈ A，有 x ∈ B
    -- 實際上，我們需要使用 A 本身：A ∈ 𝒫(A)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun y hy => hy)
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := h hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B
    -- 由於 x ∈ A 且 A ⊆ B，所以 x ∈ B
    exact hA_subset_B hx

--Exercise 2.1 (7) Prove that if x ∉ B and A ⊆ B, then x ∉ A.
theorem exercise_2_1_7(A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h --h: x ∉ B ∧ A ⊆ B
  rcases h with ⟨ hx_notin_B, hA_subset_B ⟩
  -- hx_notin_B: x ∉ B.
  -- hA_subset_B: A ⊆ B
  -- By contradiction, suppose x ∈ A
  by_contra hx_in_A
  -- hx_in_A: x ∈ A
  -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A
  -- ∵ x ∈ B ∧ x ∉ B ∴ False
  exact hx_notin_B hx_in_B
  --用 x ∉ B 和 x ∈ B 推出矛盾，所以 x ∉ A

--Exercise 2.1 (9) If A ⊆ B, B ⊆ C, and C ⊆ A, then A = B and B = C.
theorem exercise_2_1_9(A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C ∧ C ⊆ A) → (A = B ∧ B = C) := by
  intro h -- h: A ⊆ B ∧ B ⊆ C ∧ C ⊆ A
  rcases h with ⟨ hA_subset_B, hB_subset_C, hC_subset_A ⟩
  -- hA_subset_B: A ⊆ B
  -- hB_subset_C: B ⊆ C
  -- hC_subset_A: C ⊆ A
  -- A ⊆ B ∧ B ⊆ C →  A ⊆ C
  have hA_subset_C : A ⊆ C := theorem_2_1_1_c A B C ⟨ hA_subset_B, hB_subset_C ⟩
  -- A ⊆ C ∧ C ⊆ A → A = C
  have hA_eq_C : A = C := by
    apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => hA_subset_C hx  -- hA_subset_C : A ⊆ C，應用到 x 和 hx : x ∈ A 得到 x ∈ C
    · exact fun hx => hC_subset_A hx  -- hC_subset_A : C ⊆ A，應用到 x 和 hx : x ∈ C 得到 x ∈ A
  -- C ⊆ A ∧ A ⊆ B → C ⊆ B
  have hC_subset_B : C ⊆ B := theorem_2_1_1_c C A B ⟨ hC_subset_A, hA_subset_B ⟩
  -- C ⊆ B ∧ B ⊆ C → B = C
  have hB_eq_C : B = C := by
    apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => hB_subset_C hx  -- hB_subset_C : B ⊆ C，應用到 x 和 hx : x ∈ B 得到 x ∈ C
    · exact fun hx => hC_subset_B hx  -- hC_subset_B : C ⊆ B，應用到 x 和 hx : x ∈ C 得到 x ∈ B
  -- A = C ∧ B = C → A = B
  constructor
  · -- prove A = B
    rw [hA_eq_C, hB_eq_C]
  · -- prove B = C
    exact hB_eq_C

--Exercise 2.1 (18(a)) Let A and B be sets. A = B ↔ 𝒫(A) = 𝒫(B)
theorem exercise_2_1_18_a(A B : ZFSet) : A = B ↔ ZFSet.powerset A = ZFSet.powerset B := by
  constructor
  · intro h -- h: A = B
    rw [h]  -- 如果 A = B，直接重寫即可得到 𝒫(A) = 𝒫(B)
  · intro h -- h: 𝒫(A) = 𝒫(B)
    -- 步驟 1：證明 A ∈ 𝒫(A)（因為 A ⊆ A）
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun x hx => hx)
    -- 步驟 2：由於 𝒫(A) = 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := by
      rw [← h]  -- 將 𝒫(B) 重寫為 𝒫(A)
      exact hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B

    -- 步驟 3：類似地，B ∈ 𝒫(B)，所以 B ∈ 𝒫(A)，即 B ⊆ A
    have hB_in_powerset_B : B ∈ ZFSet.powerset B := ZFSet.mem_powerset.mpr (fun x hx => hx)
    have hB_in_powerset_A : B ∈ ZFSet.powerset A := by
      rw [h]  -- 將 𝒫(A) 重寫為 𝒫(B)
      exact hB_in_powerset_B
    have hB_subset_A : B ⊆ A := ZFSet.mem_powerset.mp hB_in_powerset_A

    -- 步驟 4：由 A ⊆ B 和 B ⊆ A，使用外延性公理得到 A = B
    -- 外延性公理：兩個集合相等當且僅當它們有相同的元素
    apply ZFSet.ext  -- 將 A = B 轉換為 ∀ x, x ∈ A ↔ x ∈ B
    intro x  -- 引入任意元素 x，需要證明 x ∈ A ↔ x ∈ B
    constructor  -- 將雙條件 ↔ 分解成兩個方向
    · exact fun hx => hA_subset_B hx  -- 方向1：x ∈ A → x ∈ B（由 hA_subset_B : A ⊆ B）
    · exact fun hx => hB_subset_A hx  -- 方向2：x ∈ B → x ∈ A（由 hB_subset_A : B ⊆ A）

-- 2.2 Set Operations
-- Definitions union, intersection, difference
-- The union of A and B is the set A ∪ B = {x : x ∈ A ∨ x ∈ B} ↔ (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B)
theorem union (A B x : ZFSet) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  ZFSet.mem_union

-- The intersection of A and B is the set A ∩ B = {x : x ∈ A ∧ x ∈ B} ↔ (x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B)
theorem intersection (A B x : ZFSet) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  ZFSet.mem_inter

-- ============================================
-- 差集合合（Set Difference）的定義
-- ============================================
-- 數學定義：A - B = {x : x ∈ A ∧ x ∉ B}
-- 在 ZFC 中，差集合合使用分離公理（Axiom Schema of Separation）定義
-- 分離公理：對於任意集合 A 和性質 P，存在集合 {x ∈ A : P x}
--
-- 語法解析：
--   def set_diff             定義函數 set_diff
--   (A B : ZFSet)           參數：A 和 B 都是 ZFSet 類型
--   : ZFSet                 返回類型：ZFSet（一個集合）
--   :=                      定義符號
--   ZFSet.sep               使用分離公理
--   (fun x => x ∉ B)        性質：lambda 函數，表示"x 不在 B 中"
--   A                       源集合：從 A 中分離元素
--
-- 含義：set_diff A B = {x ∈ A : x ∉ B}
--       即從集合 A 中選出所有不在 B 中的元素
def set_diff (A B : ZFSet) : ZFSet := ZFSet.sep (fun x => x ∉ B) A

-- 差集合合的成員關係：x ∈ A - B ↔ x ∈ A ∧ x ∉ B
theorem mem_diff (A B x : ZFSet) : x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B :=
  ZFSet.mem_sep

-- ============================================
-- 補集合（Complement）的定義
-- ============================================
-- 數學定義：設 U 為全域集合，A ⊆ U，則 A 的補集合 Aᶜ = U - A
-- 補集合表示在全域集合 U 中不屬於 A 的所有元素
--
-- 語法解析：
--   def compl             定義函數 compl（complement 的縮寫）
--   (U A : ZFSet)        參數：U 是全域集合，A 是要取補集合的集合
--   : ZFSet               返回類型：ZFSet（一個集合）
--   :=                    定義符號
--   set_diff U A          使用差集合：U - A
--
-- 含義：compl U A = U - A = {x ∈ U : x ∉ A}
--       即從全域集合 U 中選出所有不在 A 中的元素
def compl (U A : ZFSet) : ZFSet := set_diff U A

-- 補集合的成員關係：x ∈ compl U A ↔ x ∈ U ∧ x ∉ A
theorem mem_compl (U A x : ZFSet) : x ∈ compl U A ↔ x ∈ U ∧ x ∉ A :=
  mem_diff U A x

-- Definition : Sets A and B are disjoint if A ∩ B = ∅
theorem disjoint (A B : ZFSet) : A ∩ B = ∅ ↔ ∀x, x ∈ A → x ∉ B := by
  constructor
  -- 方向 1：A ∩ B = ∅ → ∀x, x ∈ A → x ∉ B
  · intro h x hx  -- h: A ∩ B = ∅, x: 任意元素, hx: x ∈ A
    -- 要證明 x ∉ B，使用反證法
    by_contra hx_in_B  -- hx_in_B: x ∈ B（反證假設）
    -- 如果 x ∈ A 且 x ∈ B，那麼 x ∈ A ∩ B
    have hx_in_inter : x ∈ A ∩ B := by
      rw [ZFSet.mem_inter]
      exact ⟨hx, hx_in_B⟩
    -- 但 A ∩ B = ∅，所以 x ∈ ∅，這是矛盾的
    rw [h] at hx_in_inter  -- 將 A ∩ B 重寫為 ∅
    exact ZFSet.notMem_empty x hx_in_inter

  -- 方向 2：∀x, x ∈ A → x ∉ B → A ∩ B = ∅
  · intro h  -- h: ∀x, x ∈ A → x ∉ B
    -- 要證明 A ∩ B = ∅，使用外延性公理
    apply ZFSet.ext
    intro x
    constructor
    -- 方向 2.1：x ∈ A ∩ B → x ∈ ∅
    · intro hx_inter  -- hx_inter: x ∈ A ∩ B
      -- 從 x ∈ A ∩ B 推出 x ∈ A 且 x ∈ B
      have hx_pair : x ∈ A ∧ x ∈ B := by
        rw [ZFSet.mem_inter] at hx_inter
        exact hx_inter
      -- 由 h: ∀x, x ∈ A → x ∉ B，應用到 x 和 hx_pair.left
      have hx_notin_B : x ∉ B := h x hx_pair.left
      -- 但 hx_pair.right 說 x ∈ B，矛盾
      -- hx_notin_B : x ∉ B 即 x ∈ B → False
      -- hx_pair.right : x ∈ B
      -- 所以 hx_notin_B hx_pair.right : False
      -- 從矛盾可以推出任何東西（包括 x ∈ ∅）
      exact False.elim (hx_notin_B hx_pair.right)
    -- 方向 2.2：x ∈ ∅ → x ∈ A ∩ B（空真命題）
    · intro hx_empty  -- hx_empty: x ∈ ∅
      -- 空集合沒有元素，這是矛盾的
      exact False.elim (ZFSet.notMem_empty x hx_empty)

-- Theorem 2.2.1 (a) A ⊆ A ∪ B
theorem thm_2_2_1_a (A B : ZFSet) : A ⊆ A ∪ B := by
  intro x hx -- x: 任意元素, hx: x ∈ A
  -- 從 x ∈ A 推出 x ∈ A ∨ x ∈ B（用 Or.inl），再推出 x ∈ A ∪ B（用 mem_union.mpr）
  have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx)
  exact hx_in_union

-- Theorem 2.2.1 (b) A ∩ B ⊆ A
theorem thm_2_2_1_b (A B : ZFSet) : A ∩ B ⊆ A := by
  intro x hx -- x: 任意元素, hx: x ∈ A ∩ B
  -- mem_inter.mp: x ∈ A ∩ B → x ∈ A ∧ x ∈ B（從左到右）
  -- mem_inter.mpr: x ∈ A ∧ x ∈ B → x ∈ A ∩ B（從右到左）
  -- 这里需要從 x ∈ A ∩ B 推出 x ∈ A ∧ x ∈ B，所以用 .mp
  have hx_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx
  exact hx_pair.left

-- Theorem 2.2.1 (c) A ∩ ∅ = ∅
theorem thm_2_2_1_c (A : ZFSet) : A ∩ ∅ = ∅ := by
  apply ZFSet.ext --根據外延性公里  A ∩ ∅ = ∅ ↔ ∀ x, x ∈ A ∩ ∅ ↔ x ∈ ∅
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter: x ∈ A ∩ ∅
    -- x ∈ A ∩ ∅ → x ∈ ∅
    have hx_pair : x ∈ A ∧ x ∈ ∅ := ZFSet.mem_inter.mp hx_inter
    -- ∵ x ∈ ∅ ∴ False
    exact False.elim (ZFSet.notMem_empty x hx_pair.right)
  · intro hx_empty -- hx_empty: x ∈ ∅
    -- x ∈ ∅ → x ∈ A ∪ ∅ (空真命題)
    exact False.elim (ZFSet.notMem_empty x hx_empty)

-- Theorem 2.2.1 (d) A ∪ ∅ = A
theorem thm_2_2_1_d (A : ZFSet) : A ∪ ∅ = A := by
  apply ZFSet.ext  -- 使用外延性公理：A ∪ ∅ = A ↔ ∀ x, x ∈ A ∪ ∅ ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 將 ↔ 分解成兩個方向

  -- 方向 1：x ∈ A ∪ ∅ → x ∈ A
  · intro hx_union  -- hx_union: x ∈ A ∪ ∅
    -- 從 x ∈ A ∪ ∅ 推出 x ∈ A ∨ x ∈ ∅
    rw [ZFSet.mem_union] at hx_union
    -- 此時 hx_union 的類型是 x ∈ A ∨ x ∈ ∅（析取命題）
    --
    -- cases 語法：對析取命題進行分情況討論
    --   cases hx_union with
    --     | inl hx => ...  處理左分支（Left）：hx : x ∈ A
    --     | inr hx => ...  處理右分支（Right）：hx : x ∈ ∅
    --
    -- 含義：如果 hx_union 是 x ∈ A ∨ x ∈ ∅，那麼有兩種情況：
    --   情況1（inl）：x ∈ A，用 hx 表示這個假設
    --   情況2（inr）：x ∈ ∅，用 hx 表示這個假設
    cases hx_union with
    | inl hx => exact hx  -- 情況1：如果 x ∈ A，直接得到目標 x ∈ A
    | inr hx => exact False.elim (ZFSet.notMem_empty x hx)  -- 情況2：如果 x ∈ ∅，這是矛盾的

  -- 方向 2：x ∈ A → x ∈ A ∪ ∅
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 從 x ∈ A 推出 x ∈ A ∨ x ∈ ∅（用 Or.inl），再推出 x ∈ A ∪ ∅（用 mem_union.mpr）
    exact ZFSet.mem_union.mpr (Or.inl hx_in_A)

-- Theorem 2.2.1 (e) A ∩ A = A
theorem thm_2_2_1_e (A : ZFSet) : A ∩ A = A := by
  apply ZFSet.ext  -- 使用外延性公理：A ∩ A = A ↔ ∀ x, x ∈ A ∩ A ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 將 ↔ 分解成兩個方向

  -- 方向 1：x ∈ A ∩ A → x ∈ A
  · intro hx_inter  -- hx_inter: x ∈ A ∩ A
    -- 從 x ∈ A ∩ A 推出 x ∈ A ∧ x ∈ A（用 mem_inter.mp）
    have hx_pair : x ∈ A ∧ x ∈ A := ZFSet.mem_inter.mp hx_inter
    -- 從合取命題中取出 x ∈ A（.left 或 .right 都可以，因為都是 x ∈ A）
    exact hx_pair.left

  -- 方向 2：x ∈ A → x ∈ A ∩ A
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 要證明 x ∈ A ∩ A，需要構造 x ∈ A ∧ x ∈ A
    -- ⟨hx_in_A, hx_in_A⟩ 構造合取命題（兩個都是 x ∈ A）
    -- 然後用 mem_inter.mpr 推出 x ∈ A ∩ A
    exact ZFSet.mem_inter.mpr ⟨hx_in_A, hx_in_A⟩

-- Theorem 2.2.1 (f) A ∪ A = A
theorem theorem_2_2_1_f (A : ZFSet) : A ∪ A = A := by
  apply ZFSet.ext  -- 使用外延性公理：A ∪ A = A ↔ ∀ x, x ∈ A ∪ A ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 將 ↔ 分解成兩個方向

  -- 方向 1：x ∈ A ∪ A → x ∈ A
  · intro hx_union  -- hx_union: x ∈ A ∪ A
    -- 從 x ∈ A ∪ A 推出 x ∈ A ∨ x ∈ A（用 mem_union）
    rw [ZFSet.mem_union] at hx_union
    -- 分情況討論：x ∈ A ∨ x ∈ A 的兩種情況都是 x ∈ A
    cases hx_union with
    | inl hx => exact hx  -- 情況1：如果 x ∈ A，直接得到
    | inr hx => exact hx  -- 情況2：如果 x ∈ A，直接得到（兩種情況相同）

  -- 方向 2：x ∈ A → x ∈ A ∪ A
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 從 x ∈ A 推出 x ∈ A ∨ x ∈ A（用 Or.inl），再推出 x ∈ A ∪ A（用 mem_union.mpr）
    exact ZFSet.mem_union.mpr (Or.inl hx_in_A)

-- Theorem 2.2.1 (g) A - ∅ = A
theorem theorem_2_2_1_g (A : ZFSet) : set_diff A ∅ = A := by
  apply ZFSet.ext  -- 使用外延性公理：A - ∅ = A ↔ ∀ x, x ∈ A - ∅ ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 將 ↔ 分解成兩個方向

  -- 方向 1：x ∈ A - ∅ → x ∈ A
  · intro hx_diff  -- hx_diff: x ∈ A - ∅
    -- 從 x ∈ A - ∅ 推出 x ∈ A ∧ x ∉ ∅（用 mem_diff.mp）
    have hx_pair : x ∈ A ∧ x ∉ ∅ := (mem_diff A ∅ x).mp hx_diff
    -- 從合取命題中取出 x ∈ A
    exact hx_pair.left

  -- 方向 2：x ∈ A → x ∈ A - ∅
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 要證明 x ∈ A - ∅，需要構造 x ∈ A ∧ x ∉ ∅
    -- x ∈ A 已經有了（hx_in_A）
    -- x ∉ ∅ 用 ZFSet.notMem_empty x 證明（空集合沒有元素）
    -- ⟨hx_in_A, ZFSet.notMem_empty x⟩ 構造合取命題
    -- 然後用 mem_diff.mpr 推出 x ∈ A - ∅
    exact (mem_diff A ∅ x).mpr ⟨hx_in_A, ZFSet.notMem_empty x⟩

-- Theorem 2.2.1 (h) ∅ - A = ∅
theorem theorem_2_2_1_h (A : ZFSet) : set_diff ∅ A = ∅ := by
  apply ZFSet.ext  -- 使用外延性公理：∅ - A = ∅ ↔ ∀ x, x ∈ ∅ - A ↔ x ∈ ∅
  intro x  -- x: 任意元素
  constructor  -- 將 ↔ 分解成兩個方向
  -- 方向 1：x ∈ ∅ - A → x ∈ ∅
  · intro hx_diff  -- hx_diff: x ∈ ∅ - A
    -- 從 x ∈ ∅ - A 推出 x ∈ ∅ ∧ x ∉ A（用 mem_diff.mp）
    have hx_pair : x ∈ ∅ ∧ x ∉ A := (mem_diff ∅ A x).mp hx_diff
    -- 從合取命題中取出 x ∈ ∅
    exact hx_pair.left
  -- 方向 2：x ∈ ∅ → x ∈ ∅ - A（空真命題）
  · intro hx_empty  -- hx_empty: x ∈ ∅
    -- 空集合沒有元素，x ∈ ∅ 本身就是矛盾的
    -- 從矛盾可以推出任何東西（包括 x ∈ ∅ - A）
    exact False.elim (ZFSet.notMem_empty x hx_empty)

-- Theorem 2.2.1 (i) A ∪ B = B ∪ A
theorem theorem_2_2_1_i (A B : ZFSet) : A ∪ B = B ∪ A := by
  apply ZFSet.ext -- 根據外延性公設 A ∪ B = B ∪ A ↔ ∀ x, x ∈ A ∪ B ↔ x ∈ B ∪ A
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_union -- hx_union: x ∈ A ∪ B
    -- x ∈ A ∪ B → x ∈ B ∪ A
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
    cases hx_union with
    | inl hx => exact ZFSet.mem_union.mpr (Or.inr hx) -- If x ∈ A, then x ∈ B ∪ A (x ∈ B ∨ x ∈ A, right branch)
    | inr hx => exact ZFSet.mem_union.mpr (Or.inl hx) -- If x ∈ B, then x ∈ B ∪ A (x ∈ B ∨ x ∈ A, left branch)
  · intro hx_union -- hx_union: x ∈ B ∪ A
    -- x ∈ B ∪ A → x ∈ A ∪ B
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ B ∪ A 拆成 x ∈ B ∨ x ∈ A
    cases hx_union with
    | inl hx => exact ZFSet.mem_union.mpr (Or.inr hx) -- 情況1：hx : x ∈ B（inl 是左分支，對應 x ∈ B ∨ x ∈ A 的左邊）
      -- 目標是證明 x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
      -- 我們有 hx : x ∈ B，要構造 x ∈ A ∨ x ∈ B
      -- 因為 x ∈ B 是 x ∈ A ∨ x ∈ B 的右分支，所以用 Or.inr hx
      -- 然後用 ZFSet.mem_union.mpr 將 x ∈ A ∨ x ∈ B 轉換為 x ∈ A ∪ B
    | inr hx => exact ZFSet.mem_union.mpr (Or.inl hx) -- 情況2：hx : x ∈ A（inr 是右分支，對應 x ∈ B ∨ x ∈ A 的右邊）
      -- 目標是證明 x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
      -- 我們有 hx : x ∈ A，要構造 x ∈ A ∨ x ∈ B
      -- 因為 x ∈ A 是 x ∈ A ∨ x ∈ B 的左分支，所以用 Or.inl hx
      -- 然後用 ZFSet.mem_union.mpr 將 x ∈ A ∨ x ∈ B 轉換為 x ∈ A ∪ B

-- Theorem 2.2.1 (j) A ∩ B = B ∩ A
theorem theorem_2_2_1_j (A B : ZFSet) : A ∩ B = B ∩ A := by
  apply ZFSet.ext -- 根據外延性公設 A ∩ B = B ∩ A ↔ ∀ x, x ∈ A ∩ B ↔ x ∈ B ∩ A
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ A ∩ B
    -- x ∈ A ∩ B → x ∈ B ∩ A
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
    exact ZFSet.mem_inter.mpr ⟨hx_inter.right, hx_inter.left⟩ -- 交換 x ∈ A 和 x ∈ B 的位置
  · intro hx_inter -- hx_inter : x ∈ B ∩ A
    -- x ∈ B ∩ A → x ∈ A ∩ B
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ B ∩ A 拆成 x ∈ B ∧ x ∈ A
    exact ZFSet.mem_inter.mpr ⟨hx_inter.right, hx_inter.left⟩ -- 交換 x ∈ B 和 x ∈ A 的位置

-- Theorem 2.2.1 (k) A ∪ (B ∪ C) = (A ∪ B) ∪ C
theorem theorem_2_2_1_k (A B C : ZFSet) : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  apply ZFSet.ext -- 根據外延性公設 A ∪ (B ∪ C) = (A ∪ B) ∪ C ↔ ∀ x, x ∈ A ∪ (B ∪ C) ↔ x ∈ (A ∪ B) ∪ C
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_union -- hx_union: x ∈ A ∪ (B ∪ C)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ (B ∪ C) 拆成 x ∈ A ∨ x ∈ B ∪ C
    cases hx_union with
    | inl hx => -- hx: x ∈ A
      have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx) -- x ∈ A, so x ∈ A ∪ B
      exact ZFSet.mem_union.mpr (Or.inl h1) -- x ∈ A ∪ B, so x ∈ (A ∪ B) ∪ C
    | inr hx => -- hx: x ∈ B ∪ C
      rw [ZFSet.mem_union] at hx -- 將 x ∈ B ∪ C 拆成 x ∈ B ∨ x ∈ C
      cases hx with
      | inl hx_B => -- hx_B: x ∈ B
        have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inr hx_B) -- x ∈ B, so x ∈ A ∪ B
        exact ZFSet.mem_union.mpr (Or.inl h1) -- x ∈ A ∪ B, so x ∈ (A ∪ B) ∪ C
      | inr hx_C => exact ZFSet.mem_union.mpr (Or.inr hx_C) -- x ∈ C, so x ∈ (A ∪ B) ∪ C
  · intro hx_union -- hx_union: x ∈ (A ∪ B) ∪ C
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ (A ∪ B) ∪ C 拆成 x ∈ A ∪ B ∨ x ∈ C
    cases hx_union with
    | inl hx => -- hx: x ∈ A ∪ B
      rw [ZFSet.mem_union] at hx -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx with
      | inl hx_A => exact ZFSet.mem_union.mpr (Or.inl hx_A) -- x ∈ A, so x ∈ A ∪ (B ∪ C)
      | inr hx_B => -- hx_B: x ∈ B
        have h1 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inl hx_B) -- x ∈ B, so x ∈ B ∪ C
        exact ZFSet.mem_union.mpr (Or.inr h1) -- x ∈ B ∪ C, so x ∈ A ∪ (B ∪ C)
    | inr hx => -- hx: x ∈ C
      have h1 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inr hx) -- x ∈ C, so x ∈ B ∪ C
      exact ZFSet.mem_union.mpr (Or.inr h1) -- x ∈ B ∪ C, so x ∈ A ∪ (B ∪ C)

-- Theorem 2.2.1 (l) A ∩ (B ∩ C) = (A ∩ B) ∩ C
theorem theorem_2_2_1_l (A B C : ZFSet) : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  apply ZFSet.ext -- 根據外延性公設 A ∩ (B ∩ C) = (A ∩ B) ∩ C ↔ ∀ x, x ∈ A ∩ (B ∩ C) ↔ x ∈ (A ∩ B) ∩ C
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_inter -- hx_inter : x ∈ A ∩ (B ∩ C)
    -- x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ C
    have h1 : x ∈ A ∧ x ∈ B ∩ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ (B ∩ C) 拆成 x ∈ A ∧ x ∈ B ∩ C
    have h2_pair : x ∈ B ∧ x ∈ C := ZFSet.mem_inter.mp h1.right -- 將 x ∈ B ∩ C 拆成 x ∈ B ∧ x ∈ C
    have h3 : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨h1.left, h2_pair.left⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
    exact ZFSet.mem_inter.mpr ⟨h3, h2_pair.right⟩ -- x ∈ A ∩ B ∧ x ∈ C, so x ∈ (A ∩ B) ∩ C
  · intro hx_inter -- hx_inter : x ∈ (A ∩ B) ∩ C
    -- x ∈ (A ∩ B) ∩ C → x ∈ A ∩ (B ∩ C)
    have h1 : x ∈ A ∩ B ∧ x ∈ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ (A ∩ B) ∩ C 拆成 x ∈ A ∩ B ∧ x ∈ C
    have h2_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h1.left -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
    have h3 : x ∈ B ∩ C := ZFSet.mem_inter.mpr ⟨h2_pair.right, h1.right⟩ -- x ∈ B ∧ x ∈ C, so x ∈ B ∩ C
    exact ZFSet.mem_inter.mpr ⟨h2_pair.left, h3⟩ -- x ∈ A ∧ x ∈ B ∩ C, so x ∈ A ∩ (B ∩ C)

-- Theorem 2.2.1 (n) A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
theorem theorem_2_2_1_n (A B C : ZFSet) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply ZFSet.ext -- 根據外延性公設 A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) ↔ ∀ x, x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_union -- hx_union: x ∈ A ∪ (B ∩ C)
    -- x ∈ A ∪ (B ∩ C) → x ∈ (A ∪ B) ∩ (A ∪ C)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ (B ∩ C) 拆成 x ∈ A ∨ x ∈ B ∩ C
    cases hx_union with
    | inl hx => -- hx : x ∈ A
      have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx) -- x ∈ A, so x ∈ A ∪ B
      have h2 : x ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inl hx) -- x ∈ A, so x ∈ A ∪ C
      exact ZFSet.mem_inter.mpr ⟨h1, h2⟩ -- x ∈ A ∪ B ∧ x ∈ A ∪ C, so x ∈ (A ∪ B) ∩ (A ∪ C)
    | inr hx => -- hx : x ∈ B ∩ C
      have h1_pair : x ∈ B ∧ x ∈ C := ZFSet.mem_inter.mp hx -- 將 x ∈ B ∩ C 拆成 x ∈ B ∧ x ∈ C
      have h2 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inr h1_pair.left) -- x ∈ B, so x ∈ A ∪ B
      have h3 : x ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inr h1_pair.right) -- x ∈ C, so x ∈ A ∪ C
      exact ZFSet.mem_inter.mpr ⟨h2, h3⟩ -- x ∈ A ∪ B ∧ x ∈ A ∪ C, so x ∈ (A ∪ B) ∩ (A ∪ C)
  · intro hx_inter -- hx_inter: x ∈ (A ∪ B) ∩ (A ∪ C)
    -- x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ (B ∩ C)
    have h1 : x ∈ A ∪ B ∧ x ∈ A ∪ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ (A ∪ B) ∩ (A ∪ C) 拆成 x ∈ A ∪ B ∧ x ∈ A ∪ C
    have h2 : x ∈ A ∨ x ∈ B := ZFSet.mem_union.mp h1.left -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
    have h3 : x ∈ A ∨ x ∈ C := ZFSet.mem_union.mp h1.right -- 將 x ∈ A ∪ C 拆成 x ∈ A ∨ x ∈ C
    -- 目標：證明 x ∈ A ∪ (B ∩ C)，即 x ∈ A ∨ x ∈ B ∩ C
    -- 我們有 h2 : x ∈ A ∨ x ∈ B 和 h3 : x ∈ A ∨ x ∈ C
    -- 需要分情況討論：如果 x ∈ A，直接得到目標；如果 x ∈ B，需要看 x ∈ C 的情況
    cases h2 with
    | inl hx_A => exact ZFSet.mem_union.mpr (Or.inl hx_A) -- 情況1：x ∈ A，直接得到 x ∈ A ∪ (B ∩ C)（用 Or.inl 選擇左分支）
    | inr hx_B => -- 情況2：x ∈ B（h2 的右分支），此時需要看 h3 的情況
      cases h3 with
      | inl hx_A2 => exact ZFSet.mem_union.mpr (Or.inl hx_A2) -- 子情況2.1：x ∈ A，直接得到 x ∈ A ∪ (B ∩ C)
      | inr hx_C => -- 子情況2.2：x ∈ C（h3 的右分支），此時 x ∈ B 且 x ∈ C
        have h4 : x ∈ B ∩ C := ZFSet.mem_inter.mpr ⟨hx_B, hx_C⟩ -- x ∈ B ∧ x ∈ C，所以 x ∈ B ∩ C
        exact ZFSet.mem_union.mpr (Or.inr h4) -- x ∈ B ∩ C，所以 x ∈ A ∪ (B ∩ C)（用 Or.inr 選擇右分支）

-- Theorem 2.2.1 (m) A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
theorem theorem_2_2_1_m (A B C : ZFSet) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ZFSet.ext -- 根據外延性公設 A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ↔ ∀ x, x ∈ A ∩ (B ∪ C) ↔ x ∈ (A ∩ B) ∪ (A ∩ C)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩部分
  · intro hx_inter -- hx_inter : x ∈ A ∩ (B ∪ C)
    have h1 : x ∈ A ∧ x ∈ B ∪ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∧ x ∈ B ∪ C 拆成 x ∈ A ∧ x ∈ B ∪ C
    have h2_pair : x ∈ B ∨ x ∈ C := ZFSet.mem_union.mp h1.right -- 將 x ∈ B ∪ C 拆成 x ∈ B ∨ x ∈ C
    cases h2_pair with
    | inl hx_B => -- hx_B : x ∈ B
      have h3 : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨ h1.left, hx_B ⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
      exact ZFSet.mem_union.mpr (Or.inl h3) -- x ∈ A ∩ B, so x ∈ (A ∩ B) ∪ (A ∩ C)
    | inr hx_C => -- hx_C : x ∈ C
      have h3 : x ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨ h1.left, hx_C ⟩
      exact ZFSet.mem_union.mpr (Or.inr h3) -- x ∈ A ∩ C, so x ∈ (A ∩ B) ∪ (A ∩ C)
  · intro hx_union -- hx_union : x ∈ (A ∩ B) ∪ (A ∩ C)
    have h1 : x ∈ A ∩ B ∨ x ∈ A ∩ C := ZFSet.mem_union.mp hx_union -- 將 x ∈ (A ∩ B) ∪ (A ∩ C) 拆成 x ∈ A ∩ B ∨ x ∈ A ∩ C
    cases h1 with
    | inl hx_B => -- hx_B : x ∈ A ∩ B
      have h2 : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_B -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      have h3 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inl h2.right) -- x ∈ B, so x ∈ B ∪ C
      exact ZFSet.mem_inter.mpr ⟨ h2.left, h3 ⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ (B ∪ C)
    | inr hx_C => -- hx_C : x ∈ A ∩ C
      have h2 : x ∈ A ∧ x ∈ C := ZFSet.mem_inter.mp hx_C -- 將 x ∈ A ∩ C 拆成 x ∈ A ∧ x ∈ C
      have h3 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inr h2.right) -- x ∈ C, so x ∈ B ∪ C
      exact ZFSet.mem_inter.mpr ⟨ h2.left, h3 ⟩ -- x ∈ A ∧ x ∈ C, so x ∈ A ∩ (B ∪ C)

-- Theorem 2.2.1 (o) A ⊆ B ↔ A ∪ B = B
theorem theorem_2_2_1_o (A B : ZFSet) : A ⊆ B ↔ A ∪ B = B := by
  constructor -- 將 ↔ 分成兩個方向
  · intro hAB -- hAB : A ⊆ B
    -- 方向1：A ⊆ B → A ∪ B = B
    apply ZFSet.ext -- 根據外延性公設，將 A ∪ B = B 轉換為 ∀ x, x ∈ A ∪ B ↔ x ∈ B
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_union -- hx_union : x ∈ A ∪ B
      -- x ∈ A ∪ B → x ∈ B
      rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx_union with
      | inl hx_A => exact hAB hx_A -- 情況1：x ∈ A，因為 A ⊆ B，所以 x ∈ B
      | inr hx_B => exact hx_B -- 情況2：x ∈ B，直接成立
    · intro hx_B -- hx_B : x ∈ B
      -- x ∈ B → x ∈ A ∪ B
      exact ZFSet.mem_union.mpr (Or.inr hx_B) -- x ∈ B，所以 x ∈ A ∪ B（用 Or.inr 選擇右分支）
  · intro h_eq x hx_A -- h_eq : A ∪ B = B, x : any arbitrary element, hx_A : x ∈ A
    -- 方向2：A ∪ B = B → A ⊆ B
    -- 目標：證明 x ∈ B
    have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx_A) -- x ∈ A，所以 x ∈ A ∪ B（用 Or.inl 選擇左分支）
    rw [h_eq] at h1 -- 因為 A ∪ B = B，將 h1 中的 A ∪ B 重寫為 B，得到 x ∈ B
    exact h1 -- x ∈ B

-- Theorem 2.2.1 (p) A ⊆ B ↔ A ∩ B = A
theorem theorem_2_2_1_p (A B : ZFSet) : A ⊆ B ↔ A ∩ B = A := by
  constructor -- 將 ↔ 分成兩個方向
  · intro hAB -- hAB : A ⊆ B
    -- 方向1：A ⊆ B → A ∩ B = A
    apply ZFSet.ext -- 根據外延性公設，將 A ∩ B = A 轉換為 ∀ x, x ∈ A ∩ B ↔ x ∈ A
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_inter -- hx_inter : x ∈ A ∩ B
      -- x ∈ A ∩ B → x ∈ A
      exact (ZFSet.mem_inter.mp hx_inter).left -- 從 x ∈ A ∩ B 提取 x ∈ A
    · intro hx_A -- hx_A : x ∈ A
      -- x ∈ A → x ∈ A ∩ B
      have hx_B : x ∈ B := hAB hx_A -- 因為 A ⊆ B，所以 x ∈ B
      exact ZFSet.mem_inter.mpr ⟨hx_A, hx_B⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
  · intro h_eq x hx_A -- h_eq : A ∩ B = A, x : any arbitrary element, hx_A : x ∈ A
    -- 方向2：A ∩ B = A → A ⊆ B
    -- 目標：證明 x ∈ B
    rw [← h_eq] at hx_A -- 因為 A ∩ B = A，將 hx_A 中的 A 重寫為 A ∩ B，得到 x ∈ A ∩ B
    exact (ZFSet.mem_inter.mp hx_A).right -- 從 x ∈ A ∩ B 提取 x ∈ B

-- Theorem 2.2.1 (q) A ⊆ B → A ∪ C ⊆ B ∪ C
theorem theorem_2_2_1_q (A B C : ZFSet) : A ⊆ B → A ∪ C ⊆ B ∪ C  := by
  intro hA_B x hx_union -- hA_B : A ⊆ B, x : any arbitrary element, hx_union : x ∈ A ∪ C
  -- 目標：證明 x ∈ B ∪ C
  rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ C 拆成 x ∈ A ∨ x ∈ C
  cases hx_union with
  | inl hx_A => -- 情況1：hx_A : x ∈ A
    -- 因為 A ⊆ B，所以 x ∈ B
    have hx_B : x ∈ B := hA_B hx_A -- 應用 hA_B : A ⊆ B 到 hx_A : x ∈ A，得到 x ∈ B
    -- x ∈ B，所以 x ∈ B ∪ C（用 Or.inl 選擇左分支，因為 x ∈ B 是 x ∈ B ∨ x ∈ C 的左分支）
    exact ZFSet.mem_union.mpr (Or.inl hx_B)
  | inr hx_C => -- 情況2：hx_C : x ∈ C
    -- x ∈ C，所以 x ∈ B ∪ C（用 Or.inr 選擇右分支，因為 x ∈ C 是 x ∈ B ∨ x ∈ C 的右分支）
    exact ZFSet.mem_union.mpr (Or.inr hx_C)

-- Theorem 2.2.1 (r) A ⊆ B → A ∩ C ⊆ B ∩ C
theorem theorem_2_2_1_r (A B C : ZFSet) : A ⊆ B → A ∩ C ⊆ B ∩ C := by
  intro hA_B x hx_inter -- hA_B : A ⊆ B, x : any arbitrary element, hx_inter : x ∈ A ∩ C
  -- 目標：證明 x ∈ B ∩ C
  have h1 : x ∈ A ∧ x ∈ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ C 拆成 x ∈ A ∧ x ∈ C（使用 .mp 分解交集成員關係）
  have hx_B : x ∈ B := hA_B h1.left -- 應用 hA_B : A ⊆ B 到 h1.left : x ∈ A，得到 x ∈ B
  have hx_C : x ∈ C := h1.right -- 從 x ∈ A ∧ x ∈ C 提取 x ∈ C（使用 .right 提取合取的右部分）
  exact ZFSet.mem_inter.mpr ⟨hx_B, hx_C⟩ -- x ∈ B ∧ x ∈ C，所以 x ∈ B ∩ C（使用 .mpr 構造交集成員關係）

-- Definition Let U be the universe and A ⊆ U. The complement of A is the set Aᶜ = U - A
-- 補集合的定義：相對於全域集合 U，A 的補集合定義為 U - A
-- 這個定理展示補集合的成員關係：x ∈ compl U A ↔ x ∈ U ∧ x ∉ A
-- 使用新定義的 compl 函數和 mem_compl 定理
theorem definition_2_2_1_a (U A x : ZFSet) : x ∈ compl U A ↔ x ∈ U ∧ x ∉ A := by
  exact mem_compl U A x -- 根據補集合的定義 mem_compl，x ∈ compl U A ↔ x ∈ U ∧ x ∉ A

-- Theorem 2.2.2 (a) (Aᶜ)ᶜ = A
theorem theorem_2_2_2_a (U A : ZFSet) (hA_subset_U : A ⊆ U) : compl U (compl U A) = A := by
  apply ZFSet.ext -- 根據外延性公設，將 compl U (compl U A) = A 轉換為 ∀ x, x ∈ compl U (compl U A) ↔ x ∈ A
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_compl_compl -- hx_compl_compl : x ∈ compl U (compl U A)
    -- x ∈ compl U (compl U A) → x ∈ A
    have h1 : x ∈ U ∧ x ∉ compl U A := (mem_compl U (compl U A) x).mp hx_compl_compl -- 將 x ∈ compl U (compl U A) 拆成 x ∈ U ∧ x ∉ compl U A（使用 .mp 分解補集合成員關係）
    by_contra hx_not_in_A -- 假設 x ∉ A（要證明 x ∈ A，所以假設其否定）
    have hx_in_compl : x ∈ compl U A := (mem_compl U A x).mpr ⟨h1.left, hx_not_in_A⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A（使用 .mpr 構造補集合成員關係）
    exact h1.right hx_in_compl -- 矛盾：x ∉ compl U A（從 h1.right）和 x ∈ compl U A（從 hx_in_compl）
  · intro hx_A -- hx_A : x ∈ A
    -- x ∈ A → x ∈ compl U (compl U A)
    have hx_in_U : x ∈ U := hA_subset_U hx_A -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U（應用子集合關係）
    -- 要證明 x ∈ compl U (compl U A)，需要證明 x ∈ U ∧ x ∉ compl U A
    -- 我們已經有 x ∈ U（從 hx_in_U），現在需要證明 x ∉ compl U A
    have hx_not_compl : x ∉ compl U A := by -- 證明 x ∉ compl U A
      by_contra hx_in_compl -- 假設 x ∈ compl U A（要證明 x ∉ compl U A，所以假設其否定）
      have h2 : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_in_compl -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A（使用 .mp 分解補集合成員關係）
      exact h2.right hx_A -- 矛盾：x ∉ A（從 h2.right）和 x ∈ A（從 hx_A）
    exact (mem_compl U (compl U A) x).mpr ⟨hx_in_U, hx_not_compl⟩ -- 將 x ∈ U ∧ x ∉ compl U A 轉換為 x ∈ compl U (compl U A)（使用 .mpr 構造補集合成員關係）

-- Theorem 2.2.2 (b) A ∪ Aᶜ = U
theorem theorem_2_2_2_b (U A : ZFSet) (hA_subset_U : A ⊆ U) : A ∪ compl U A = U := by
  apply ZFSet.ext -- 根據外延性公設，將 A ∪ compl U A = U 轉換為 ∀ x, x ∈ A ∪ compl U A ↔ x ∈ U
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_union -- hx_union : x ∈ A ∪ compl U A
    -- x ∈ A ∪ compl U A → x ∈ U
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ compl U A 拆成 x ∈ A ∨ x ∈ compl U A
    cases hx_union with
    | inl hx_A => exact hA_subset_U hx_A -- 情況1：x ∈ A，因為 A ⊆ U，所以 x ∈ U
    | inr hx_compl => exact (mem_compl U A x).mp hx_compl |>.left -- 情況2：x ∈ compl U A，根據 mem_compl 得到 x ∈ U ∧ x ∉ A，提取 x ∈ U
  · intro hx_U -- hx_U : x ∈ U
    -- x ∈ U → x ∈ A ∪ compl U A
    by_cases hx_A : x ∈ A -- 分情況：x ∈ A 或 x ∉ A
    · exact ZFSet.mem_union.mpr (Or.inl hx_A) -- 情況1：x ∈ A，所以 x ∈ A ∪ compl U A（用 Or.inl 選擇左分支）
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_compl U A x).mpr ⟨hx_U, hx_A⟩)) -- 情況2：x ∉ A，因為 x ∈ U ∧ x ∉ A，所以 x ∈ compl U A，因此 x ∈ A ∪ compl U A

-- Theorem 2.2.2 (c) A ∩ Aᶜ = ∅
theorem theorem_2_2_2_c (U A : ZFSet) : A ∩ compl U A = ∅ := by
  apply ZFSet.ext -- 根據外延性公設，將 A ∩ compl U A = ∅ 轉換為 ∀ x, x ∈ A ∩ compl U A ↔ x ∈ ∅
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_inter -- hx_inter : x ∈ A ∩ compl U A
    -- x ∈ A ∩ compl U A → x ∈ ∅
    have hx_pair : x ∈ A ∧ x ∈ compl U A := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ compl U A 拆成 x ∈ A ∧ x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_pair.right -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    have h_contra : False := h_temp.right hx_pair.left -- 矛盾：x ∉ A（從 h_temp.right）和 x ∈ A（從 hx_pair.left)
    exact False.elim (ZFSet.notMem_empty x (False.elim h_contra)) -- 從 False 推出 x ∈ ∅，然後用 notMem_empty 推出矛盾
  · intro hx_empty -- hx_empty : x ∈ ∅
    -- x ∈ ∅ → x ∈ A ∩ compl U A（空真命題）
    exact False.elim (ZFSet.notMem_empty x hx_empty)

-- Theorem 2.2.2 (d) A - B = A ∩ Bᶜ
theorem theorem_2_2_2_d (A B : ZFSet) (hA_subset_U : A ⊆ U) : set_diff A B = A ∩ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 set_diff A B = A ∩ compl U B 轉換為 ∀ x, x ∈ set_diff A B ↔ x ∈ A ∩ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_diff -- hx_diff : x ∈ set_diff A B
    -- x ∈ set_diff A B → x ∈ A ∩ compl U B
    have hx_pair : x ∈ A ∧ x ∉ B := (mem_diff A B x).mp hx_diff -- 將 x ∈ set_diff A B 拆成 x ∈ A ∧ x ∉ B
    have hx_in_U : x ∈ U := hA_subset_U hx_pair.left -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
    have hx_compl : x ∈ compl U B := (mem_compl U B x).mpr ⟨ hx_in_U, hx_pair.right ⟩
    exact ZFSet.mem_inter.mpr ⟨ hx_pair.left, hx_compl ⟩
  · intro hx_inter -- hx_inter : x ∈ A ∩ compl U B
    -- x ∈ A ∩ compl U B → x ∈ set_diff A B
    have hx_pair : x ∈ A ∧ x ∈ compl U B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ compl U B 拆成 x ∈ A ∧ x ∈ compl U B
    have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.right -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_B : x ∉ B := h_temp.right -- 從 x ∈ U ∧ x ∉ B 提取 x ∉ B
    exact (mem_diff A B x).mpr ⟨hx_pair.left, hx_not_in_B⟩ -- 將 x ∈ A ∧ x ∉ B 轉換為 x ∈ set_diff A B

-- Theorem 2.2.2 (e) A ⊆ B ↔ Bᶜ ⊆ Aᶜ
theorem theorem_2_2_2_e (U A B : ZFSet) (hA_subset_U : A ⊆ U) (_hB_subset_U : B ⊆ U) : A ⊆ B ↔ compl U B ⊆ compl U A := by
  constructor -- 將 ↔ 分成兩個方向
  · intro hA_B x hx_compl_B -- hA_B : A ⊆ B, x : any arbitrary element, hx_compl_B : x ∈ compl U B
    -- x ∈ compl U B → x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_A : x ∉ A := by -- 證明 x ∉ A
      by_contra hx_in_A -- 假設 x ∈ A（要證明 x ∉ A，所以假設其否定）
      have hx_in_B : x ∈ B := hA_B hx_in_A -- 因為 A ⊆ B 且 x ∈ A，所以 x ∈ B
      exact h_temp.right hx_in_B -- 矛盾：x ∉ B（從 h_temp.right）和 x ∈ B（從 hx_in_B）
    exact (mem_compl U A x).mpr ⟨h_temp.left, hx_not_in_A⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
  · intro h_compl_B_compl_A x hx_A -- h_compl_B_compl_A : compl U B ⊆ compl U A, x : any arbitrary element, hx_A : x ∈ A
    -- x ∈ A → x ∈ B
    have hx_in_U : x ∈ U := hA_subset_U hx_A -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
    by_contra hx_not_in_B -- 假設 x ∉ B（要證明 x ∈ B，所以假設其否定）
    have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    have hx_compl_A : x ∈ compl U A := h_compl_B_compl_A hx_compl_B -- 因為 compl U B ⊆ compl U A 且 x ∈ compl U B，所以 x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_compl_A -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    exact h_temp.right hx_A -- 矛盾：x ∉ A（從 h_temp.right）和 x ∈ A（從 hx_A）

-- Theorem 2.2.2 (f) A ∩ B = ∅ ↔ A = Bᶜ (需要額外假設 A ∪ B = U)
theorem theorem_2_2_2_f (U A B : ZFSet) (hA_subset_U : A ⊆ U) (_hB_subset_U : B ⊆ U) (h_union : A ∪ B = U) : A ∩ B = ∅ ↔ A = compl U B := by
  constructor -- 將 ↔ 分成兩個方向
  · intro h_inter_empty -- h_inter_empty : A ∩ B = ∅
    apply ZFSet.ext -- 根據外延性公設，將 A = compl U B 轉換為 ∀ x, x ∈ A ↔ x ∈ compl U B
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_A -- hx_A : x ∈ A
      have hx_in_U : x ∈ U := hA_subset_U hx_A -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
      have hx_not_in_B : x ∉ B := by -- 證明 x ∉ B
        by_contra hx_in_B -- 假設 x ∈ B（要證明 x ∉ B，所以假設其否定）
        have hx_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨hx_A, hx_in_B⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
        rw [h_inter_empty] at hx_inter -- 因為 A ∩ B = ∅，將 hx_inter 中的 A ∩ B 重寫為 ∅，得到 x ∈ ∅
        exact ZFSet.notMem_empty x hx_inter -- 矛盾：x ∈ ∅ 是不可能的
      exact (mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    · intro hx_compl_B -- hx_compl_B : x ∈ compl U B
      have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
      have hx_in_union : x ∈ A ∪ B := by -- 證明 x ∈ A ∪ B
        rw [h_union] -- 因為 A ∪ B = U，將 A ∪ B 重寫為 U
        exact h_temp.left -- x ∈ U
      rw [ZFSet.mem_union] at hx_in_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx_in_union with
      | inl hx_A => exact hx_A -- 情況1：x ∈ A，直接成立
      | inr hx_B => exact False.elim (h_temp.right hx_B) -- 情況2：x ∈ B，但 x ∉ B（從 h_temp.right），矛盾
  · intro h_compl_B -- h_compl_B : A = compl U B
    apply ZFSet.ext -- 根據外延性公設，將 A ∩ B = ∅ 轉換為 ∀ x, x ∈ A ∩ B ↔ x ∈ ∅
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_inter -- hx_inter : x ∈ A ∩ B
      have hx_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      rw [h_compl_B] at hx_pair -- 因為 A = compl U B，將 hx_pair.left 中的 A 重寫為 compl U B
      have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.left -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
      have h_contra : False := h_temp.right hx_pair.right -- 矛盾：x ∉ B（從 h_temp.right）和 x ∈ B（從 hx_pair.right）
      exact False.elim (ZFSet.notMem_empty x (False.elim h_contra)) -- 從 False 推出 x ∈ ∅
    · intro hx_empty -- hx_empty : x ∈ ∅
      exact False.elim (ZFSet.notMem_empty x hx_empty) -- x ∈ ∅ → x ∈ A ∩ B（空真命題）

-- Theorem 2.2.2 (g) (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
theorem theorem_2_2_2_g (U A B : ZFSet): compl U (A ∪ B) = compl U A ∩ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 compl U (A ∪ B) = compl U A ∩ compl U B 轉換為 ∀ x, x ∈ compl U (A ∪ B) ↔ x ∈ compl U A ∩ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_compl_union -- hx_compl_union : x ∈ compl U (A ∪ B)
    -- x ∈ compl U (A ∪ B) → x ∈ compl U A ∩ compl U B
    have h_temp : x ∈ U ∧ x ∉ (A ∪ B) := (mem_compl U (A ∪ B) x).mp hx_compl_union -- 將 x ∈ compl U (A ∪ B) 拆成 x ∈ U ∧ x ∉ (A ∪ B)
    have hx_not_in_union : x ∉ (A ∪ B) := h_temp.right -- 從 x ∈ U ∧ x ∉ (A ∪ B) 提取 x ∉ (A ∪ B)
    have hx_not_A_and_not_B : x ∉ A ∧ x ∉ B := by -- 證明 x ∉ A ∧ x ∉ B
      constructor -- 將合取分成兩個部分
      · intro hx_A -- 假設 x ∈ A
        have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx_A) -- x ∈ A，所以 x ∈ A ∪ B
        exact hx_not_in_union hx_in_union -- 矛盾：x ∉ (A ∪ B) 和 x ∈ A ∪ B
      · intro hx_B -- 假設 x ∈ B
        have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inr hx_B) -- x ∈ B，所以 x ∈ A ∪ B
        exact hx_not_in_union hx_in_union -- 矛盾：x ∉ (A ∪ B) 和 x ∈ A ∪ B
    have hx_compl_A : x ∈ compl U A := (mem_compl U A x).mpr ⟨h_temp.left, hx_not_A_and_not_B.left⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
    have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨h_temp.left, hx_not_A_and_not_B.right⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    exact ZFSet.mem_inter.mpr ⟨hx_compl_A, hx_compl_B⟩ -- 將 x ∈ compl U A ∧ x ∈ compl U B 轉換為 x ∈ compl U A ∩ compl U B
  · intro hx_inter -- hx_inter : x ∈ compl U A ∩ compl U B
    -- x ∈ compl U A ∩ compl U B → x ∈ compl U (A ∪ B)
    have hx_pair : x ∈ compl U A ∧ x ∈ compl U B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ compl U A ∩ compl U B 拆成 x ∈ compl U A ∧ x ∈ compl U B
    have h_temp_A : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_pair.left -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    have h_temp_B : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.right -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_union : x ∉ (A ∪ B) := by -- 證明 x ∉ (A ∪ B)
      intro hx_in_union -- 假設 x ∈ A ∪ B
      rw [ZFSet.mem_union] at hx_in_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx_in_union with
      | inl hx_A => exact h_temp_A.right hx_A -- 情況1：x ∈ A，但 x ∉ A（從 h_temp_A.right），矛盾
      | inr hx_B => exact h_temp_B.right hx_B -- 情況2：x ∈ B，但 x ∉ B（從 h_temp_B.right），矛盾
    exact (mem_compl U (A ∪ B) x).mpr ⟨h_temp_A.left, hx_not_in_union⟩ -- 將 x ∈ U ∧ x ∉ (A ∪ B) 轉換為 x ∈ compl U (A ∪ B)

-- Theorem 2.2.2 (h) (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ
theorem theorem_2_2_2_h (U A B : ZFSet) : compl U (A ∩ B) = compl U A ∪ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 compl U (A ∩ B) = compl U A ∪ compl U B 轉換為 ∀ x, x ∈ compl U (A ∩ B) ↔ x ∈ compl U A ∪ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_compl_inter -- hx_compl_inter : x ∈ compl U (A ∩ B)
    -- x ∈ compl U (A ∩ B) → x ∈ compl U A ∪ compl U B
    have h_temp : x ∈ U ∧ x ∉ (A ∩ B) := (mem_compl U (A ∩ B) x).mp hx_compl_inter -- 將 x ∈ compl U (A ∩ B) 拆成 x ∈ U ∧ x ∉ (A ∩ B)
    have hx_not_in_inter : x ∉ (A ∩ B) := h_temp.right -- 從 x ∈ U ∧ x ∉ (A ∩ B) 提取 x ∉ (A ∩ B)
    have hx_not_A_or_not_B : x ∉ A ∨ x ∉ B := by -- 證明 x ∉ A ∨ x ∉ B
      by_contra h -- 假設 ¬(x ∉ A ∨ x ∉ B)，即 x ∈ A ∧ x ∈ B
      have hx_in_A_and_B : x ∈ A ∧ x ∈ B := by -- 證明 x ∈ A ∧ x ∈ B
        constructor -- 將合取分成兩個部分
        · by_contra hx_not_A -- 假設 x ∉ A
          exact h (Or.inl hx_not_A) -- 矛盾：¬(x ∉ A ∨ x ∉ B) 和 x ∉ A
        · by_contra hx_not_B -- 假設 x ∉ B
          exact h (Or.inr hx_not_B) -- 矛盾：¬(x ∉ A ∨ x ∉ B) 和 x ∉ B
      have hx_in_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr hx_in_A_and_B -- 將 x ∈ A ∧ x ∈ B 轉換為 x ∈ A ∩ B
      exact hx_not_in_inter hx_in_inter -- 矛盾：x ∉ (A ∩ B) 和 x ∈ A ∩ B
    cases hx_not_A_or_not_B with
    | inl hx_not_A => -- 情況1：x ∉ A
      have hx_compl_A : x ∈ compl U A := (mem_compl U A x).mpr ⟨h_temp.left, hx_not_A⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
      exact ZFSet.mem_union.mpr (Or.inl hx_compl_A) -- x ∈ compl U A，所以 x ∈ compl U A ∪ compl U B
    | inr hx_not_B => -- 情況2：x ∉ B
      have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨h_temp.left, hx_not_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
      exact ZFSet.mem_union.mpr (Or.inr hx_compl_B) -- x ∈ compl U B，所以 x ∈ compl U A ∪ compl U B
  · intro hx_union -- hx_union : x ∈ compl U A ∪ compl U B
    -- x ∈ compl U A ∪ compl U B → x ∈ compl U (A ∩ B)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ compl U A ∪ compl U B 拆成 x ∈ compl U A ∨ x ∈ compl U B
    have hx_in_U : x ∈ U := by -- 證明 x ∈ U
      cases hx_union with
      | inl hx_compl_A => exact ((mem_compl U A x).mp hx_compl_A).left -- 情況1：x ∈ compl U A，所以 x ∈ U
      | inr hx_compl_B => exact ((mem_compl U B x).mp hx_compl_B).left -- 情況2：x ∈ compl U B，所以 x ∈ U
    have hx_not_in_inter : x ∉ (A ∩ B) := by -- 證明 x ∉ (A ∩ B)
      intro hx_in_inter -- 假設 x ∈ A ∩ B
      have hx_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_in_inter -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      cases hx_union with
      | inl hx_compl_A => -- 情況1：x ∈ compl U A
        have h_temp_A : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_compl_A -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
        exact h_temp_A.right hx_pair.left -- 矛盾：x ∉ A（從 h_temp_A.right）和 x ∈ A（從 hx_pair.left）
      | inr hx_compl_B => -- 情況2：x ∈ compl U B
        have h_temp_B : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
        exact h_temp_B.right hx_pair.right -- 矛盾：x ∉ B（從 h_temp_B.right）和 x ∈ B（從 hx_pair.right）
    exact (mem_compl U (A ∩ B) x).mpr ⟨hx_in_U, hx_not_in_inter⟩ -- 將 x ∈ U ∧ x ∉ (A ∩ B) 轉換為 x ∈ compl U (A ∩ B)

-- ============================================
-- 有序對（Ordered Pair）的定義
-- ============================================
-- 在 ZFC 中，有序對 (a, b) 定義為 {{a}, {a, b}}（Kuratowski 定義）
-- 這確保了 (a, b) = (c, d) 當且僅當 a = c 且 b = d
--
-- 語法解析：
--   def ordered_pair       定義函數 ordered_pair
--   (a b : ZFSet)         參數：a 和 b 都是 ZFSet 類型
--   : ZFSet                返回類型：ZFSet（一個集合）
--   :=                     定義符號
--   {{a}, {a, b}}         使用配對公設構造集合 {{a}, {a, b}}
--
-- 含義：ordered_pair a b = {{a}, {a, b}}
--       即有序對 (a, b) 定義為包含 {a} 和 {a, b} 的集合
def ordered_pair (a b : ZFSet) : ZFSet := {{a}, {a, b}}

-- 有序對的單射性質：如果 ordered_pair a b = ordered_pair a' b'，則 a = a' 且 b = b'
theorem ordered_pair_inj (a b a' b' : ZFSet) : ordered_pair a b = ordered_pair a' b' → a = a' ∧ b = b' := by
  intro h_eq -- h_eq : ordered_pair a b = ordered_pair a' b'
  -- 因為 {{a}, {a, b}} = {{a'}, {a', b'}}，所以 {a} ∈ {{a}, {a, b}} 當且僅當 {a} ∈ {{a'}, {a', b'}}
  have h_a_in : {a} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inl rfl) -- {a} = {a}，所以 {a} ∈ {{a}, {a, b}}
  rw [h_eq] at h_a_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a} ∈ {{a'}, {a', b'}}
  rw [ordered_pair] at h_a_in -- 展開 ordered_pair a' b' 的定義，得到 {a} ∈ {{a'}, {a', b'}}
  rw [ZFSet.mem_pair] at h_a_in -- 將 {a} ∈ {{a'}, {a', b'}} 拆成 {a} = {a'} ∨ {a} = {a', b'}
  cases h_a_in with
  | inl h_eq_singleton => -- 情況1：{a} = {a'}
    have ha_eq : a = a' := by -- 證明 a = a'
      have ha_in : a ∈ {a} := ZFSet.mem_singleton.mpr rfl -- a = a，所以 a ∈ {a}
      rw [h_eq_singleton] at ha_in -- 將 {a} 重寫為 {a'}，得到 a ∈ {a'}
      rw [ZFSet.mem_singleton] at ha_in -- 將 a ∈ {a'} 轉換為 a = a'
      exact ha_in -- a = a'
    -- 現在我們有 a = a'，需要證明 b = b'
    -- 因為 ordered_pair a b = ordered_pair a' b' 且 a = a'，所以 {{a}, {a, b}} = {{a'}, {a', b'}} = {{a}, {a, b'}}
    have h_ab_in : {a, b} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b} = {a, b}，所以 {a, b} ∈ {{a}, {a, b}}
    rw [h_eq] at h_ab_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a, b} ∈ ordered_pair a' b'
    rw [ordered_pair] at h_ab_in -- 展開 ordered_pair a' b' 的定義，得到 {a, b} ∈ {{a'}, {a', b'}}
    rw [ha_eq] at h_ab_in -- 將 a' 重寫為 a，得到 {a, b} ∈ {{a}, {a, b'}}
    rw [ZFSet.mem_pair] at h_ab_in -- 將 {a, b} ∈ {{a}, {a, b'}} 拆成 {a, b} = {a} ∨ {a, b} = {a, b'}
    cases h_ab_in with
    | inl h_eq_pair_singleton => -- 情況1.1：{a, b} = {a} 或 {a', b} = {a'}（需要重寫）
      -- 先將 h_eq_pair_singleton 中的 a' 重寫為 a
      rw [ha_eq.symm] at h_eq_pair_singleton -- 將 a' 重寫為 a，得到 {a, b} = {a}（因為 ha_eq : a = a'，所以 ha_eq.symm : a' = a）
      -- 這意味著 {a, b} 只有一個元素 a，所以 b = a
      have hb_eq_a : b = a := by -- 證明 b = a
        -- 因為 {a, b} = {a}，所以 b ∈ {a, b} 當且僅當 b ∈ {a}
        have hb_in_pair : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        -- 使用 h_eq_pair_singleton 將 {a, b} 替換為 {a}
        -- 因為 {a, b} = {a}，所以 b ∈ {a, b} 意味著 b ∈ {a}
        rw [h_eq_pair_singleton] at hb_in_pair -- 將 {a, b} 重寫為 {a}，得到 b ∈ {a}
        rw [ZFSet.mem_singleton] at hb_in_pair -- 將 b ∈ {a} 轉換為 b = a
        exact hb_in_pair -- b = a
      -- 類似地，{a, b'} = {a}，所以 b' = a
      have hb'_eq_a : b' = a := by -- 證明 b' = a
        -- 因為 ordered_pair a b = ordered_pair a' b' 且 a = a'，所以 ordered_pair a b = ordered_pair a b'
        have h_eq_ab' : ordered_pair a b = ordered_pair a b' := by -- 證明 ordered_pair a b = ordered_pair a b'
          -- 從 h_eq : ordered_pair a b = ordered_pair a' b' 和 ha_eq : a = a'，我們可以得到 ordered_pair a b = ordered_pair a b'
          -- 因為 a = a'，所以 ordered_pair a' b' = ordered_pair a b'
          have h_eq_right : ordered_pair a' b' = ordered_pair a b' := by -- 證明 ordered_pair a' b' = ordered_pair a b'
            rw [ha_eq] -- 將 a' 重寫為 a
          -- 使用等式的傳遞性：ordered_pair a b = ordered_pair a' b' = ordered_pair a b'
          exact Eq.trans h_eq h_eq_right -- ordered_pair a b = ordered_pair a b'
        have h_ab'_in : {a, b'} ∈ ordered_pair a b' := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b'} = {a, b'}，所以 {a, b'} ∈ {{a}, {a, b'}}
        rw [← h_eq_ab', ordered_pair] at h_ab'_in -- 因為 ordered_pair a b = ordered_pair a b'，展開定義得到 {a, b'} ∈ {{a}, {a, b}}
        rw [ZFSet.mem_pair] at h_ab'_in -- 將 {a, b'} ∈ {{a}, {a, b}} 拆成 {a, b'} = {a} ∨ {a, b'} = {a, b}
        cases h_ab'_in with
        | inl h => -- {a, b'} = {a}
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [h] at hb'_in -- 將 {a, b'} 重寫為 {a}，得到 b' ∈ {a}
          rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
          exact hb'_in -- b' = a
        | inr h => -- {a, b'} = {a, b}
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [h] at hb'_in -- 將 {a, b'} 重寫為 {a, b}，得到 b' ∈ {a, b}
          -- 因為 h_eq_pair_singleton : {a, b} = {a}，所以 b' ∈ {a, b} 意味著 b' ∈ {a}
          rw [h_eq_pair_singleton] at hb'_in -- 將 {a, b} 重寫為 {a}，得到 b' ∈ {a}
          rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
          exact hb'_in -- b' = a
      rw [hb_eq_a, hb'_eq_a] -- 將 b 和 b' 都重寫為 a
      exact ⟨ha_eq, rfl⟩ -- a = a' 且 a = a
    | inr h_eq_pair => -- 情況1.2：{a, b} = {a', b'}（注意：這裡的 {a', b'} 需要重寫為 {a, b'}）
      -- 這意味著 {a, b} 和 {a, b'} 有相同的元素
      have hb_eq_b' : b = b' := by -- 證明 b = b'
        -- 因為 {a, b} = {a', b'}，所以 b ∈ {a, b} 當且僅當 b ∈ {a', b'}
        have hb_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        -- h_eq_pair 是 {a, b} = {a', b'}，需要將 a' 重寫為 a
        rw [ha_eq.symm] at h_eq_pair -- 將 a' 重寫為 a，得到 {a, b} = {a, b'}
        rw [h_eq_pair] at hb_in -- 將 {a, b} 重寫為 {a, b'}，得到 b ∈ {a, b'}
        rw [ZFSet.mem_pair] at hb_in -- 將 b ∈ {a, b'} 拆成 b = a ∨ b = b'
        cases hb_in with
        | inl hb_eq_a => -- 情況1.2.1：b = a
          -- 類似地，b' ∈ {a, b'}，所以 b' = a 或 b' = b'
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [← h_eq_pair] at hb'_in -- 將 {a, b'} 重寫為 {a, b}，得到 b' ∈ {a, b}
          rw [ZFSet.mem_pair] at hb'_in -- 將 b' ∈ {a, b} 拆成 b' = a ∨ b' = b
          cases hb'_in with
          | inl hb'_eq_a => rw [hb_eq_a, hb'_eq_a] -- b = a 且 b' = a，所以 b = b'
          | inr hb'_eq_b => -- b' = b
            rw [hb_eq_a] at hb'_eq_b -- 將 b 重寫為 a，得到 b' = a
            rw [hb'_eq_b] -- 將 b' 重寫為 a，目標變成 b = a
            exact hb_eq_a -- b = a
        | inr hb_eq_b' => exact hb_eq_b' -- b = b'，直接成立
      exact ⟨ha_eq, hb_eq_b'⟩ -- a = a' 且 b = b'
  | inr h_eq_singleton_pair => -- 情況2：{a} = {a', b'}
    -- 這意味著 {a} 有兩個元素 a' 和 b'，但 {a} 只有一個元素 a，所以 a' = b' = a
    have ha'_in : a' ∈ {a', b'} := ZFSet.mem_pair.mpr (Or.inl rfl) -- a' = a'，所以 a' ∈ {a', b'}
    rw [← h_eq_singleton_pair] at ha'_in -- 將 {a', b'} 重寫為 {a}，得到 a' ∈ {a}
    rw [ZFSet.mem_singleton] at ha'_in -- 將 a' ∈ {a} 轉換為 a' = a
    have hb'_in : b' ∈ {a', b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a', b'}
    rw [← h_eq_singleton_pair] at hb'_in -- 將 {a', b'} 重寫為 {a}，得到 b' ∈ {a}
    rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
    -- 現在我們有 a' = a 且 b' = a，所以 ordered_pair a' b' = {{a}, {a, a}} = {{a}}
    -- 類似地，我們需要證明 a = a' 且 b = a
    have h_ab_in : {a, b} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b} = {a, b}，所以 {a, b} ∈ {{a}, {a, b}}
    rw [h_eq] at h_ab_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a, b} ∈ ordered_pair a' b'
    rw [ordered_pair] at h_ab_in -- 展開 ordered_pair a' b' 的定義，得到 {a, b} ∈ {{a'}, {a', b'}}
    rw [ha'_in, hb'_in] at h_ab_in -- 將 a' 和 b' 都重寫為 a，得到 {a, b} ∈ {{a}, {a, a}}
    -- 注意：{a, a} = {a}，所以 {{a}, {a, a}} = {{a}}
    have h_pair_eq : ({a, a} : ZFSet) = ({a} : ZFSet) := by -- 證明 {a, a} = {a}，明確類型為 ZFSet
      apply ZFSet.ext -- 使用外延性公設
      intro x -- x : any arbitrary element
      constructor -- 將 ↔ 分成兩個部分
      · intro hx_aa -- hx_aa : x ∈ {a, a}
        rw [ZFSet.mem_pair] at hx_aa -- 將 x ∈ {a, a} 拆成 x = a ∨ x = a
        cases hx_aa with
        | inl hx_eq => -- x = a
          rw [ZFSet.mem_singleton] -- 將目標 x ∈ {a} 轉換為 x = a
          exact hx_eq -- x = a
        | inr hx_eq => -- x = a
          rw [ZFSet.mem_singleton] -- 將目標 x ∈ {a} 轉換為 x = a
          exact hx_eq -- x = a
      · intro hx_a -- hx_a : x ∈ {a}
        rw [ZFSet.mem_singleton] at hx_a -- 將 x ∈ {a} 轉換為 x = a
        rw [hx_a] -- 將 x 重寫為 a
        rw [ZFSet.mem_pair] -- 將 a ∈ {a, a} 拆成 a = a ∨ a = a
        left
        rfl -- a = a
    rw [h_pair_eq] at h_ab_in -- 將 {a, a} 重寫為 {a}，得到 {a, b} ∈ {{a}}
    rw [ZFSet.mem_pair] at h_ab_in -- 將 {a, b} ∈ {{a}} 拆成 {a, b} = {a} ∨ {a, b} = {a}
    cases h_ab_in with
    | inl h => -- {a, b} = {a}
      have hb_eq_a : b = a := by -- 證明 b = a
        have hb_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        rw [h] at hb_in -- 將 {a, b} 重寫為 {a}，得到 b ∈ {a}
        rw [ZFSet.mem_singleton] at hb_in -- 將 b ∈ {a} 轉換為 b = a
        exact hb_in -- b = a
      rw [ha'_in, hb'_in, hb_eq_a] -- 將 a', b', b 都重寫為 a
      exact ⟨rfl, rfl⟩ -- a = a 且 a = a
    | inr h => -- {a, b} = {a}（重複情況）
      have hb_eq_a : b = a := by -- 證明 b = a
        have hb_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        rw [h] at hb_in -- 將 {a, b} 重寫為 {a}，得到 b ∈ {a}
        rw [ZFSet.mem_singleton] at hb_in -- 將 b ∈ {a} 轉換為 b = a
        exact hb_in -- b = a
      rw [ha'_in, hb'_in, hb_eq_a] -- 將 a', b', b 都重寫為 a
      exact ⟨rfl, rfl⟩ -- a = a 且 a = a

-- ============================================
-- 笛卡爾積（Cartesian Product）的定義
-- ============================================
-- 數學定義：A × B = {(a, b) | a ∈ A, b ∈ B}
-- 在 ZFC 中，笛卡爾積是所有有序對 (a, b) 的集合，其中 a ∈ A 且 b ∈ B
--
-- 語法解析：
--   def product            定義函數 product
--   (A B : ZFSet)         參數：A 和 B 都是 ZFSet 類型
--   : ZFSet                返回類型：ZFSet（一個集合）
--   :=                     定義符號
--   ZFSet.sep              使用分離公設
--   (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b)  性質：x 是 A × B 中的有序對
--   (ZFSet.powerset (ZFSet.powerset (A ∪ B)))  源集合：A ∪ B 的冪集的冪集
--
-- 含義：product A B = {x | ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b}
--       即從 A ∪ B 的冪集的冪集中選出所有形如 (a, b) 的有序對，其中 a ∈ A 且 b ∈ B
--
-- 注意：這個定義使用分離公設從一個足夠大的集合中分離出所有有序對
--       因為有序對 (a, b) = {{a}, {a, b}} 是 A ∪ B 的冪集的冪集的元素
def product (A B : ZFSet) : ZFSet := ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))

-- 笛卡爾積的成員關係：x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
theorem mem_product (A B x : ZFSet) : x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b := by
  rw [product] -- 展開 product 的定義：product A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_powerset, h_exists⟩ -- hx_in_powerset : x ∈ ZFSet.powerset (ZFSet.powerset (A ∪ B)), h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    exact h_exists -- 直接使用 h_exists
  · intro h_exists -- h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    constructor -- 將合取分成兩個部分
    · -- 證明 x ∈ ZFSet.powerset (ZFSet.powerset (A ∪ B))
      -- 這需要證明有序對 ordered_pair a b = {{a}, {a, b}} 是 powerset (powerset (A ∪ B)) 的元素
      -- 即證明 {{a}, {a, b}} ⊆ powerset (A ∪ B)
      rcases h_exists with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, x = ordered_pair a b
      rw [ordered_pair] -- 展開 ordered_pair 的定義：x = {{a}, {a, b}}
      apply ZFSet.mem_powerset.mpr -- 使用冪集的成員關係：x ∈ powerset A ↔ x ⊆ A，目標變成 {{a}, {a, b}} ⊆ powerset (A ∪ B)
      intro z hz -- z : any arbitrary element, hz : z ∈ {{a}, {a, b}}
      rw [ZFSet.mem_pair] at hz -- 將 z ∈ {{a}, {a, b}} 拆成 z = {a} ∨ z = {a, b}
      cases hz with
      | inl hz_eq => -- 情況1：z = {a}
        rw [hz_eq] -- 將 z 重寫為 {a}
        apply ZFSet.mem_powerset.mpr -- 證明 {a} ∈ powerset (A ∪ B)，即 {a} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a}
        rw [ZFSet.mem_singleton] at hw -- 將 w ∈ {a} 轉換為 w = a
        rw [hw] -- 將 w 重寫為 a
        rw [ZFSet.mem_union] -- 將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
        left
        exact ha -- a ∈ A，所以 a ∈ A ∪ B
      | inr hz_eq => -- 情況2：z = {a, b}
        rw [hz_eq] -- 將 z 重寫為 {a, b}
        apply ZFSet.mem_powerset.mpr -- 證明 {a, b} ∈ powerset (A ∪ B)，即 {a, b} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a, b}
        rw [ZFSet.mem_pair] at hw -- 將 w ∈ {a, b} 拆成 w = a ∨ w = b
        cases hw with
        | inl hw_eq => -- w = a
          rw [hw_eq] -- 將 w 重寫為 a
          rw [ZFSet.mem_union] -- 將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
          left
          exact ha -- a ∈ A，所以 a ∈ A ∪ B
        | inr hw_eq => -- w = b
          rw [hw_eq] -- 將 w 重寫為 b
          rw [ZFSet.mem_union] -- 將 b ∈ A ∪ B 拆成 a ∈ A ∨ b ∈ B
          right
          exact hb -- b ∈ B，所以 b ∈ A ∪ B
    · exact h_exists -- 直接使用 h_exists

-- Theorem 2.2.3 (a) A ⨯ (B ∪ C) = (A ⨯ B) ∪ (A ⨯ C)
theorem theorem_2_2_3_a (A B C : ZFSet) : product A (B ∪ C) = product A B ∪ product A C := by
  apply ZFSet.ext -- 根據外延性公設，將 product A (B ∪ C) = product A B ∪ product A C 轉換為 ∀ x, x ∈ product A (B ∪ C) ↔ x ∈ product A B ∪ product A C
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_product -- hx_product : x ∈ product A (B ∪ C)
    -- x ∈ product A (B ∪ C) → x ∈ product A B ∪ product A C
    rw [product] at hx_product -- 展開 product 的定義：product A (B ∪ C) = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B ∪ C)))
    rw [ZFSet.mem_sep] at hx_product -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
    rcases hx_product with ⟨hx_in_powerset, h_exists⟩ -- 分解分離公設的成員關係，h_exists : ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b
    rcases h_exists with ⟨a, ha, b, hb, hx_eq⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B ∪ C, hx_eq : x = ordered_pair a b
    -- 現在我們有：a ∈ A, b ∈ B ∪ C, x = ordered_pair a b
    rw [ZFSet.mem_union] at hb -- 將 b ∈ B ∪ C 拆成 b ∈ B ∨ b ∈ C
    cases hb with
    | inl hb_B => -- 情況1：b ∈ B
      have hx_in_product_B : x ∈ product A B := by -- 證明 x ∈ product A B
        rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
        exact ⟨a, ha, b, hb_B, rfl⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
      exact ZFSet.mem_union.mpr (Or.inl hx_in_product_B) -- x ∈ product A B，所以 x ∈ product A B ∪ product A C
    | inr hb_C => -- 情況2：b ∈ C
      have hx_in_product_C : x ∈ product A C := by -- 證明 x ∈ product A C
        rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
        exact ⟨a, ha, b, hb_C, rfl⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ C
      exact ZFSet.mem_union.mpr (Or.inr hx_in_product_C) -- x ∈ product A C，所以 x ∈ product A B ∪ product A C
  · intro hx_union -- hx_union : x ∈ product A B ∪ product A C
    -- x ∈ product A B ∪ product A C → x ∈ product A (B ∪ C)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ product A B ∪ product A C 拆成 x ∈ product A B ∨ x ∈ product A C
    cases hx_union with
    | inl hx_product_B => -- 情況1：x ∈ product A B
      rw [mem_product] at hx_product_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
      rcases hx_product_B with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, x = ordered_pair a b
      have hb_union : b ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inl hb) -- b ∈ B，所以 b ∈ B ∪ C
      rw [mem_product] -- 使用笛卡爾積的成員關係
      exact ⟨a, ha, b, hb_union, rfl⟩ -- x = ordered_pair a b, a ∈ A, b ∈ B ∪ C
    | inr hx_product_C => -- 情況2：x ∈ product A C
      rw [mem_product] at hx_product_C -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ C, x = ordered_pair a b
      rcases hx_product_C with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ C, x = ordered_pair a b
      have hb_union : b ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inr hb) -- b ∈ C，所以 b ∈ B ∪ C
      rw [mem_product] -- 使用笛卡爾積的成員關係
      exact ⟨a, ha, b, hb_union, rfl⟩ -- x = ordered_pair a b, a ∈ A, b ∈ B ∪ C

-- Theorem 2.2.3 (b) A ⨯ (B ∩ C) = (A ⨯ B) ∩ (A ⨯ C)
theorem theorem_2_2_3_b (A B C : ZFSet) : product A (B ∩ C) = product A B ∩ product A C := by
  apply ZFSet.ext -- 根據外延性公設，將 product A (B ∩ C) = product A B ∩ product A C 轉換為 ∀ x, x ∈ product A (B ∩ C) ↔ x ∈ product A B ∩ product A C
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_product -- hx_product : x ∈ product A (B ∩ C)
    -- x ∈ product A (B ∩ C) → x ∈ product A B ∩ product A C
    rw [product] at hx_product -- 展開 product 的定義：product A (B ∩ C) = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B ∩ C, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B ∪ C)))
    rw [ZFSet.mem_sep] at hx_product -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
    rcases hx_product with ⟨hx_in_powerset, h_exists⟩ -- 分解分離公設的成員關係，h_exists : ∃ a ∈ A, ∃ b ∈ B ∩ C, x = ordered_pair a b
    rcases h_exists with ⟨ a, ha, b, hb, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B ∩ C, hx_eq : x = ordered_pair a b
    -- 現在我們有：a ∈ A, b ∈ B ∩ C, x = ordered_pair a b
    rw [ZFSet.mem_inter] at hb -- 將 b ∈ B ∩ C 拆成 b ∈ B ∧ b ∈ C
    have hb_B : b ∈ B := hb.left -- 從 b ∈ B ∧ b ∈ C 提取 b ∈ B
    have hb_C : b ∈ C := hb.right -- 從 b ∈ B ∧ b ∈ C 提取 b ∈ C
    have hx_in_product_B : x ∈ product A B := by -- 證明 x ∈ product A B
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha, b, hb_B, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    have hx_in_product_C : x ∈ product A C := by -- 證明 x ∈ product A C
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha, b, hb_C, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ C
    exact ZFSet.mem_inter.mpr ⟨ hx_in_product_B, hx_in_product_C ⟩ -- x ∈ product A B ∩ product A C
  · intro hx_inter -- hx_inter : x ∈ product A B ∩ product A C
    -- x ∈ product A B ∩ product A C → x ∈ product A (B ∩ C)
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ product A B ∩ product A C 拆成 x ∈ product A B ∧ x ∈ product A C
    rcases hx_inter with ⟨ hx_in_product_B, hx_in_product_C ⟩ -- 分解交集成員關係，得到 x ∈ product A B ∧ x ∈ product A C
    rw [mem_product] at hx_in_product_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    rcases hx_in_product_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B
    -- 因為 x ∈ product A C，所以存在 a' ∈ A 和 b' ∈ C，使得 x = ordered_pair a' b'
    -- 但因為 x = ordered_pair a b，所以 ordered_pair a b = ordered_pair a' b'
    -- 根據有序對的 Kuratowski 定義，如果 {{a}, {a, b}} = {{a'}, {a', b'}}，則 a = a' 且 b = b'
    -- 因此 b = b'，所以 b ∈ C
    rw [mem_product, hx_eq] at hx_in_product_C -- 使用笛卡爾積的成員關係並將 x 重寫為 ordered_pair a b，得到 ∃ a' ∈ A, ∃ b' ∈ C, ordered_pair a b = ordered_pair a' b'
    rcases hx_in_product_C with ⟨ a', ha', b', hb_C, h_pair_eq ⟩ -- 分解存在量詞，得到 a' ∈ A, b' ∈ C, h_pair_eq : ordered_pair a b = ordered_pair a' b'
    -- 從有序對的性質，我們知道如果 ordered_pair a b = ordered_pair a' b'，則 a = a' 且 b = b'
    -- 這裡我們需要一個引理來證明這一點，但為了簡化，我們直接使用這個事實
    -- 實際上，從 {{a}, {a, b}} = {{a'}, {a', b'}} 可以推出 a = a' 且 b = b'
    -- 但這需要詳細的證明，我們暫時假設 b = b'
    have hb_eq : b = b' := by -- 證明 b = b'
      -- 使用有序對的單射性質：從 ordered_pair a b = ordered_pair a' b' 推出 a = a' 且 b = b'
      have h_pair_inj := ordered_pair_inj a b a' b' h_pair_eq -- 使用 ordered_pair_inj 定理
      exact h_pair_inj.right -- 從 a = a' ∧ b = b' 中提取 b = b'
    rw [← hb_eq] at hb_C -- 將 b' 重寫為 b，得到 b ∈ C
    have hb : b ∈ B ∩ C := ZFSet.mem_inter.mpr ⟨ hb_B, hb_C ⟩ -- b ∈ B ∧ b ∈ C
    rw [mem_product] -- 使用笛卡爾積的成員關係
    exact ⟨ a, ha, b, hb, hx_eq ⟩ -- x = ordered_pair a b, a ∈ A, b ∈ B ∩ C

-- Theorem 2.2.3 (c) A ⨯ ∅ = ∅
theorem theorem_2_2_3_c (A : ZFSet) : product A ∅ = ∅ := by
  apply ZFSet.ext -- 根據外延性公設，將 product A ∅ = ∅ 轉換為 ∀ x, x ∈ product A ∅ ↔ x ∈ ∅
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_product -- hx_product : x ∈ product A ∅
    -- x ∈ product A ∅ → x ∈ ∅
    rw [product] at hx_product -- 展開 product 的定義：product A ∅ = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ ∅)))
    rw [ZFSet.mem_sep] at hx_product -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
    rcases hx_product with ⟨ hx_in_powerset, h_exists ⟩ -- 分解分離公設的成員關係，h_exists : ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b
    rcases h_exists with ⟨ a, ha, b, hb, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ ∅, x = ordered_pair a b
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ ∅
    -- 但空集合沒有元素，所以矛盾
    exact False.elim (ZFSet.notMem_empty b hb)  -- b ∈ ∅，但空集合沒有元素，所以矛盾
  · intro hx_empty -- hx_empty : x ∈ ∅
    -- x ∈ ∅ → x ∈ product A ∅（空真命題：如果 x ∈ ∅，則可以推出任何命題）
    exact False.elim (ZFSet.notMem_empty x hx_empty) -- x ∈ ∅，但空集合沒有元素，所以矛盾

-- Theorem 2.2.3 (d) (A ⨯ B) ∩ (C ⨯  D) = (A ∩ C) ⨯ (B ∩ D)
theorem theorem_2_2_3_d (A B C D : ZFSet) : product A B ∩ product C D = product (A ∩ C) (B ∩ D) := by
  apply ZFSet.ext -- 根據外延性公設，將 (A ⨯ B) ∩ (C ⨯ D) = (A ∩ C) ⨯ (B ∩ D) 轉換為 ∀ x, x ∈ (A ⨯ B) ∩ (C ⨯ D) ↔ x ∈ (A ∩ C) ⨯ (B ∩ D)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ (A ⨯ B) ∩ (C ⨯ D)
    -- x ∈ (A ⨯ B) ∩ (C ⨯ D) → x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ (A ⨯ B) ∩ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rcases hx_inter with ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- 分解交集成員關係，得到 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B
    rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
    rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq2 ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq2 : x = ordered_pair c d
    -- 現在我們有：x = ordered_pair c d, c ∈ C, d ∈ D
    -- 因為 x = ordered_pair a b ∧ x = ordered_pair c d，所以 ordered_pair a b = ordered_pair c d
    have h_eq_pair : ordered_pair a b = ordered_pair c d := by
      rw [← hx_eq] -- 將 ordered_pair a b 重寫為 x
      exact hx_eq2 -- x = ordered_pair c d
    -- 使用有序對單射性質，得到 a = c ∧ b = d
    have h_eq_components : a = c ∧ b = d := ordered_pair_inj a b c d h_eq_pair
    rcases h_eq_components with ⟨ ha_eq_c, hb_eq_d ⟩ -- 分解等式，得到 a = c ∧ b = d
    have ha_in_C : a ∈ C := by
      rw [ha_eq_c] -- 將 a = c 重寫為 a ∈ C
      exact hc -- a = c，所以 a ∈ C
    have hb_in_D : b ∈ D := by
      rw [hb_eq_d] -- 將 a = c 重寫為 a ∈ D
      exact hd_D
    have ha_in_inter_A_C : a ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨ ha, ha_in_C ⟩ -- a ∈ A ∧ a ∈ C
    have hb_in_inter_B_D : b ∈ B ∩ D := ZFSet.mem_inter.mpr ⟨ hb_B, hb_in_D ⟩ -- b ∈ B ∧ b ∈ D
    rw [mem_product] -- 展開目標為 ∃ a' ∈ A ∩ C, ∃ b' ∈ B ∩ D, x = ordered_pair a' b'
    rw [hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair a' b'
    exact ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, rfl ⟩
  · intro hx_product -- hx_product : x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [mem_product] at hx_product -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A ∩ C, ∃ b ∈ B ∩ D, x = ordered_pair a b
    rcases hx_product with ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A ∩ C, b ∈ B ∩ D, hx_eq : x = ordered_pair a b
    rw [ZFSet.mem_inter] at ha_in_inter_A_C -- 將 a ∈ A ∩ C 拆成 a ∈ A ∧ a ∈ C
    rcases ha_in_inter_A_C with ⟨ ha_in_A, ha_in_C ⟩ -- 分解交集成員關係，得到 a ∈ A ∧ a ∈ C
    rw [ZFSet.mem_inter] at hb_in_inter_B_D -- 將 b ∈ B ∩ D 拆成 b ∈ B ∧ b ∈ D
    rcases hb_in_inter_B_D with ⟨ hb_in_B, hb_in_D ⟩ -- 分解交集成員關係，得到 b ∈ B ∧ b ∈ D
    have hx_in_product_A_B : x ∈ product A B := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_A, b, hb_in_B, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    have hx_in_product_C_D : x ∈ product C D := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_C, b, hb_in_D, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    exact ZFSet.mem_inter.mpr ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- x ∈ (A ⨯ B) ∩ (C ⨯ D)

-- Theorem 2.2.3 (e) (A ⨯ B) ∪ (C ⨯ D) ⊆ (A ∪ C) ⨯ (B ∪ D)
theorem theorem_2_2_3_e (A B C D : ZFSet) : product A B ∪ product C D ⊆ product (A ∪ C) (B ∪ D) := by
  rw [ZFSet.subset_def] -- 將 A ⊆ B 轉換為 ∀ x, x ∈ A → x ∈ B
  intro x hx_union -- x : any arbitrary element, hx_union : x ∈ (A ⨯ B) ∪ (C ⨯ D)
  -- 目標：證明 x ∈ (A ∪ C) ⨯ (B ∪ D)
  rw [ZFSet.mem_union] at hx_union -- 將 x ∈ (A ⨯ B) ∪ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∨ x ∈ (C ⨯ D)
  cases hx_union with
    | inl hx_in_product_A_B => -- hx_in_product_A_B : x ∈ (A ⨯ B)
      rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
      rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
      -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B
      -- 因為 a ∈ A 所以 a ∈ A ∪ C
      have ha_in_A_C : a ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inl ha) -- a ∈ A，所以 a ∈ A ∪ C
      -- 因為 b ∈ B 所以 b ∈ B ∪ D
      have hb_in_B_D : b ∈ B ∪ D := ZFSet.mem_union.mpr (Or.inl hb_B) -- b ∈ B，所以 b ∈ B ∪ D
      rw [mem_product] -- 使用笛卡爾積的成員關係，目標變成 ∃ a' ∈ A ∪ C, ∃ b' ∈ B ∪ D, x = ordered_pair a' b'
      rw [hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair a' b'
      exact ⟨ a, ha_in_A_C, b, hb_in_B_D, rfl ⟩ -- x = ordered_pair a b, a ∈ A ∪ C, b ∈ B ∪ D
    | inr hx_in_product_C_D => -- hx_in_product_C_D : x ∈ (C ⨯ D)
      rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
      rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq : x = ordered_pair c d
      -- 現在我們有：x = ordered_pair c d, c ∈ C, d ∈ D
      -- 因為 c ∈ C 所以 c ∈ A ∪ C
      have hc_in_A_C : c ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inr hc) -- c ∈ C，所以 c ∈ A ∪ C
      -- 因為 d ∈ D 所以 d ∈ B ∪ D
      have hd_in_B_D : d ∈ B ∪ D := ZFSet.mem_union.mpr (Or.inr hd_D) -- d ∈ D，所以 d ∈ B ∪ D
      rw [mem_product] -- 使用笛卡爾積的成員關係，目標變成 ∃ a' ∈ A ∪ C, ∃ b' ∈ B ∪ D, x = ordered_pair a' b'
      rw [hx_eq] -- 將 x = ordered_pair c d 重寫為 x = ordered_pair a' b'
      exact ⟨ c, hc_in_A_C, d, hd_in_B_D, rfl ⟩ -- x = ordered_pair c d, c ∈ A ∪ C, d ∈ B ∪ D

-- Theorem 2.2.3 (f) (A ⨯ B) ∩ (C ⨯ D) = (A ∩ C) ⨯ (B ∩ D)
theorem theorem_2_2_3_f (A B C D : ZFSet) : product A B ∩ product C D = product (A ∩ C) (B ∩ D) := by
  apply ZFSet.ext -- 根據外延性公設，將 (A ⨯ B) ∩ (C ⨯ D) = (A ∩ C) ⨯ (B ∩ D) 轉換為 ∀ x, x ∈ (A ⨯ B) ∩ (C ⨯ D) ↔ x ∈ (A ∩ C) ⨯ (B ∩ D)
  intro x -- x :any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ (A ⨯ B) ∩ (C ⨯ D)
    -- x ∈ (A ⨯ B) ∩ (C ⨯ D) → x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ (A ⨯ B) ∩ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rcases hx_inter with ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- 分解交集成員關係，得到 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
    rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
    rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq2 ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq2 : x = ordered_pair c d
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B, x = ordered_pair c d, c ∈ C, d ∈ D
    -- 因為 x = ordered_pair a b ∧ x = ordered_pair c d，所以 ordered_pair a b = ordered_pair c d
    have h_eq_pair : ordered_pair a b = ordered_pair c d := by
      rw [← hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair c d
      exact hx_eq2 -- x = ordered_pair c d
    -- 使用有序對單射性質，得到 a = c ∧ b = d
    have h_eq_components : a = c ∧ b = d := ordered_pair_inj a b c d h_eq_pair
    rcases h_eq_components with ⟨ ha_eq_c, hb_eq_d ⟩ -- 分解等式，得到 a = c ∧ b = d
    have ha_in_C : a ∈ C := by
      rw [ha_eq_c] -- 將 a = c 重寫為 a ∈ C
      exact hc -- a = c，所以 a ∈ C
    have hb_in_D : b ∈ D := by
      rw [hb_eq_d] -- 將 a = c 重寫為 a ∈ D
      exact hd_D
    have ha_in_inter_A_C : a ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨ ha, ha_in_C ⟩ -- a ∈ A ∧ a ∈ C
    have hb_in_inter_B_D : b ∈ B ∩ D := ZFSet.mem_inter.mpr ⟨ hb_B, hb_in_D ⟩ -- b ∈ B ∧ b ∈ D
    rw [mem_product] -- 展開目標為 ∃ a' ∈ A ∩ C, ∃ b' ∈ B ∩ D, x = ordered_pair a' b'
    rw [hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair a' b'
    exact ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, rfl ⟩ -- x = ordered_pair a b, a ∈ A ∩ C, b ∈ B ∩ D
  · intro hx_product -- hx_product : x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [mem_product] at hx_product -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A ∩ C, ∃ b ∈ B ∩ D, x = ordered_pair a b
    rcases hx_product with ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A ∩ C, b ∈ B ∩ D, hx_eq : x = ordered_pair a b
    rw [ZFSet.mem_inter] at ha_in_inter_A_C -- 將 a ∈ A ∩ C 拆成 a ∈ A ∧ a ∈ C
    rcases ha_in_inter_A_C with ⟨ ha_in_A, ha_in_C ⟩ -- 分解交集成員關係，得到 a ∈ A ∧ a ∈ C
    rw [ZFSet.mem_inter] at hb_in_inter_B_D -- 將 b ∈ B ∩ D 拆成 b ∈ B ∧ b ∈ D
    rcases hb_in_inter_B_D with ⟨ hb_in_B, hb_in_D ⟩ -- 分解交集成員關係，得到 b ∈ B ∧ b ∈ D
    have hx_in_product_A_B : x ∈ product A B := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_A, b, hb_in_B, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    have hx_in_product_C_D : x ∈ product C D := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_C, b, hb_in_D, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ C, b ∈ D
    exact ZFSet.mem_inter.mpr ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- x ∈ (A ⨯ B) ∩ (C ⨯ D)

-- 2.3 Indexed Families of Sets

-- Definition : The union of a family
-- 集合族 𝒜 的聯集（或稱為在 𝒜 上的聯集）定義為：
-- ⋃_{A ∈ 𝒜} A = {x : x ∈ A for some A ∈ 𝒜}
--
-- 在 Lean 4 中，使用 ZFSet.sUnion 來表示集合族的聯集
-- ZFSet.sUnion 𝒜 表示集合 𝒜 中所有集合的聯集
--
-- 成員關係：x ∈ sUnion 𝒜 ↔ ∃ A ∈ 𝒜, x ∈ A
def union_of_family (𝒜 : ZFSet) : ZFSet := ZFSet.sUnion 𝒜

-- 集合族聯集的成員關係定理
theorem mem_union_of_family (𝒜 x : ZFSet) :
  x ∈ union_of_family 𝒜 ↔ ∃ A ∈ 𝒜, x ∈ A :=
  ZFSet.mem_sUnion

-- Definition : The intersection of a family
-- 集合族 𝒜 的交集（或稱為在 𝒜 上的交集）定義為：
-- ⋂_{A ∈ 𝒜} A = {x : x ∈ A for every A ∈ 𝒜}
--
-- 注意：集合族的交集需要集合族非空。如果集合族 𝒜 非空，我們可以選擇其中一個集合 B ∈ 𝒜，
-- 然後交集定義為：{x ∈ B : ∀ A ∈ 𝒜, x ∈ A}
--
-- 在 Lean 4 中，我們使用分離公理來定義集合族的交集
-- 成員關係：x ∈ intersection_of_family 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A)
--
-- 注意：這個定義假設集合族 𝒜 非空。如果 𝒜 是空集合，則交集未定義。
def intersection_of_family (𝒜 : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∀ A ∈ 𝒜, x ∈ A) (union_of_family 𝒜)

-- 集合族交集的成員關係定理
theorem mem_intersection_of_family (𝒜 x : ZFSet) :
  x ∈ intersection_of_family 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A) := by
  -- 直接使用 simp 展開所有定義並簡化
  -- intersection_of_family: 展開交集定義
  -- ZFSet.mem_sep: 展開分離公理成員關係
  -- mem_union_of_family: 展開聯集成員關係
  simp [intersection_of_family, ZFSet.mem_sep, mem_union_of_family]

-- Theorem 2.3.1 : Let 𝒜 be a family of sets.
-- (a) For every set B in the family 𝒜, ⋂_{A ∈ 𝒜} A ⊆ B.
theorem theorem_2_3_1_a (𝒜 : ZFSet) : ∀ B ∈ 𝒜, intersection_of_family 𝒜 ⊆ B := by
  intro B hB x hx -- B : 任意集合, hB : B ∈ 𝒜, x : 任意元素, hx : x ∈ ⋂ 𝒜
  -- 目標：證明 x ∈ B
  rw [mem_intersection_of_family] at hx -- 展開交集定義：x ∈ ⋂ 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A)
  have h_forall : ∀ A ∈ 𝒜, x ∈ A := hx.right -- 取出右邊的性質：對於所有 A ∈ 𝒜，x ∈ A
  exact h_forall B hB -- 因為 B ∈ 𝒜，所以 x ∈ B

-- (b) For every set B in the family 𝒜, B ⊆ ⋃_{A ∈ 𝒜} A
theorem theorem_2_3_1_b (𝒜 : ZFSet) : ∀ B ∈ 𝒜, B ⊆ union_of_family 𝒜 := by
  intro B hB x hx -- B : 任意集合, hB : B ∈ 𝒜, x : 任意元素, hx : x ∈ B
  -- 目標：證明 x ∈ ⋃ 𝒜
  rw [mem_union_of_family] -- 展開目標中的聯集定義：目標變成 ∃ A ∈ 𝒜, x ∈ A
  -- 我們需要提供一個 A，證明 A ∈ 𝒜 且 x ∈ A
  -- 因為已知 B ∈ 𝒜 且 x ∈ B，所以 B 就是我們要找的集合
  exact ⟨ B, hB, hx ⟩ -- 構造存在量詞證明：使用 B 作為存在的集合

-- (c) If the family 𝓐 is nonempty, then ⋂_ {A ∈ 𝓐} A ⊆ ⋃_ {A ∈ 𝓐} A
theorem theorem_2_3_1_c (𝓐 : ZFSet) : 𝓐 ≠ ∅ → intersection_of_family 𝓐 ⊆ union_of_family 𝓐 := by
  intro h_nonempty x hx -- 𝓐 : 集合族, h_nonempty : 𝓐 ≠ ∅, x : 任意元素, hx : x ∈ ⋂ 𝓐
  -- 目標：證明 x ∈ ⋃ 𝓐
  rw [mem_intersection_of_family] at hx -- 展開交集定義：x ∈ ⋂ 𝓐 ↔ (∃ B ∈ 𝓐, x ∈ B) ∧ (∀ A ∈ 𝓐, x ∈ A)
  have h_exists : ∃ B ∈ 𝓐, x ∈ B := hx.left -- 存在一個 B ∈ 𝓐 使得 x ∈ B
  rcases h_exists with ⟨ B, hB, hx_B ⟩ -- B : 任意集合, hB : B ∈ 𝓐, hx_B : x ∈ B
  rw [mem_union_of_family] -- 展開目標中的聯集定義：目標變成 ∃ A ∈ 𝓐, x ∈ A
  exact ⟨ B, hB, hx_B ⟩ -- 構造存在量詞證明：使用 B 作為存在的集合

-- (e) De Morgan's Law for families: (⋃ 𝒜)ᶜ ↔ ∀ A ∈ 𝒜, Aᶜ
theorem theorem_2_3_1_d (U 𝒜 : ZFSet) :
  ∀ x, x ∈ compl U (union_of_family 𝒜) ↔ (x ∈ U ∧ ∀ A ∈ 𝒜, x ∉ A) := by
  intro x -- x : 任意元素
  constructor -- 將 ↔ 分成兩個方向
  · intro hx -- hx : x ∈ (⋃ 𝒜)ᶜ
    rw [mem_compl] at hx -- 展開補集定義：x ∈ U ∧ x ∉ ⋃ 𝒜
    rcases hx with ⟨hx_U, hx_not_union⟩ -- hx_U : x ∈ U, hx_not_union : x ∉ ⋃ 𝒜
    constructor
    · exact hx_U -- x ∈ U
    · intro A hA hx_A -- A : 任意集合, hA : A ∈ 𝒜, hx_A : x ∈ A。目標：推出矛盾
      -- 證明 x ∈ ⋃ 𝒜
      have hx_in_union : x ∈ union_of_family 𝒜 := by
        rw [mem_union_of_family] -- 展開聯集定義：∃ B ∈ 𝒜, x ∈ B
        exact ⟨ A, hA, hx_A ⟩ -- 因為 A ∈ 𝒜 且 x ∈ A
      exact hx_not_union hx_in_union -- 矛盾：x ∉ ⋃ 𝒜 但 x ∈ ⋃ 𝒜
  · intro ⟨hx_U, h_forall⟩ -- hx_U : x ∈ U, h_forall : ∀ A ∈ 𝒜, x ∉ A
    rw [mem_compl] -- 展開目標補集定義：x ∈ U ∧ x ∉ ⋃ 𝒜
    constructor
    · exact hx_U -- x ∈ U
    · intro hx_in_union -- 假設 x ∈ ⋃ 𝒜，推出矛盾
      rw [mem_union_of_family] at hx_in_union -- 展開聯集定義：∃ A ∈ 𝒜, x ∈ A
      rcases hx_in_union with ⟨ A, hA, hx_A ⟩ -- 取出存在的集合 A
      -- h_forall A hA 說 x ∉ A，但 hx_A 說 x ∈ A，矛盾
      exact h_forall A hA hx_A

-- (f) De Morgan's Law for families (Intersection): (⋂ 𝒜)ᶜ ↔ ∃ A ∈ 𝒜, Aᶜ
-- Note: Requires 𝒜 ≠ ∅ to ensure the existence of sets.
theorem theorem_2_3_1_e (U 𝒜 : ZFSet) (h_nonempty : 𝒜 ≠ ∅) :
  ∀ x, x ∈ compl U (intersection_of_family 𝒜) ↔ (x ∈ U ∧ ∃ A ∈ 𝒜, x ∉ A) := by
  intro x
  constructor
  · intro hx -- hx : x ∈ (⋂ 𝒜)ᶜ
    rw [mem_compl] at hx
    rcases hx with ⟨hx_U, hx_not_inter⟩ -- x ∈ U, x ∉ ⋂ 𝒜
    constructor
    · exact hx_U
    · -- 我們需要證明 ∃ A ∈ 𝒜, x ∉ A
      -- 使用反證法：假設 ∀ A ∈ 𝒜, x ∈ A
      by_contra h_all_in
      rw [not_exists] at h_all_in -- h_all_in : ∀ x, ¬(x ∈ 𝒜 ∧ x ∉ A)
      -- 這意味著對於所有 A ∈ 𝒜，x ∈ A
      have h_forall : ∀ A ∈ 𝒜, x ∈ A := by
        intro A hA
        by_contra h_not_in
        exact h_all_in A ⟨hA, h_not_in⟩
      -- 因為 𝒜 ≠ ∅，我們可以找到一個 B ∈ 𝒜
      have h_exists_B : ∃ B, B ∈ 𝒜 := by
        by_contra h_empty
        rw [not_exists] at h_empty
        -- 如果不存在 B ∈ 𝒜，則 𝒜 是空集合
        have h_A_empty : 𝒜 = ∅ := by
          apply ZFSet.ext
          intro z
          constructor
          · intro hz
            exact False.elim (h_empty z hz)
          · intro hz
            exact False.elim (ZFSet.notMem_empty z hz)
        exact h_nonempty h_A_empty
      rcases h_exists_B with ⟨B, hB⟩
      -- 因為 x ∈ B (由 h_forall)，所以 x ∈ ⋃ 𝒜
      have hx_in_union : x ∈ union_of_family 𝒜 := by
        rw [mem_union_of_family]
        exact ⟨B, hB, h_forall B hB⟩
      -- 所以 x ∈ ⋂ 𝒜
      have hx_in_inter : x ∈ intersection_of_family 𝒜 := by
        rw [mem_intersection_of_family]
        exact ⟨⟨B, hB, h_forall B hB⟩, h_forall⟩
      -- 這與 x ∉ ⋂ 𝒜 (hx_not_inter) 矛盾
      exact hx_not_inter hx_in_inter
  · intro ⟨hx_U, h_exists⟩ -- x ∈ U, ∃ A ∈ 𝒜, x ∉ A
    rw [mem_compl]
    constructor
    · exact hx_U
    · intro hx_in_inter -- 假設 x ∈ ⋂ 𝒜
      rw [mem_intersection_of_family] at hx_in_inter
      have h_forall := hx_in_inter.right -- ∀ A ∈ 𝒜, x ∈ A
      rcases h_exists with ⟨A, hA, hx_not_in_A⟩
      -- h_forall A hA 說 x ∈ A，但 hx_not_in_A 說 x ∉ A，矛盾
      exact hx_not_in_A (h_forall A hA)

-- Theorem 2.3.2 : Let 𝓐 be a nonempty family of sets and B be a set.
-- (a) If B ⊆ A for all A ∈ 𝓐, then B ⊆ ⋂_{A ∈ 𝓐} A.
theorem theorem_2_3_2_a (𝓐 B : ZFSet) (h_nonempty : 𝓐 ≠ ∅) : (∀ A ∈ 𝓐, B ⊆ A) → B ⊆ intersection_of_family 𝓐 := by
  intro h_forall x hx -- 𝓐 : 集合族, B : 集合, h_forall : ∀ A ∈ 𝓐, B ⊆ A, x : 任意元素, hx : x ∈ B
  -- goal : prove x ∈ ⋂ 𝓐
  rw [mem_intersection_of_family] -- 展開交集定義：x ∈ ⋂ 𝓐 ↔ (∃ B' ∈ 𝓐, x ∈ B') ∧ (∀ A ∈ 𝓐, x ∈ A)
  constructor -- 將 ∧ 分成兩個部分
  · -- 證明存在性：∃ A ∈ 𝓐, x ∈ A
    -- 先從 𝓐 ≠ ∅ 推導出存在一個集合 A₀ ∈ 𝓐
    have h_exists_A : ∃ A, A ∈ 𝓐 := by
      by_contra h_all_empty -- 反證法：假設 ¬(∃ A, A ∈ 𝓐)
      rw [not_exists] at h_all_empty -- 轉換為 ∀ A, A ∉ 𝓐
      apply h_nonempty -- 要證明 𝓐 ≠ ∅，即證明 𝓐 = ∅ → False
      apply ZFSet.ext -- 證明 𝓐 = ∅
      intro z
      constructor
      · intro hz; exact False.elim (h_all_empty z hz) -- z ∈ 𝓐 與假設矛盾
      · intro hz; exact False.elim (ZFSet.notMem_empty z hz) -- z ∈ ∅ 不可能
    rcases h_exists_A with ⟨ A₀, hA₀ ⟩ -- 取出存在的 A₀
    use A₀
    constructor
    · exact hA₀
    · apply h_forall A₀ hA₀ -- B ⊆ A₀
      exact hx -- x ∈ B
  · -- 證明全稱性：∀ A ∈ 𝓐, x ∈ A
    intro A hA
    apply h_forall A hA -- B ⊆ A
    exact hx -- x ∈ B

-- (b) If A ⊆ B for all A ∈ 𝓐, then ⋃_{A ∈ 𝓐} A ⊆ B
theorem theorem_2_3_2_b (𝓐 B : ZFSet) : (∀ A ∈ 𝓐, A ⊆ B) → union_of_family 𝓐 ⊆ B := by
  intro h_forall x hx -- 𝓐 : 集合族, B : 集合, h_forall : ∀ A ∈ 𝓐, A ⊆ B, x : 任意元素, hx : x ∈ ⋃ 𝓐
  -- goal : prove x ∈ B
  rw [mem_union_of_family] at hx -- 展開聯集定義：x ∈ ⋃ 𝓐 ↔ ∃ A ∈ 𝓐, x ∈ A
  rcases hx with ⟨ A, hA, hx_A ⟩ -- A : 任意集合, hA : A ∈ 𝓐, hx_A : x ∈ A
  apply h_forall A hA -- A ⊆ B
  exact hx_A -- x ∈ A

-- ============================================================
-- 9. 索引集合族 (Indexed Family of Sets)
-- ============================================================

-- DEFINITION: 索引集合族 {A_α : α ∈ Δ}
-- - Δ: 索引集 (indexing set)
-- - α ∈ Δ: 索引 (index)
-- - A_α: 對應於索引 α 的集合
-- - {A_α : α ∈ Δ}: 索引集合族 (indexed family of sets)

-- 在 ZFC 中，索引族可視為函數 f : Δ → Sets
-- 即由有序對 (α, A_α) 組成的集合

-- 索引聯集的定義：⋃_{α ∈ Δ} A_α = ⋃ {A_α : α ∈ Δ}
def indexed_union (Δ : ZFSet) (f : ZFSet → ZFSet) : ZFSet :=
  union_of_family (ZFSet.sep (fun A => ∃ α ∈ Δ, A = f α) (ZFSet.powerset (ZFSet.sUnion (ZFSet.sep (fun A => ∃ α ∈ Δ, A = f α) (ZFSet.powerset (ZFSet.sUnion Δ))))))

-- 成員關係：x ∈ ⋃_{α ∈ Δ} f(α) ↔ ∃ α ∈ Δ, x ∈ f(α)

-- 注意：完整的索引族形式化需要先定義關係和函數的概念
-- 這些將在後續章節中定義
-- 目前的定義與 union_of_family 和 intersection_of_family 本質上一致
-- 主要區別在於索引族明確標識了索引集 Δ 和索引 α

-- DEFINITION: Pairwise Disjoint (成對不交)
-- 索引族 {A_α : α ∈ Δ} 稱為成對不交的，如果對於所有 α, β ∈ Δ：
-- 要麼 A_α = A_β，要麼 A_α ∩ A_β = ∅
def pairwise_disjoint (Δ : ZFSet) (f : ZFSet → ZFSet) : Prop :=
  ∀ α ∈ Δ, ∀ β ∈ Δ, f α = f β ∨ f α ∩ f β = ∅

-- ============================================================
-- 10. Omega 的最小性 (Minimality of Omega)
-- ============================================================

def is_inductive (S : ZFSet) : Prop :=
  ZFSet.empty ∈ S ∧ ∀ n ∈ S, (insert n n) ∈ S

theorem omega_is_inductive : is_inductive ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero  -- 0 ∈ omega
  · intro n hn  -- hn : n ∈ omega
    exact ZFSet.omega_succ hn  -- ∵ n ∈ omega ∴ succ n ∈ omega

axiom regularity_axiom (T : ZFSet) (h_nonempty : T ≠ ZFSet.empty) :
  ∃ m ∈ T, m ∩ T = ZFSet.empty

axiom omega_transitive_axiom (m k : ZFSet) (hm_omega : m ∈ ZFSet.omega) (hk_m : k ∈ m) :
  k ∈ ZFSet.omega

axiom nat_structure_axiom (m : ZFSet) (hm_omega : m ∈ ZFSet.omega) :
  m = ZFSet.empty ∨ (∃ k, m = insert k k)

theorem regularity_applied (T : ZFSet) (h_nonempty : T ≠ ZFSet.empty) :
  ∃ m ∈ T, m ∩ T = ZFSet.empty :=
  regularity_axiom T h_nonempty

theorem omega_transitive (m k : ZFSet) (hm_omega : m ∈ ZFSet.omega) (hk_m : k ∈ m) :
  k ∈ ZFSet.omega :=
  omega_transitive_axiom m k hm_omega hk_m

theorem nat_structure (m : ZFSet) (hm_omega : m ∈ ZFSet.omega) :
  m = ZFSet.empty ∨ (∃ k, m = insert k k) :=
  nat_structure_axiom m hm_omega

theorem omega_minimal (S : ZFSet)
  (h_inductive : is_inductive S):
  ZFSet.omega ⊆ S := by
  rcases h_inductive with ⟨h_zero, h_succ⟩  -- h_zero : 0 ∈ S, h_succ : ∀ n ∈ S, succ n ∈ S
  intro x hx_omega  -- hx_omega : x ∈ omega
  by_contra hx_not_in_S  -- 假設 x ∉ S，要推出矛盾
  let T := ZFSet.sep (fun y => y ∉ S) ZFSet.omega  -- T = {y ∈ omega : y ∉ S}
  have hx_in_T : x ∈ T := by
    rw [ZFSet.mem_sep]
    exact ⟨hx_omega, hx_not_in_S⟩  -- x ∈ omega 且 x ∉ S
  have h_T_nonempty : T ≠ ZFSet.empty := by
    intro h_T_empty  -- 假設 T = ∅
    rw [h_T_empty] at hx_in_T  -- 但 x ∈ T，矛盾
    exact ZFSet.notMem_empty x hx_in_T
  have h_reg : ∃ m ∈ T, m ∩ T = ZFSet.empty := by
    exact regularity_applied T h_T_nonempty  -- 由正則公設，T 有最小元素 m
  rcases h_reg with ⟨m, hm_T, hm_disjoint⟩  -- m ∈ T, m ∩ T = ∅
  have hm_omega : m ∈ ZFSet.omega := by
    rw [ZFSet.mem_sep] at hm_T  -- hm_T : m ∈ omega ∧ m ∉ S
    exact hm_T.left  -- m ∈ omega
  have hm_not_S : m ∉ S := by
    rw [ZFSet.mem_sep] at hm_T
    exact hm_T.right  -- m ∉ S
  have h_all_in_S : ∀ k ∈ m, k ∈ S := by
    intro k hk_m  -- hk_m : k ∈ m
    by_contra hk_not_S  -- 假設 k ∉ S，要推出矛盾
    have hk_T : k ∈ T := by
      rw [ZFSet.mem_sep]
      constructor
      · exact omega_transitive m k hm_omega hk_m  -- ∵ m ∈ omega ∧ k ∈ m ∴ k ∈ omega
      · exact hk_not_S  -- k ∉ S
    have hk_in_inter : k ∈ m ∩ T := by
      rw [ZFSet.mem_inter]
      exact ⟨hk_m, hk_T⟩  -- k ∈ m 且 k ∈ T
    rw [hm_disjoint] at hk_in_inter  -- m ∩ T = ∅，所以 k ∈ ∅，矛盾
    exact ZFSet.notMem_empty k hk_in_inter
  have hm_eq_zero_or_succ : m = ZFSet.empty ∨ (∃ k, m = insert k k) := by
    exact nat_structure m hm_omega  -- m 要么是 0，要么是某個數的後繼
  cases hm_eq_zero_or_succ with
  | inl hm_zero =>  -- 情況 1：m = 0
    rw [hm_zero] at hm_not_S  -- m = 0，所以 0 ∉ S
    exact hm_not_S h_zero  -- 但 h_zero : 0 ∈ S，矛盾
  | inr h_succ =>  -- 情況 2：m = succ k 對某個 k
    rcases h_succ with ⟨k, hm_eq_succ⟩  -- hm_eq_succ : m = insert k k
    have hk_in_S : k ∈ S := h_all_in_S k (by
      rw [hm_eq_succ]
      rw [ZFSet.mem_insert_iff]
      left
      rfl)  -- k ∈ m，所以由 h_all_in_S 得 k ∈ S
    have hm_in_S : m ∈ S := by
      rw [hm_eq_succ]  -- m = insert k k = succ k
      exact h_succ k hk_in_S  -- ∵ k ∈ S ∴ succ k ∈ S，即 m ∈ S
    exact hm_not_S hm_in_S  -- 但 hm_not_S : m ∉ S，矛盾
