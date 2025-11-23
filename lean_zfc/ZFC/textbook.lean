import Mathlib.SetTheory.ZFC.Basic
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
theorem thm_2_2_1_f (A : ZFSet) : A ∪ A = A := by
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
theorem thm_2_2_1_g (A : ZFSet) : set_diff A ∅ = A := by
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
theorem thm_2_2_1_h (A : ZFSet) : set_diff ∅ A = ∅ := by
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
theorem thm_2_2_1_i (A B : ZFSet) : A ∪ B = B ∪ A := by
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
