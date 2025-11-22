import Mathlib.SetTheory.ZFC.Basic
--2.1 Basic Concepts of Set Theory
--Theorem 2.1.1 (a) for every set A, ∅ ⊆ A
-- 空集是任何集合的子集（空真命题：空集没有元素，所以条件永远为假）
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- hx : x ∈ ∅，但空集没有元素，这是矛盾的
  have : False := ZFSet.notMem_empty x hx
  -- 从矛盾可以推出任何东西（包括 x ∈ A）
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
theorem thm2_1_2 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h --h: A = ∅ ∧ B = ∅
  rcases h with ⟨ hA, hB ⟩ --hA: A = ∅, hB: B = ∅
  -- 使用 calc 进行链式等式证明：A = ∅ = B
  calc
    A = ∅ := hA --hA: A = ∅
    _ = B := hB.symm  -- hB : B = ∅，所以 hB.symm : ∅ = B

--Theorem 2.1.3 For any sets A and B, A ⊆ B and A ≠ ∅ → B ≠ ∅
theorem thm2_1_3(A B : ZFSet) : (A ⊆ B ∧ A ≠ ∅) → B ≠ ∅ := by
  -- 引入前提条件
  intro h --h: A ⊆ B ∧ A ≠ ∅
  -- 分解合取命题：hxAB: A ⊆ B, hA_nonempty: A ≠ ∅
  rcases h with ⟨ hxAB, hA_nonempty ⟩
  -- 使用反证法：假设 B = ∅
  by_contra hB_empty --hB_empty: B = ∅
  -- 从 A ⊆ B 和 B = ∅ 推出 A ⊆ ∅
  have hA_subset_empty : A ⊆ ∅ := by
    rw [hB_empty] at hxAB -- 将 hxAB 中的 B 替换为 ∅
    exact hxAB
  -- 证明 A = ∅（因为 A ⊆ ∅ 意味着 A 没有元素）
  have hA_empty : A = ∅ := by
    -- 使用外延性公理：A = ∅ ↔ (∀ x, x ∈ A ↔ x ∈ ∅)
    -- 执行 apply ZFSet.ext 后，目标从 "A = ∅" 变成了 "∀ x, x ∈ A ↔ x ∈ ∅"
    apply ZFSet.ext
    -- intro x 的作用：引入任意的元素 x
    -- 要证明 "∀ x, x ∈ A ↔ x ∈ ∅"，我们需要：
    --   1) 取任意元素 x（intro x）
    --   2) 证明 "x ∈ A ↔ x ∈ ∅"
    intro x
    -- constructor 将双条件 ↔ 分解成两个方向：x ∈ A → x ∈ ∅ 和 x ∈ ∅ → x ∈ A
    constructor
    · intro hx -- x ∈ A
      -- 由于 A ⊆ ∅，所以 x ∈ ∅，但空集没有元素，这是矛盾的
      have : x ∈ ∅ := hA_subset_empty hx
      exact False.elim (ZFSet.notMem_empty x this)
    · intro hx -- x ∈ ∅
      -- 空集没有元素，x ∈ ∅ 本身就是矛盾的
      exact False.elim (ZFSet.notMem_empty x hx)
  -- 推出矛盾：hA_empty : A = ∅ 与 hA_nonempty : A ≠ ∅ 矛盾
  exact hA_nonempty hA_empty

--Theorem 2.1.5 Let A and B be sets. Then A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)
-- 其中 𝒫(A) 表示 A 的幂集（所有 A 的子集组成的集合）
theorem thm2_1_5(A B : ZFSet) : A ⊆ B ↔ ZFSet.powerset A ⊆ ZFSet.powerset B := by
  constructor
  -- 方向 1：A ⊆ B → 𝒫(A) ⊆ 𝒫(B)
  · intro h x hx --h : A ⊆ B, hx : x ∈ 𝒫(A)，即 x ∈ ZFSet.powerset A
    -- 要证明 x ∈ 𝒫(B)，即 x ∈ ZFSet.powerset B，需要证明 x ⊆ B
    -- 首先，从 x ∈ 𝒫(A) 推出 x ⊆ A
    have hx_subset_A : x ⊆ A := ZFSet.mem_powerset.mp hx
    -- 由于 x ⊆ A 且 A ⊆ B，所以 x ⊆ B
    have hx_subset_B : x ⊆ B := fun y hy => h (hx_subset_A hy)
    -- 因此 x ∈ 𝒫(B)
    exact ZFSet.mem_powerset.mpr hx_subset_B
  -- 方向 2：𝒫(A) ⊆ 𝒫(B) → A ⊆ B
  · intro h x hx --h : 𝒫(A) ⊆ 𝒫(B), hx : x ∈ A
    -- 要证明 x ∈ B
    -- 首先，注意到 {x} 是 A 的子集（因为 x ∈ A）
    -- 但更简单的方法：注意到 A 本身是 A 的子集，所以 A ∈ 𝒫(A)
    -- 由于 𝒫(A) ⊆ 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    -- 但我们需要证明的是对于任意 x ∈ A，有 x ∈ B
    -- 实际上，我们需要使用 A 本身：A ∈ 𝒫(A)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun y hy => hy)
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := h hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B
    -- 由于 x ∈ A 且 A ⊆ B，所以 x ∈ B
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
    · exact fun hx => hA_subset_C hx  -- hA_subset_C : A ⊆ C，应用到 x 和 hx : x ∈ A 得到 x ∈ C
    · exact fun hx => hC_subset_A hx  -- hC_subset_A : C ⊆ A，应用到 x 和 hx : x ∈ C 得到 x ∈ A
  -- C ⊆ A ∧ A ⊆ B → C ⊆ B
  have hC_subset_B : C ⊆ B := theorem_2_1_1_c C A B ⟨ hC_subset_A, hA_subset_B ⟩
  -- C ⊆ B ∧ B ⊆ C → B = C
  have hB_eq_C : B = C := by
    apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => hB_subset_C hx  -- hB_subset_C : B ⊆ C，应用到 x 和 hx : x ∈ B 得到 x ∈ C
    · exact fun hx => hC_subset_B hx  -- hC_subset_B : C ⊆ B，应用到 x 和 hx : x ∈ C 得到 x ∈ B
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
    rw [h]  -- 如果 A = B，直接重写即可得到 𝒫(A) = 𝒫(B)
  · intro h -- h: 𝒫(A) = 𝒫(B)
    -- 步骤 1：证明 A ∈ 𝒫(A)（因为 A ⊆ A）
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun x hx => hx)
    -- 步骤 2：由于 𝒫(A) = 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := by
      rw [← h]  -- 将 𝒫(B) 重写为 𝒫(A)
      exact hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B

    -- 步骤 3：类似地，B ∈ 𝒫(B)，所以 B ∈ 𝒫(A)，即 B ⊆ A
    have hB_in_powerset_B : B ∈ ZFSet.powerset B := ZFSet.mem_powerset.mpr (fun x hx => hx)
    have hB_in_powerset_A : B ∈ ZFSet.powerset A := by
      rw [h]  -- 将 𝒫(A) 重写为 𝒫(B)
      exact hB_in_powerset_B
    have hB_subset_A : B ⊆ A := ZFSet.mem_powerset.mp hB_in_powerset_A

    -- 步骤 4：由 A ⊆ B 和 B ⊆ A，使用外延性公理得到 A = B
    -- 外延性公理：两个集合相等当且仅当它们有相同的元素
    apply ZFSet.ext  -- 将 A = B 转换为 ∀ x, x ∈ A ↔ x ∈ B
    intro x  -- 引入任意元素 x，需要证明 x ∈ A ↔ x ∈ B
    constructor  -- 将双条件 ↔ 分解成两个方向
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
-- 差集（Set Difference）的定义
-- ============================================
-- 数学定义：A - B = {x : x ∈ A ∧ x ∉ B}
-- 在 ZFC 中，差集使用分离公理（Axiom Schema of Separation）定义
-- 分离公理：对于任意集合 A 和性质 P，存在集合 {x ∈ A : P x}
--
-- 语法解析：
--   def set_diff             定义函数 set_diff
--   (A B : ZFSet)           参数：A 和 B 都是 ZFSet 类型
--   : ZFSet                 返回类型：ZFSet（一个集合）
--   :=                      定义符号
--   ZFSet.sep               使用分离公理
--   (fun x => x ∉ B)        性质：lambda 函数，表示"x 不在 B 中"
--   A                       源集合：从 A 中分离元素
--
-- 含义：set_diff A B = {x ∈ A : x ∉ B}
--       即从集合 A 中选出所有不在 B 中的元素
def set_diff (A B : ZFSet) : ZFSet := ZFSet.sep (fun x => x ∉ B) A

-- 差集的成员关系：x ∈ A - B ↔ x ∈ A ∧ x ∉ B
theorem mem_diff (A B x : ZFSet) : x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B :=
  ZFSet.mem_sep

-- Definition : Sets A and B are disjoint if A ∩ B = ∅
theorem disjoint (A B : ZFSet) : A ∩ B = ∅ ↔ ∀x, x ∈ A → x ∉ B := by
  constructor
  -- 方向 1：A ∩ B = ∅ → ∀x, x ∈ A → x ∉ B
  · intro h x hx  -- h: A ∩ B = ∅, x: 任意元素, hx: x ∈ A
    -- 要证明 x ∉ B，使用反证法
    by_contra hx_in_B  -- hx_in_B: x ∈ B（反证假设）
    -- 如果 x ∈ A 且 x ∈ B，那么 x ∈ A ∩ B
    have hx_in_inter : x ∈ A ∩ B := by
      rw [ZFSet.mem_inter]
      exact ⟨hx, hx_in_B⟩
    -- 但 A ∩ B = ∅，所以 x ∈ ∅，这是矛盾的
    rw [h] at hx_in_inter  -- 将 A ∩ B 重写为 ∅
    exact ZFSet.notMem_empty x hx_in_inter

  -- 方向 2：∀x, x ∈ A → x ∉ B → A ∩ B = ∅
  · intro h  -- h: ∀x, x ∈ A → x ∉ B
    -- 要证明 A ∩ B = ∅，使用外延性公理
    apply ZFSet.ext
    intro x
    constructor
    -- 方向 2.1：x ∈ A ∩ B → x ∈ ∅
    · intro hx_inter  -- hx_inter: x ∈ A ∩ B
      -- 从 x ∈ A ∩ B 推出 x ∈ A 且 x ∈ B
      have hx_pair : x ∈ A ∧ x ∈ B := by
        rw [ZFSet.mem_inter] at hx_inter
        exact hx_inter
      -- 由 h: ∀x, x ∈ A → x ∉ B，应用到 x 和 hx_pair.left
      have hx_notin_B : x ∉ B := h x hx_pair.left
      -- 但 hx_pair.right 说 x ∈ B，矛盾
      -- hx_notin_B : x ∉ B 即 x ∈ B → False
      -- hx_pair.right : x ∈ B
      -- 所以 hx_notin_B hx_pair.right : False
      -- 从矛盾可以推出任何东西（包括 x ∈ ∅）
      exact False.elim (hx_notin_B hx_pair.right)
    -- 方向 2.2：x ∈ ∅ → x ∈ A ∩ B（空真命题）
    · intro hx_empty  -- hx_empty: x ∈ ∅
      -- 空集没有元素，这是矛盾的
      exact False.elim (ZFSet.notMem_empty x hx_empty)

-- Theorem 2.2.1 (a) A ⊆ A ∪ B
theorem thm_2_2_1_a (A B : ZFSet) : A ⊆ A ∪ B := by
  intro x hx -- x: 任意元素, hx: x ∈ A
  -- 从 x ∈ A 推出 x ∈ A ∨ x ∈ B（用 Or.inl），再推出 x ∈ A ∪ B（用 mem_union.mpr）
  have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx)
  exact hx_in_union

-- Theorem 2.2.1 (b) A ∩ B ⊆ A
theorem thm_2_2_1_b (A B : ZFSet) : A ∩ B ⊆ A := by
  intro x hx -- x: 任意元素, hx: x ∈ A ∩ B
  -- mem_inter.mp: x ∈ A ∩ B → x ∈ A ∧ x ∈ B（从左到右）
  -- mem_inter.mpr: x ∈ A ∧ x ∈ B → x ∈ A ∩ B（从右到左）
  -- 这里需要从 x ∈ A ∩ B 推出 x ∈ A ∧ x ∈ B，所以用 .mp
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
  constructor  -- 将 ↔ 分解成两个方向

  -- 方向 1：x ∈ A ∪ ∅ → x ∈ A
  · intro hx_union  -- hx_union: x ∈ A ∪ ∅
    -- 从 x ∈ A ∪ ∅ 推出 x ∈ A ∨ x ∈ ∅
    rw [ZFSet.mem_union] at hx_union
    -- 此时 hx_union 的类型是 x ∈ A ∨ x ∈ ∅（析取命题）
    --
    -- cases 语法：对析取命题进行分情况讨论
    --   cases hx_union with
    --     | inl hx => ...  处理左分支（Left）：hx : x ∈ A
    --     | inr hx => ...  处理右分支（Right）：hx : x ∈ ∅
    --
    -- 含义：如果 hx_union 是 x ∈ A ∨ x ∈ ∅，那么有两种情况：
    --   情况1（inl）：x ∈ A，用 hx 表示这个假设
    --   情况2（inr）：x ∈ ∅，用 hx 表示这个假设
    cases hx_union with
    | inl hx => exact hx  -- 情况1：如果 x ∈ A，直接得到目标 x ∈ A
    | inr hx => exact False.elim (ZFSet.notMem_empty x hx)  -- 情况2：如果 x ∈ ∅，这是矛盾的

  -- 方向 2：x ∈ A → x ∈ A ∪ ∅
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 从 x ∈ A 推出 x ∈ A ∨ x ∈ ∅（用 Or.inl），再推出 x ∈ A ∪ ∅（用 mem_union.mpr）
    exact ZFSet.mem_union.mpr (Or.inl hx_in_A)

-- Theorem 2.2.1 (e) A ∩ A = A
theorem thm_2_2_1_e (A : ZFSet) : A ∩ A = A := by
  apply ZFSet.ext  -- 使用外延性公理：A ∩ A = A ↔ ∀ x, x ∈ A ∩ A ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 将 ↔ 分解成两个方向

  -- 方向 1：x ∈ A ∩ A → x ∈ A
  · intro hx_inter  -- hx_inter: x ∈ A ∩ A
    -- 从 x ∈ A ∩ A 推出 x ∈ A ∧ x ∈ A（用 mem_inter.mp）
    have hx_pair : x ∈ A ∧ x ∈ A := ZFSet.mem_inter.mp hx_inter
    -- 从合取命题中取出 x ∈ A（.left 或 .right 都可以，因为都是 x ∈ A）
    exact hx_pair.left

  -- 方向 2：x ∈ A → x ∈ A ∩ A
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 要证明 x ∈ A ∩ A，需要构造 x ∈ A ∧ x ∈ A
    -- ⟨hx_in_A, hx_in_A⟩ 构造合取命题（两个都是 x ∈ A）
    -- 然后用 mem_inter.mpr 推出 x ∈ A ∩ A
    exact ZFSet.mem_inter.mpr ⟨hx_in_A, hx_in_A⟩

-- Theorem 2.2.1 (f) A ∪ A = A
theorem thm_2_2_1_f (A : ZFSet) : A ∪ A = A := by
  apply ZFSet.ext  -- 使用外延性公理：A ∪ A = A ↔ ∀ x, x ∈ A ∪ A ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 将 ↔ 分解成两个方向

  -- 方向 1：x ∈ A ∪ A → x ∈ A
  · intro hx_union  -- hx_union: x ∈ A ∪ A
    -- 从 x ∈ A ∪ A 推出 x ∈ A ∨ x ∈ A（用 mem_union）
    rw [ZFSet.mem_union] at hx_union
    -- 分情况讨论：x ∈ A ∨ x ∈ A 的两种情况都是 x ∈ A
    cases hx_union with
    | inl hx => exact hx  -- 情况1：如果 x ∈ A，直接得到
    | inr hx => exact hx  -- 情况2：如果 x ∈ A，直接得到（两种情况相同）

  -- 方向 2：x ∈ A → x ∈ A ∪ A
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 从 x ∈ A 推出 x ∈ A ∨ x ∈ A（用 Or.inl），再推出 x ∈ A ∪ A（用 mem_union.mpr）
    exact ZFSet.mem_union.mpr (Or.inl hx_in_A)

-- Theorem 2.2.1 (g) A - ∅ = A
theorem thm_2_2_1_g (A : ZFSet) : set_diff A ∅ = A := by
  apply ZFSet.ext  -- 使用外延性公理：A - ∅ = A ↔ ∀ x, x ∈ A - ∅ ↔ x ∈ A
  intro x  -- x: 任意元素
  constructor  -- 将 ↔ 分解成两个方向

  -- 方向 1：x ∈ A - ∅ → x ∈ A
  · intro hx_diff  -- hx_diff: x ∈ A - ∅
    -- 从 x ∈ A - ∅ 推出 x ∈ A ∧ x ∉ ∅（用 mem_diff.mp）
    have hx_pair : x ∈ A ∧ x ∉ ∅ := (mem_diff A ∅ x).mp hx_diff
    -- 从合取命题中取出 x ∈ A
    exact hx_pair.left

  -- 方向 2：x ∈ A → x ∈ A - ∅
  · intro hx_in_A  -- hx_in_A: x ∈ A
    -- 要证明 x ∈ A - ∅，需要构造 x ∈ A ∧ x ∉ ∅
    -- x ∈ A 已经有了（hx_in_A）
    -- x ∉ ∅ 用 ZFSet.notMem_empty x 证明（空集没有元素）
    -- ⟨hx_in_A, ZFSet.notMem_empty x⟩ 构造合取命题
    -- 然后用 mem_diff.mpr 推出 x ∈ A - ∅
    exact (mem_diff A ∅ x).mpr ⟨hx_in_A, ZFSet.notMem_empty x⟩

-- Theorem 2.2.1 (h) ∅ - A = ∅
theorem thm_2_2_1_h (A : ZFSet) : set_diff ∅ A = ∅ := by
  apply ZFSet.ext  -- 使用外延性公理：∅ - A = ∅ ↔ ∀ x, x ∈ ∅ - A ↔ x ∈ ∅
  intro x  -- x: 任意元素
  constructor  -- 将 ↔ 分解成两个方向
  -- 方向 1：x ∈ ∅ - A → x ∈ ∅
  · intro hx_diff  -- hx_diff: x ∈ ∅ - A
    -- 从 x ∈ ∅ - A 推出 x ∈ ∅ ∧ x ∉ A（用 mem_diff.mp）
    have hx_pair : x ∈ ∅ ∧ x ∉ A := (mem_diff ∅ A x).mp hx_diff
    -- 从合取命题中取出 x ∈ ∅
    exact hx_pair.left
  -- 方向 2：x ∈ ∅ → x ∈ ∅ - A（空真命题）
  · intro hx_empty  -- hx_empty: x ∈ ∅
    -- 空集没有元素，x ∈ ∅ 本身就是矛盾的
    -- 从矛盾可以推出任何东西（包括 x ∈ ∅ - A）
    exact False.elim (ZFSet.notMem_empty x hx_empty)
