import Mathlib.SetTheory.ZFC.Basic
--3. Relations and Partitions
-- 本文件定義了 ZFC 集合論中的關係（Relations）相關概念

-- ============================================
-- 有序對 (Ordered Pair) 定義
-- ============================================
-- 使用 Kuratowski 定義：有序對 (a, b) = {{a}, {a, b}}
-- 這個定義的優點是：兩個有序對相等當且僅當它們的兩個分量分別相等
-- 即：(a, b) = (a', b') ↔ a = a' ∧ b = b'
def ordered_pair (a b : ZFSet) : ZFSet :=
  {{a}, {a, b}}

-- 定理：x 屬於有序對 (a, b) 當且僅當 x = {a} 或 x = {a, b}
-- 這是 Kuratowski 定義的直接結果
theorem mem_ordered_pair (a b x : ZFSet) : x ∈ ordered_pair a b ↔ x = {a} ∨ x = {a, b} :=
  ZFSet.mem_pair

-- ============================================
-- 有序對的唯一性引理（左分量）
-- ============================================
-- 引理：如果兩個有序對相等，則它們的第一個分量相等
-- 即：ordered_pair a b = ordered_pair a' b' → a = a'
-- 這是 Kuratowski 定義的重要性質，用於證明有序對的唯一性
lemma ordered_pair_eq_left {a b a' b' : ZFSet} :ordered_pair a b = ordered_pair a' b' → a = a' := by
  intro h -- 引入假設 h : ordered_pair a b = ordered_pair a' b'
  -- 策略：證明 {a} 屬於 ordered_pair a b，然後利用 h 和集合相等的性質
  have ha_mem : {a} ∈ ordered_pair a b := by
    rw [ordered_pair] -- 展開 ordered_pair 的定義：ordered_pair a b = {{a}, {a, b}}
    rw [ordered_pair, ordered_pair] at h -- 在假設 h 中展開兩個有序對的定義
    apply ZFSet.mem_pair.mpr -- 使用配對公理：x ∈ {y, z} ↔ x = y ∨ x = z
    -- 目標變成：{a} = {a} ∨ {a} = {a, b}
    left -- 選擇左邊的情況：證明 {a} = {a}
    rfl -- 由反身性可得 {a} = {a}
  -- 現在利用 h 將 ha_mem 改寫
  rw [h] at ha_mem -- 將 ha_mem 中的 ordered_pair a b 替換為 ordered_pair a' b'
  -- 現在 ha_mem : {a} ∈ {{a'}, {a', b'}}
  rw [ordered_pair] at ha_mem -- 展開 ordered_pair a' b' 的定義
  rw [ZFSet.mem_pair] at ha_mem -- 使用配對公理，得到 {a} = {a'} ∨ {a} = {a', b'}
  cases ha_mem with -- 對兩種情況進行分類討論
  | inl h_eq_a => -- 情況1：{a} = {a'}
    -- 從 {a} = {a'} 推出 a = a'
    have h_a_in : a ∈ ({a} : ZFSet) := ZFSet.mem_singleton.mpr rfl -- a ∈ {a} 由單元素集合的性質
    rw [h_eq_a] at h_a_in -- 將 {a} 替換為 {a'}，得到 a ∈ {a'}
    rw [ZFSet.mem_singleton] at h_a_in -- 使用單元素集合的性質，得到 a = a'
    exact h_a_in -- 證畢
  | inr h_eq_a_b => -- 情況2：{a} = {a', b'}
    -- 從 {a} = {a', b'} 推出 a = a'
    have h_aprime_in : a' ∈ ({a', b'} : ZFSet) := ZFSet.mem_pair.mpr (Or.inl rfl) -- a' ∈ {a', b'}
    rw [← h_eq_a_b] at h_aprime_in -- 將 {a', b'} 替換為 {a}，得到 a' ∈ {a}
    rw [ZFSet.mem_singleton] at h_aprime_in -- 使用單元素集合的性質，得到 a' = a
    exact h_aprime_in.symm -- 由對稱性得到 a = a'

-- ============================================
-- 有序對的唯一性引理（右分量）
-- ============================================
-- 引理：如果兩個有序對相等，則它們的第二個分量相等
-- 即：ordered_pair a b = ordered_pair a' b' → b = b'
-- 這是 Kuratowski 定義的另一個重要性質
lemma ordered_pair_eq_right {a b a' b' : ZFSet} :ordered_pair a b = ordered_pair a' b' → b = b' := by
  intro h -- 引入假設 h : ordered_pair a b = ordered_pair a' b'
  -- 策略：先證明 a = a'，然後利用這個事實簡化問題
  have ha_eq : a = a' := ordered_pair_eq_left h -- 使用左分量引理得到 a = a'
  rw [← ha_eq] at h -- 將 h 中的 a' 替換為 a，得到 {{a}, {a, b}} = {{a}, {a, b'}}
  rw [ordered_pair, ordered_pair] at h -- 展開兩個有序對的定義
  -- 現在目標是從 {{a}, {a, b}} = {{a}, {a, b'}} 推出 b = b'
  have h_pair : ({a, b} : ZFSet) = ({a, b'} : ZFSet) := by
    -- 策略：證明 {a, b} 屬於左邊的集合，然後利用 h 和集合相等的性質
    have h_in_lhs : {a, b} ∈ {{a}, {a, b}} := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b} ∈ {{a}, {a, b}}
    rw [h] at h_in_lhs -- 將左邊替換為右邊，得到 {a, b} ∈ {{a}, {a, b'}}
    rw [ZFSet.mem_pair] at h_in_lhs -- 使用配對公理，得到 {a, b} = {a} ∨ {a, b} = {a, b'}
    cases h_in_lhs with -- 對兩種情況進行分類討論
    | inl h_eq_a => -- 情況1：{a, b} = {a}
      -- 這意味著 {a, b} 是單元素集合，所以 a = b
      rw [h_eq_a] at h -- 將 h 中的 {a, b} 替換為 {a}，得到 {{a}, {a}} = {{a}, {a, b'}}
      have h_ab'_in_lhs : {a, b'} ∈ ({ {a}, {a} } : ZFSet) := by
        rw [h] -- 將左邊替換為右邊，目標變成 {a, b'} ∈ {{a}, {a, b'}}
        apply ZFSet.mem_pair.mpr -- 使用配對公理
        right -- 選擇右邊的情況：證明 {a, b'} = {a, b'}
        exact rfl -- 由反身性可得
      rw [ZFSet.mem_pair] at h_ab'_in_lhs -- 得到 {a, b'} = {a} ∨ {a, b'} = {a}
      cases h_ab'_in_lhs with
      | inl h_l => -- {a, b'} = {a}
        rw [h_l] -- 將 {a, b'} 替換為 {a}
        exact h_eq_a -- 使用 h_eq_a : {a, b} = {a}
      | inr h_r => -- {a, b'} = {a}
        rw [h_r] -- 將 {a, b'} 替換為 {a}
        exact h_eq_a -- 使用 h_eq_a : {a, b} = {a}
    | inr h_eq_a_b => -- 情況2：{a, b} = {a, b'}
      exact h_eq_a_b -- 直接得到 {a, b} = {a, b'}
  -- 現在我們有 h_pair : {a, b} = {a, b'}，需要從中推出 b = b'
  have h_b_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b ∈ {a, b} 由配對公理
  rw [h_pair] at h_b_in -- 將 {a, b} 替換為 {a, b'}，得到 b ∈ {a, b'}
  rw [ZFSet.mem_pair] at h_b_in -- 使用配對公理，得到 b = a ∨ b = b'
  cases h_b_in with -- 對兩種情況進行分類討論
  | inr h_eq_b => -- 情況1：b = b'
    exact h_eq_b -- 直接得到目標
  | inl h_eq_a => -- 情況2：b = a
    -- 如果 b = a，則 {a, b} = {a}，需要進一步分析
    rw [h_eq_a] at h_pair -- 將 h_pair 中的 b 替換為 a，得到 {a, a} = {a, b'}
    have h_b_in_lhs : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' ∈ {a, b'}
    rw [← h_pair] at h_b_in_lhs -- 將 {a, b'} 替換為 {a, a}，得到 b' ∈ {a, a}
    rw [ZFSet.mem_pair] at h_b_in_lhs -- 使用配對公理，得到 b' = a ∨ b' = a
    cases h_b_in_lhs with
    | inl h_l => -- b' = a
      rw [h_l] -- 將 b' 替換為 a
      exact h_eq_a -- 使用 h_eq_a : b = a，得到 b = b'（因為 b = a 且 b' = a）
    | inr h_r => -- b' = a
      rw [h_r] -- 將 b' 替換為 a
      exact h_eq_a -- 使用 h_eq_a : b = a，得到 b = b'（因為 b = a 且 b' = a）


-- ============================================
-- 笛卡爾積 (Cartesian Product) 定義
-- ============================================
-- 數學定義：A × B = { (a, b) | a ∈ A, b ∈ B }
-- 在 ZFC 中，我們需要使用分離公理從一個足夠大的集合中分離出所有有序對
-- 技術細節：我們從 A ∪ B 的冪集的冪集中分離，因為有序對 {{a}, {a, b}} 的元素是 {a} 和 {a, b}，
-- 而這些集合都是 A ∪ B 的子集，所以有序對本身是 powerset(A ∪ B) 的子集
def product (A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b)
            (ZFSet.powerset (ZFSet.powerset (A ∪ B)))

-- 定理：x 屬於笛卡爾積 A × B 當且僅當存在 a ∈ A 和 b ∈ B 使得 x = (a, b)
-- 這是笛卡爾積定義的直接刻畫
theorem mem_product (A B x : ZFSet) : x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b := by
  rw [product] -- 展開 product 的定義：product A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：x ∈ powerset(powerset(A ∪ B)) ∧ (∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) ↔ (∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b)
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_powerset, h_exists⟩ -- 左到右：假設 x 在分離集合中
    exact h_exists -- 直接使用存在性條件
  · intro h_exists -- 右到左：假設存在 a ∈ A, b ∈ B 使得 x = ordered_pair a b
    constructor -- 需要證明兩個條件：1) x 在冪集中，2) 存在性條件
    · rcases h_exists with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, x = ordered_pair a b
      -- 使用 rfl 將 x 替換為 ordered_pair a b，所以目標變成證明 ordered_pair a b 在冪集中
      rw [ordered_pair] -- 展開 ordered_pair 的定義：x = {{a}, {a, b}}
      -- 目標：{{a}, {a, b}} ∈ powerset(powerset(A ∪ B))
      -- 即：{{a}, {a, b}} ⊆ powerset(A ∪ B)
      apply ZFSet.mem_powerset.mpr -- 使用冪集的成員關係：x ∈ powerset A ↔ x ⊆ A
      -- 目標變成：{{a}, {a, b}} ⊆ powerset(A ∪ B)
      intro z hz -- 引入任意元素 z，假設 z ∈ {{a}, {a, b}}
      rw [ZFSet.mem_pair] at hz -- 使用配對公理，得到 z = {a} ∨ z = {a, b}
      cases hz with -- 對兩種情況進行分類討論
      | inl hz_eq => -- 情況1：z = {a}
        rw [hz_eq] -- 將 z 重寫為 {a}
        -- 目標：{a} ∈ powerset(A ∪ B)，即 {a} ⊆ A ∪ B
        apply ZFSet.mem_powerset.mpr -- 使用冪集的成員關係
        intro w hw -- 引入任意元素 w，假設 w ∈ {a}
        rw [ZFSet.mem_singleton] at hw -- 使用單元素集合的性質，得到 w = a
        rw [hw] -- 將 w 重寫為 a
        rw [ZFSet.mem_union] -- 使用聯集的性質，目標變成 a ∈ A ∨ a ∈ B
        left -- 選擇左邊的情況
        exact ha -- 使用 ha : a ∈ A
      | inr hz_eq => -- 情況2：z = {a, b}
        rw [hz_eq] -- 將 z 重寫為 {a, b}
        -- 目標：{a, b} ∈ powerset(A ∪ B)，即 {a, b} ⊆ A ∪ B
        apply ZFSet.mem_powerset.mpr -- 使用冪集的成員關係
        intro w hw -- 引入任意元素 w，假設 w ∈ {a, b}
        rw [ZFSet.mem_pair] at hw -- 使用配對公理，得到 w = a ∨ w = b
        cases hw with -- 對兩種情況進行分類討論
        | inl hw_eq => -- 情況2.1：w = a
          rw [hw_eq] -- 將 w 重寫為 a
          rw [ZFSet.mem_union] -- 使用聯集的性質，目標變成 a ∈ A ∨ a ∈ B
          left -- 選擇左邊的情況
          exact ha -- 使用 ha : a ∈ A
        | inr hw_eq => -- 情況2.2：w = b
          rw [hw_eq] -- 將 w 重寫為 b
          rw [ZFSet.mem_union] -- 使用聯集的性質，目標變成 b ∈ A ∨ b ∈ B
          right -- 選擇右邊的情況
          exact hb -- 使用 hb : b ∈ B
    · exact h_exists -- 第二個條件直接使用假設


-- ============================================
-- 二元關係 (Binary Relation) 定義
-- ============================================
-- 定義：從集合 A 到集合 B 的二元關係 R 是 A × B 的子集
-- 即：R ⊆ A × B
-- 這意味著 R 中的每個元素都是形如 (a, b) 的有序對，其中 a ∈ A, b ∈ B
def is_relation (R A B : ZFSet) : Prop :=
  ∀ x ∈ R, x ∈ product A B

-- def is_relation (R A B : ZFSet) : ZFSet :=
--   ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair a b)
--             (product A B)

-- theorem mem_is_relation (R A B x : ZFSet) : x ∈ is_relation R A B ↔ x ∈ product A B ∧ x ∈ R := by
--   rw [is_relation] -- 展開 is_relation 的定義：is_relation R A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
--   rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
--   constructor -- 將 ↔ 分成兩個方向
--   · intro ⟨hx_in_product_A_B, h_exists⟩
--     rcases h_exists with ⟨a, ha, b, hb, hR, h_eq⟩ --將存在量詞分解成 a ∈ A, b ∈ B, ordered_pair a b ∈ R, x = ordered_pair a b
--     constructor
--     · exact hx_in_product_A_B
--     · rw [h_eq] --將 x = ordered_pair a b 重寫為 x = ordered_pair a b
--       exact hR
--   · intro ⟨hx_in_product_A_B, hx_in_R⟩
--     constructor
--     · exact hx_in_product_A_B
--     · rw [mem_product] at hx_in_product_A_B
--       rcases hx_in_product_A_B with ⟨a, ha, b, hb, h_eq⟩
--       rw [h_eq] at hx_in_R
--       exact ⟨a, ha, b, hb, hx_in_R, h_eq⟩



-- ============================================
-- 恒等關係 (Identity Relation) 定義
-- ============================================
-- 定義：集合 A 上的恒等關係是集合 {(a, a) | a ∈ A}
-- 恒等關係將每個元素映射到它自己
-- 在圖論中，這對應於每個頂點都有自環的圖
def identity_relation (A : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a)
            (product A A)

-- 定理：x 屬於恒等關係當且僅當存在 a ∈ A 使得 x = (a, a)
-- 這是恒等關係定義的直接刻畫
theorem mem_identity_relation (A x :ZFSet) : x ∈ identity_relation A ↔ ∃ a ∈ A, x = ordered_pair a a := by
  rw [identity_relation] -- 展開 identity_relation 的定義：identity_relation A = ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a) (product A A)
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：x ∈ product A A ∧ (∃ a ∈ A, x = ordered_pair a a) ↔ (∃ a ∈ A, x = ordered_pair a a)
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_product_A_A, h_exists⟩ -- 左到右：假設 x 在分離集合中
    exact h_exists -- 直接使用存在性條件
  · intro h -- 右到左：假設存在 a ∈ A 使得 x = ordered_pair a a
    rcases h with ⟨a, ha, h_eq⟩ -- 分解存在量詞，得到 a ∈ A, x = ordered_pair a a
    constructor -- 需要證明兩個條件：1) x 在 product A A 中，2) 存在性條件
    · rw [mem_product] -- 展開 mem_product，目標變成 ∃ a' ∈ A, ∃ b' ∈ A, x = ordered_pair a' b'
      exact ⟨a, ha, a, ha, h_eq⟩ -- 使用 a 作為兩個分量，因為 x = (a, a)
    · exact ⟨a, ha, h_eq⟩ -- 第二個條件直接使用假設




-- ============================================
-- 輔助引理：從 R 中提取元素的證明
-- ============================================
-- 邏輯：(a, b) ∈ R  =>  {a} ∈ ⋃R  =>  a ∈ ⋃⋃R
lemma pair_in_union_of_union_left {a b R : ZFSet} (h : ordered_pair a b ∈ R) : a ∈ ZFSet.sUnion (ZFSet.sUnion R) := by
  have h_singleton_in_union : {a} ∈ ZFSet.sUnion R := by
    rw [ZFSet.mem_sUnion]
    exists ordered_pair a b -- 證人是 (a, b)
    constructor
    · exact h
    · rw [ordered_pair, ZFSet.mem_pair]
      left
      rfl
  rw [ZFSet.mem_sUnion]
  exists {a}
  constructor
  · exact h_singleton_in_union
  · rw [ZFSet.mem_singleton]


lemma pair_in_union_of_union_right {a b R : ZFSet} (h : ordered_pair a b ∈ R) : b ∈ ZFSet.sUnion (ZFSet.sUnion R) := by
  have h_pair_in_union : {a, b} ∈ ZFSet.sUnion R := by
    rw [ZFSet.mem_sUnion]
    exists ordered_pair a b -- 證人是 (a, b)
    constructor
    · exact h
    · apply ZFSet.mem_pair.mpr
      right
      rfl
  rw [ZFSet.mem_sUnion]
  exists {a, b}
  constructor
  · exact h_pair_in_union
  · rw [ZFSet.mem_pair]
    right
    rfl
-- ============================================
-- 關係的定義域 (Domain) 定義
-- ============================================
-- 定義：從集合 A 到集合 B 的關係 R 的定義域是所有 R 中有序對的第一個分量組成的集合
-- 即：domain R = {a ∈ A | ∃ b ∈ B, (a, b) ∈ R}
-- 在函數的語言中，定義域是"輸入"的集合
def domain (R : ZFSet) : ZFSet :=
  ZFSet.sep (fun a => ∃ b, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))

-- 定理：a 屬於關係 R 的定義域當且僅當存在 b ∈ B 使得 (a, b) ∈ R
-- 這是定義域定義的直接刻畫
theorem mem_domain (R : ZFSet) : a ∈ domain R ↔ ∃ b , ordered_pair a b ∈ R := by
  rw [domain] -- 展開 domain 的定義：domain R = ZFSet.sep (fun a => ∃ b, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：a ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ b, ordered_pair a b ∈ R) ↔ (∃ b, ordered_pair a b ∈ R)
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 a ∈ domain R，即 a ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ b, ordered_pair a b ∈ R)
    exact h.2
  · intro h2 -- 右到左：假設存在 b 使得 ordered_pair a b ∈ R
    rcases h2 with ⟨b, hpair⟩
    constructor
    · exact pair_in_union_of_union_left hpair
    · exists b

-- ============================================
-- 關係的值域 (Range) 定義
-- ============================================
-- 定義：從集合 A 到集合 B 的關係 R 的值域是所有 R 中有序對的第二個分量組成的集合
-- 即：range R = {b ∈ B | ∃ a ∈ A, (a, b) ∈ R}
-- 在函數的語言中，值域是"輸出"的集合
def range (R : ZFSet) : ZFSet :=
  ZFSet.sep (fun b => ∃ a, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))

-- 定理：b 屬於關係 R 的值域當且僅當存在 a ∈ A 使得 (a, b) ∈ R
-- 這是值域定義的直接刻畫
theorem mem_range (R : ZFSet) : b ∈ range R ↔ ∃ a, ordered_pair a b ∈ R := by
  rw [range] -- 展開 range 的定義：range R = ZFSet.sep (fun b => ∃ a, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：b ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ a, ordered_pair a b ∈ R) ↔ (∃ a, ordered_pair a b ∈ R)
  constructor
  · intro h -- 左到右：假設 b ∈ range R，即 b ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ a, ordered_pair a b ∈ R)
    exact h.2
  · intro h2 -- 右到左：假設存在 a 使得 ordered_pair a b ∈ R
    rcases h2 with ⟨a, hpair⟩
    constructor
    · exact pair_in_union_of_union_right hpair
    · exists a


def inverse_relation (R : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a, ∃ b, ordered_pair a b ∈ R ∧ x = ordered_pair b a)
            (product (range R) (domain R))


theorem mem_inverse_relation (R x : ZFSet) : x ∈ inverse_relation R ↔ ∃ a, ∃ b, ordered_pair a b ∈ R ∧ x = ordered_pair b a := by
  rw [inverse_relation]
  rw [ZFSet.mem_sep]
  constructor
  · intro h
    exact h.2
  · intro h_exist
    rcases h_exist with ⟨a, b, hpair, h_eq⟩
    constructor
    · rw [h_eq]
      rw [mem_product]
      exists b
      constructor
      · rw [mem_range]
        exact ⟨a, hpair⟩
      · exists a
        constructor
        · rw [mem_domain]
          exact ⟨b, hpair⟩
        · rfl
    · exact ⟨a, b, hpair, h_eq⟩




-- Theorem 2.2.4 (a)：Dom(R⁻¹) = Rng(R)
theorem dom_inv_eq_rng (R : ZFSet) : domain (inverse_relation R) = range R := by
  apply ZFSet.ext
  intro b
  constructor
  · intro h_dom
    rw [mem_domain] at h_dom
    rcases h_dom with ⟨a, hpair⟩
    rw [mem_inverse_relation] at hpair
    rcases hpair with ⟨a1, b1, hpair1, hpair2⟩
    have b_eq_b1 : b = b1 := ordered_pair_eq_left hpair2
    have a_eq_a1 : a = a1 := ordered_pair_eq_right hpair2
    subst b_eq_b1 a_eq_a1
    rw [mem_range]
    exact ⟨a, hpair1⟩
  · intro h_rng
    rw [mem_range] at h_rng
    rcases h_rng with ⟨a, hpair⟩
    rw [mem_domain]
    exists a
    rw [mem_inverse_relation]
    exact ⟨a, b, hpair, rfl⟩

-- Theorem 2.2.4 (b)：Rng(R⁻¹) = Dom(R)
theorem rng_inv_eq_dom (R: ZFSet) : range (inverse_relation R) = domain R := by
  apply ZFSet.ext
  intro a
  constructor
  · intro h_rng
    rw [mem_range] at h_rng
    rcases h_rng with ⟨b, hpair⟩
    rw [mem_inverse_relation] at hpair
    rw [mem_domain]
    rcases hpair with ⟨a1, b1, hpair1, hpair2⟩
    have a_eq_a1 : a = a1 := ordered_pair_eq_right hpair2
    have b_eq_b1 : b = b1 := ordered_pair_eq_left hpair2
    subst a_eq_a1 b_eq_b1
    exact ⟨b, hpair1⟩
  · intro h_dom
    rw [mem_domain] at h_dom
    rcases h_dom with ⟨b, hpair⟩
    rw [mem_range]
    exists b
    rw [mem_inverse_relation]
    exact ⟨a, b, hpair, rfl⟩



-- Definition：組合關係 (Composition Relation) 定義
def composition_relation (S R : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a , ∃ c , x = ordered_pair a c ∧ ∃ b , ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S) (product(domain R) (range S))

theorem mem_composition_relation (S R A B C x : ZFSet) : x ∈ composition_relation S R A C B ↔ ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S := by
  rw [composition_relation] -- 展開 composition_relation 的定義：composition_relation R S A C B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S) (product A C)
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- h : x ∈ composition_relation S R A C B
    exact h.2 -- 直接使用 h.2
  · intro h_exist -- h_exist : ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S
    rcases h_exist with ⟨a, haA, c, hcC, h_eq, b, hbB, hpair1, hpair2⟩ -- 分解存在量詞，得到 a ∈ A, c ∈ C, x = ordered_pair a c, b ∈ B, hpair1 : ordered_pair a b ∈ R, hpair2 : ordered_pair b c ∈ S
    constructor -- 需要證明兩個條件：1) x ∈ product A C, 2) ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S
    · rw [mem_product] -- 展開 mem_product，目標變成 ∃ a' ∈ A, ∃ c' ∈ C, x = ordered_pair a' c'
      exact ⟨a, haA, c, hcC, h_eq⟩ -- 使用 a, haA, c, hcC, h_eq 構造對：a ∈ A, c ∈ C, x = ordered_pair a c
    · exact ⟨a, haA, c, hcC, h_eq, b, hbB, hpair1, hpair2⟩ -- 第二個條件直接使用 h_exist




-- Theorem 3.1.2 (a)：(R⁻¹)⁻¹ = R
theorem R_inv_inv_eq_R (R A B : ZFSet) (hR : is_relation R A B): inverse_relation (inverse_relation R A B) B A = R := by
  apply ZFSet.ext -- 使用外延性公理，將 inverse_relation (inverse_relation R A B) B A = R 轉換為 ∀ y, y ∈ inverse_relation (inverse_relation R A B) B A ↔ y ∈ R
  intro x
  constructor
  · intro h_inv_inv
    rw [mem_inverse_relation] at h_inv_inv -- 展開 inverse_relation 的定義：inverse_relation R A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair b a) (product B A)
    rcases h_inv_inv with ⟨b, hbB, a, haA, hpair_in_inv, x_eq⟩
    rw [mem_inverse_relation] at hpair_in_inv -- 展開 mem_inverse_relation 的定義：mem_inverse_relation R A B x = ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair b a
    rcases hpair_in_inv with ⟨a1, ha1A, b1, hb1B, hpair1, x_eq1⟩ -- 分解存在量詞，得到 a1 ∈ A, b1 ∈ B, hpair1 : ordered_pair a1 b1 ∈ R, x_eq1 : x = ordered_pair b1 a1
    have b_eq_b1 : b = b1 := ordered_pair_eq_left x_eq1 -- 使用有序對左分量唯一性引理
    have a_eq_a1 : a = a1 := ordered_pair_eq_right x_eq1 -- 使用有序對右分量唯一性引理
    rw [a_eq_a1, b_eq_b1] at x_eq
    rw [← x_eq] at hpair1
    exact hpair1
  · intro h_R
    rw [mem_inverse_relation]
    rw [is_relation] at hR -- 展開 is_relation 的定義：is_relation R A B = ∀ x ∈ R, x ∈ product A B
    have x_in_product : x ∈ product A B := hR x h_R
    rw [mem_product] at x_in_product
    rcases x_in_product with ⟨a, haA, b, hbB, x_eq⟩
    exists b, hbB, a, haA
    constructor
    · rw [mem_inverse_relation]
      rw [x_eq] at h_R
      exact ⟨a, haA, b, hbB, h_R, rfl⟩
    · exact x_eq

-- Theorem 3.1.2 (b)：T∘(S∘R) = (T∘S)∘R
-- theorem Comp_Associative_Law (T S R A B C D: ZFSet):
--   composition_relation T (composition_relation S R A C B) A D C = composition_relation (composition_relation T S B D C) R A D B := by
--   apply ZFSet.ext -- 使用外延性公理，將 composition_relation T (composition_relation S R A C B) A D C = composition_relation (composition_relation T S B D C) R A D B 轉換為 ∀ y, y ∈ composition_relation T (composition_relation S R A C B) A D C ↔ y ∈ composition_relation (composition_relation T S B D C) R A D B
--   intro x
--   constructor
--   · intro hl_comp
--     rw [mem_composition_relation] at hl_comp -- 展開 composition_relation 的定義：composition_relation R S A C B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S) (product A C)
--     rcases hl_comp with ⟨a, haA, d, hdD, x_eq_pair_ad, c, hcC, hpair_ac, hpair_cd⟩ -- 分解存在量詞，得到 a ∈ A, d ∈ D, x = ordered_pair a d, b ∈ B, hpair1 : ordered_pair a b ∈ R, hpair2 : ordered_pair b c ∈ S
--     rw [mem_composition_relation]
--     exists a, haA, d, hdD
--     constructor
--     · exact x_eq_pair_ad
--     · rw [mem_composition_relation] at hpair_ac
--       rcases hpair_ac with ⟨a1, ha1A, c1, hc1C, hpair_ac_a1c1, b_exists⟩ -- 分解存在量詞，得到 a1 ∈ A, c1 ∈ C, x = ordered_pair a1 c1, b ∈ B, hpair_ac_a1c1 : ordered_pair a1 b ∈ R, b_exists : ∃ b ∈ B, ordered_pair a1 b ∈ R ∧ ordered_pair b c1 ∈ S
--       rcases b_exists with ⟨b, hbB, hpair_ab, hpair_bc1⟩ -- 分解存在量詞，得到 b ∈ B, hpair_ab : ordered_pair a1 b ∈ R, hpair_bc1 : ordered_pair b c1 ∈ S
--       exists b, hbB
--       constructor
--       · have a_eq_a1 : a = a1 := ordered_pair_eq_left hpair_ac_a1c1
--         subst a_eq_a1
--         exact hpair_ab
--       · rw [mem_composition_relation]
--         exists b, hbB, d, hdD
--         constructor
--         · exact rfl
--         · exists c, hcC
--           have c_eq_c1 : c = c1 := ordered_pair_eq_right hpair_ac_a1c1
--           subst c_eq_c1
--           exact ⟨hpair_bc1, hpair_cd⟩
--   · intro hr_comp
--     rw [mem_composition_relation] at hr_comp -- 展開 composition_relation 的定義：composition_relation R S A C B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ c ∈ C, x = ordered_pair a c ∧ ∃ b ∈ B, ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S) (product A C)
--     rcases hr_comp with ⟨a, haA, d, hdD, x_eq_pair_ad, b, hbB, hpair_ab, hpair_bd⟩ -- 分解存在量詞，得到 a ∈ A, d ∈ D, x = ordered_pair a d, b ∈ B, hpair_ab : ordered_pair a b ∈ R, hpair_bd : ordered_pair b d ∈ S
--     rw [mem_composition_relation]
--     exists a, haA, d, hdD
--     constructor
--     · exact x_eq_pair_ad
--     · rw [mem_composition_relation] at hpair_bd
--       rcases hpair_bd with ⟨b1, hb1B, d1, hd1D, hpair_bd_b1d1, c_exists⟩ -- 分解存在量詞，得到 b1 ∈ B, d1 ∈ D, x = ordered_pair b1 d1, c ∈ C, hpair_bd_b1d1 : ordered_pair b1 c ∈ S, c_exists : ∃ c ∈ C, ordered_pair b1 c ∈ S ∧ ordered_pair c d1 ∈ T
--       rcases c_exists with ⟨c, hcC, hpair_b1c1, hpair_c1d1⟩ -- 分解存在量詞，得到 c1 ∈ C, hpair_b1c1 : ordered_pair b1 c1 ∈ S, hpair_c1d1 : ordered_pair c1 d1 ∈ T
--       exists c, hcC
--       constructor
--       · rw [mem_composition_relation]
--         exists a, haA, c, hcC
--         constructor
--         · exact rfl
--         · exists b, hbB
--           have b_eq_b1 : b = b1 := ordered_pair_eq_left hpair_bd_b1d1
--           subst b_eq_b1
--           exact ⟨hpair_ab, hpair_b1c1⟩
--       · have d_eq_d1 : d = d1 := ordered_pair_eq_right hpair_bd_b1d1
--         subst d_eq_d1
--         exact hpair_c1d1

-- Theorem 3.1.2 (b)：T∘(S∘R) = (T∘S)∘R
theorem Comp_Associative_Law (T S R A B C D: ZFSet):
  composition_relation T (composition_relation S R A C B) A D C = composition_relation (composition_relation T S B D C) R A D B := by
  have h_pair : ∀ (a d : ZFSet),
    ordered_pair a d ∈ composition_relation T (composition_relation S R A C B) A D C ↔ ordered_pair a d ∈ composition_relation (composition_relation T S B D C) R A D B := by
    intro a d
    calc
      ordered_pair a d ∈ composition_relation T (composition_relation S R A C B) A D C
      ↔ ∃ a ∈ A, ∃ d ∈ D, ordered_pair a d ∈ composition_relation T (composition_relation S R A C B) A D C
