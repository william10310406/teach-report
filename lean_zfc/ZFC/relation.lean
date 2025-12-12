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
  ∀ x ∈ R, ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b

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
-- 定理：a 屬於關係 R 的定義域當且僅當存在 b 使得 (a, b) ∈ R
-- 這是定義域定義的直接刻畫
-- 注意：這裡的 a 是隱式參數，需要在定理聲明中明確指定
theorem mem_domain (R a : ZFSet) : a ∈ domain R ↔ ∃ b , ordered_pair a b ∈ R := by
  rw [domain] -- 展開 domain 的定義：domain R = ZFSet.sep (fun a => ∃ b, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：a ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ b, ordered_pair a b ∈ R) ↔ (∃ b, ordered_pair a b ∈ R)
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 a ∈ domain R，即 a ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ b, ordered_pair a b ∈ R)
    exact h.2 -- 直接取出存在性條件
  · intro h2 -- 右到左：假設存在 b 使得 ordered_pair a b ∈ R
    rcases h2 with ⟨b, hpair⟩ -- 分解存在量詞，得到 b 和 hpair : ordered_pair a b ∈ R
    constructor -- 需要證明兩個條件：1) a 在雙重並集中，2) 存在性條件
    · -- 證明 a ∈ ZFSet.sUnion (ZFSet.sUnion R)
      -- 利用輔助引理：從 (a, b) ∈ R 可以推出 a ∈ ⋃⋃R
      exact pair_in_union_of_union_left hpair
    · -- 證明存在性條件：∃ b, ordered_pair a b ∈ R
      exists b -- 使用剛才分解出的 b

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
-- 定理：b 屬於關係 R 的值域當且僅當存在 a 使得 (a, b) ∈ R
-- 這是值域定義的直接刻畫
-- 注意：這裡的 b 是隱式參數，需要在定理聲明中明確指定
theorem mem_range (R b : ZFSet) : b ∈ range R ↔ ∃ a, ordered_pair a b ∈ R := by
  rw [range] -- 展開 range 的定義：range R = ZFSet.sep (fun b => ∃ a, ordered_pair a b ∈ R) (ZFSet.sUnion (ZFSet.sUnion (R)))
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：b ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ a, ordered_pair a b ∈ R) ↔ (∃ a, ordered_pair a b ∈ R)
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 b ∈ range R，即 b ∈ ZFSet.sUnion (ZFSet.sUnion R) ∧ (∃ a, ordered_pair a b ∈ R)
    exact h.2 -- 直接取出存在性條件
  · intro h2 -- 右到左：假設存在 a 使得 ordered_pair a b ∈ R
    rcases h2 with ⟨a, hpair⟩ -- 分解存在量詞，得到 a 和 hpair : ordered_pair a b ∈ R
    constructor -- 需要證明兩個條件：1) b 在雙重並集中，2) 存在性條件
    · -- 證明 b ∈ ZFSet.sUnion (ZFSet.sUnion R)
      -- 利用輔助引理：從 (a, b) ∈ R 可以推出 b ∈ ⋃⋃R
      exact pair_in_union_of_union_right hpair
    · -- 證明存在性條件：∃ a, ordered_pair a b ∈ R
      exists a -- 使用剛才分解出的 a


-- ============================================
-- 反關係 (Inverse Relation) 定義
-- ============================================
-- 定義：關係 R 的反關係 R⁻¹ 是將 R 中所有有序對的兩個分量交換得到的關係
-- 即：R⁻¹ = {(b, a) | (a, b) ∈ R}
-- 數學意義：如果 R 是從 A 到 B 的關係，則 R⁻¹ 是從 B 到 A 的關係
-- 在函數的語言中，反關係對應於反函數（如果存在）
def inverse_relation (R : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a, ∃ b, ordered_pair a b ∈ R ∧ x = ordered_pair b a)
            (product (range R) (domain R))
postfix:max "⁻¹" => inverse_relation -- 定義 ⁻¹ 為 inverse_relation 的簡寫

-- 定理：x 屬於反關係 R⁻¹ 當且僅當存在 a, b 使得 (a, b) ∈ R 且 x = (b, a)
-- 這是反關係定義的直接刻畫
theorem mem_inverse_relation (R x : ZFSet) : x ∈ R⁻¹ ↔ ∃ a, ∃ b, ordered_pair a b ∈ R ∧ x = ordered_pair b a := by
  rw [inverse_relation] -- 展開 inverse_relation 的定義
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 x 在分離集合中
    exact h.2 -- 直接取出存在性條件
  · intro h_exist -- 右到左：假設存在 a, b 使得 (a, b) ∈ R 且 x = (b, a)
    rcases h_exist with ⟨a, b, hpair, h_eq⟩ -- 分解存在量詞
    constructor -- 需要證明兩個條件：1) x 在笛卡爾積中，2) 存在性條件
    · -- 證明 x ∈ product (range R) (domain R)
      -- 即證明 (b, a) ∈ (range R) × (domain R)
      rw [h_eq] -- 將 x 替換為 ordered_pair b a
      rw [mem_product] -- 展開笛卡爾積的成員關係
      exists b -- 第一個分量是 b
      constructor
      · -- 證明 b ∈ range R，即存在 a' 使得 (a', b) ∈ R
        rw [mem_range]
        exact ⟨a, hpair⟩ -- 使用 a 作為證人
      · exists a -- 第二個分量是 a
        constructor
        · -- 證明 a ∈ domain R，即存在 b' 使得 (a, b') ∈ R
          rw [mem_domain]
          exact ⟨b, hpair⟩ -- 使用 b 作為證人
        · rfl -- ordered_pair b a = ordered_pair b a
    · -- 證明存在性條件
      exact ⟨a, b, hpair, h_eq⟩




-- ============================================
-- 反關係的性質定理
-- ============================================
-- Theorem 2.2.4 (a)：反關係的定義域等於原關係的值域
-- 即：Dom(R⁻¹) = Rng(R)
-- 數學意義：如果 (a, b) ∈ R，則 b 在 R 的值域中，同時 b 在 R⁻¹ 的定義域中
theorem dom_inv_eq_rng (R : ZFSet) : domain (inverse_relation R) = range R := by
  apply ZFSet.ext -- 使用外延性公理，證明兩個集合相等
  intro b -- 對任意元素 b
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 b ∈ domain (R⁻¹)，則 b ∈ range R
    intro h_dom -- 假設 b ∈ domain (R⁻¹)
    rw [mem_domain] at h_dom -- 展開定義域的刻畫
    rcases h_dom with ⟨a, hpair⟩ -- 得到存在 a 使得 (a, b) ∈ R⁻¹
    rw [mem_inverse_relation] at hpair -- 展開反關係的刻畫
    rcases hpair with ⟨a1, b1, hpair1, hpair2⟩ -- 得到 (a1, b1) ∈ R 且 (a, b) = (b1, a1)
    -- 比對有序對的分量以統一變數
    have b_eq_b1 : b = b1 := ordered_pair_eq_left hpair2 -- 從 (a, b) = (b1, a1) 得到 b = b1
    have a_eq_a1 : a = a1 := ordered_pair_eq_right hpair2 -- 從 (a, b) = (b1, a1) 得到 a = a1
    subst b_eq_b1 a_eq_a1 -- 替換變數
    rw [mem_range] -- 展開值域的刻畫
    exact ⟨a, hpair1⟩ -- 使用 (a1, b1) ∈ R（即 (a, b) ∈ R）證明 b ∈ range R
  · -- 方向2：如果 b ∈ range R，則 b ∈ domain (R⁻¹)
    intro h_rng -- 假設 b ∈ range R
    rw [mem_range] at h_rng -- 展開值域的刻畫
    rcases h_rng with ⟨a, hpair⟩ -- 得到存在 a 使得 (a, b) ∈ R
    rw [mem_domain] -- 展開定義域的刻畫
    exists a -- 使用 a 作為證人
    rw [mem_inverse_relation] -- 展開反關係的刻畫
    exact ⟨a, b, hpair, rfl⟩ -- 直接構造：因為 (a, b) ∈ R，所以 (b, a) ∈ R⁻¹

-- Theorem 2.2.4 (b)：反關係的值域等於原關係的定義域
-- 即：Rng(R⁻¹) = Dom(R)
-- 數學意義：如果 (a, b) ∈ R，則 a 在 R 的定義域中，同時 a 在 R⁻¹ 的值域中
theorem rng_inv_eq_dom (R: ZFSet) : range (R⁻¹) = domain R := by
  apply ZFSet.ext -- 使用外延性公理，證明兩個集合相等
  intro a -- 對任意元素 a
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 a ∈ range (R⁻¹)，則 a ∈ domain R
    intro h_rng -- 假設 a ∈ range (R⁻¹)
    rw [mem_range] at h_rng -- 展開值域的刻畫
    rcases h_rng with ⟨b, hpair⟩ -- 得到存在 b 使得 (b, a) ∈ R⁻¹
    rw [mem_inverse_relation] at hpair -- 展開反關係的刻畫
    rw [mem_domain] -- 展開定義域的刻畫
    rcases hpair with ⟨a1, b1, hpair1, hpair2⟩ -- 得到 (a1, b1) ∈ R 且 (b, a) = (b1, a1)
    -- 比對有序對的分量以統一變數
    have a_eq_a1 : a = a1 := ordered_pair_eq_right hpair2 -- 從 (b, a) = (b1, a1) 得到 a = a1
    have b_eq_b1 : b = b1 := ordered_pair_eq_left hpair2 -- 從 (b, a) = (b1, a1) 得到 b = b1
    subst a_eq_a1 b_eq_b1 -- 替換變數
    exact ⟨b, hpair1⟩ -- 使用 (a1, b1) ∈ R（即 (a, b) ∈ R）證明 a ∈ domain R
  · -- 方向2：如果 a ∈ domain R，則 a ∈ range (R⁻¹)
    intro h_dom -- 假設 a ∈ domain R
    rw [mem_domain] at h_dom -- 展開定義域的刻畫
    rcases h_dom with ⟨b, hpair⟩ -- 得到存在 b 使得 (a, b) ∈ R
    rw [mem_range] -- 展開值域的刻畫
    exists b -- 使用 b 作為證人
    rw [mem_inverse_relation] -- 展開反關係的刻畫
    exact ⟨a, b, hpair, rfl⟩ -- 直接構造：因為 (a, b) ∈ R，所以 (b, a) ∈ R⁻¹



-- ============================================
-- 組合關係 (Composition Relation) 定義
-- ============================================
-- 定義：關係 S 和 R 的組合 S ∘ R 是滿足以下條件的關係：
-- (a, c) ∈ S ∘ R 當且僅當存在 b 使得 (a, b) ∈ R 且 (b, c) ∈ S
-- 數學意義：組合關係對應於關係的複合，類似於函數的複合
-- 注意：這裡的順序是 S ∘ R，表示先應用 R，再應用 S
def composition_relation (S R : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a b c , x = ordered_pair a c ∧ ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S) (product (domain R) (range S))
infixr:60 " ∘ " => composition_relation -- 定義 ∘ 為 composition_relation 的簡寫

-- 定理：x 屬於組合關係 S ∘ R 當且僅當存在 a, b, c 使得 x = (a, c) 且 (a, b) ∈ R 且 (b, c) ∈ S
-- 這是組合關係定義的直接刻畫
theorem mem_composition_relation (S R x : ZFSet) : x ∈ S ∘ R ↔ ∃ a b c, x = ordered_pair a c ∧ ordered_pair a b ∈ R ∧ ordered_pair b c ∈ S := by
  rw [composition_relation] -- 展開 composition_relation 的定義
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 x 在分離集合中
    exact h.2 -- 直接取出存在性條件
  · intro h_exist -- 右到左：假設存在 a, b, c 使得 x = (a, c) 且 (a, b) ∈ R 且 (b, c) ∈ S
    rcases h_exist with ⟨a, b, c, h_eq, hpair1, hpair2⟩ -- 分解存在量詞
    constructor -- 需要證明兩個條件：1) x 在笛卡爾積中，2) 存在性條件
    · -- 證明 x ∈ product (domain R) (range S)
      -- 即證明 (a, c) ∈ (domain R) × (range S)
      rw [mem_product] -- 展開笛卡爾積的成員關係
      exists a -- 第一個分量是 a
      constructor
      · -- 證明 a ∈ domain R，即存在 b' 使得 (a, b') ∈ R
        rw [mem_domain]
        exact ⟨b, hpair1⟩ -- 使用 b 作為證人
      · exists c -- 第二個分量是 c
        constructor
        · -- 證明 c ∈ range S，即存在 b' 使得 (b', c) ∈ S
          rw [mem_range]
          exact ⟨b, hpair2⟩ -- 使用 b 作為證人
        · exact h_eq -- x = ordered_pair a c
    · -- 證明存在性條件
      exact ⟨a, b, c, h_eq, hpair1, hpair2⟩



-- ============================================
-- 關係運算的基本性質定理
-- ============================================
-- Theorem 3.1.2 (a)：反關係的反關係等於原關係
-- 即：(R⁻¹)⁻¹ = R
-- 數學意義：對關係取兩次反關係會回到原關係，這與函數的反函數性質類似
theorem R_inv_inv_eq_R (R A B : ZFSet)(hR : is_relation R A B) : (R⁻¹)⁻¹ = R := by
  apply ZFSet.ext -- 使用外延性公理，證明兩個集合相等
  intro x -- 對任意元素 x
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 x ∈ (R⁻¹)⁻¹，則 x ∈ R
    intro h_inv_inv -- 假設 x ∈ (R⁻¹)⁻¹
    rw [mem_inverse_relation] at h_inv_inv -- 展開反關係的刻畫
    rcases h_inv_inv with ⟨a, b, hpair, h_eq⟩ -- 得到 (a, b) ∈ R⁻¹ 且 x = (b, a)
    rw [mem_inverse_relation] at hpair -- 再次展開反關係的刻畫
    rcases hpair with ⟨b1, a1, hpair1, hpair2⟩ -- 得到 (b1, a1) ∈ R 且 (a, b) = (a1, b1)
    -- 比對有序對的分量以統一變數
    have a_eq_a1 : a = a1 := ordered_pair_eq_left hpair2 -- 從 (a, b) = (a1, b1) 得到 a = a1
    have b_eq_b1 : b = b1 := ordered_pair_eq_right hpair2 -- 從 (a, b) = (a1, b1) 得到 b = b1
    subst a_eq_a1 b_eq_b1 h_eq -- 替換變數，得到 x = (b1, a1) = (b, a)
    exact hpair1 -- 使用 (b1, a1) ∈ R（即 (b, a) ∈ R）證明 x ∈ R
  · -- 方向2：如果 x ∈ R，則 x ∈ (R⁻¹)⁻¹
    intro h_R -- 假設 x ∈ R
    rw [mem_inverse_relation] -- 展開反關係的刻畫
    rw [is_relation] at hR -- 使用關係的定義
    have h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b := hR x h_R -- 從關係定義得到 x 是有序對
    rcases h_exists with ⟨a, ha, b, hb, h_eq⟩ -- 分解存在量詞，得到 x = (a, b)
    exists b, a -- 使用 (b, a) 作為證人，因為我們要證明 x = (a, b) ∈ (R⁻¹)⁻¹
    constructor
    · -- 證明 (b, a) ∈ R⁻¹
      -- 根據反關係的定義，需要證明存在 c, d 使得 (c, d) ∈ R 且 (b, a) = (d, c)
      rw [mem_inverse_relation]
      exists a, b -- 使用 (a, b) 作為證人，因為 (a, b) ∈ R
      constructor
      · -- 證明 (a, b) ∈ R
        subst h_eq -- 將 x 替換為 (a, b)，因為 x = (a, b)
        exact h_R -- 這是我們的假設
      · rfl -- 證明 (b, a) = (b, a)，這是顯然的
    · -- 證明 x = (a, b)
      -- 注意：根據定義，x ∈ (R⁻¹)⁻¹ 當且僅當存在 c, d 使得 (c, d) ∈ R⁻¹ 且 x = (d, c)
      -- 我們已經證明了 (b, a) ∈ R⁻¹，所以需要證明 x = (a, b) = (a, b)
      -- 但實際上，我們需要的是 x = (a, b)，而我們已經有 h_eq : x = (a, b)
      exact h_eq -- 直接使用假設




-- Theorem 3.1.2 (b)：組合關係的結合律
-- 即：T ∘ (S ∘ R) = (T ∘ S) ∘ R
-- 數學意義：關係的組合運算滿足結合律，這與函數的複合類似
-- 證明策略：使用外延性公理，證明兩個集合包含相同的元素
theorem Comp_Associative_Law (T S R: ZFSet):
  composition_relation T (composition_relation S R) = composition_relation (composition_relation T S) R := by
  apply ZFSet.ext -- 使用外延性公理，將集合相等轉換為元素成員關係的等價
  intro x -- 對任意元素 x
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 x ∈ T ∘ (S ∘ R)，則 x ∈ (T ∘ S) ∘ R
    intro hl_comp -- 假設 x ∈ T ∘ (S ∘ R)
    rw [mem_composition_relation] at hl_comp -- 展開組合關係的刻畫
    -- 得到：存在 a, c, d 使得 x = (a, d) 且 (a, c) ∈ S ∘ R 且 (c, d) ∈ T
    rcases hl_comp with ⟨a, c, d, h_eq, hpair1, hpair2⟩
    rw [mem_composition_relation] at hpair1 -- 展開 (a, c) ∈ S ∘ R
    -- 得到：存在 a1, b, c1 使得 (a, c) = (a1, c1) 且 (a1, b) ∈ R 且 (b, c1) ∈ S
    rcases hpair1 with ⟨a1, b, c1, h_eq1, hpair11, hpair12⟩
    rw [mem_composition_relation] -- 目標：證明 x ∈ (T ∘ S) ∘ R
    exists a, b, d -- 使用 (a, b, d) 作為證人
    constructor
    · exact h_eq -- x = (a, d)
    · constructor
      · -- 證明 (a, b) ∈ R
        have a_eq_a1 : a = a1 := ordered_pair_eq_left h_eq1 -- 從 (a, c) = (a1, c1) 得到 a = a1
        subst a_eq_a1 -- 替換變數
        exact hpair11 -- 使用 (a1, b) ∈ R（即 (a, b) ∈ R）
      · -- 證明 (b, d) ∈ T ∘ S
        rw [mem_composition_relation]
        exists b, c, d -- 使用 (b, c, d) 作為證人
        constructor
        · rfl -- (b, d) = (b, d)
        · constructor
          · -- 證明 (b, c) ∈ S
            have c_eq_c1 : c = c1 := ordered_pair_eq_right h_eq1 -- 從 (a, c) = (a1, c1) 得到 c = c1
            subst c_eq_c1 -- 替換變數
            exact hpair12 -- 使用 (b, c1) ∈ S（即 (b, c) ∈ S）
          · -- 證明 (c, d) ∈ T
            exact hpair2 -- 直接使用假設
  · -- 方向2：如果 x ∈ (T ∘ S) ∘ R，則 x ∈ T ∘ (S ∘ R)
    intro hr_comp -- 假設 x ∈ (T ∘ S) ∘ R
    rw [mem_composition_relation] at hr_comp -- 展開組合關係的刻畫
    -- 得到：存在 a, b, d 使得 x = (a, d) 且 (a, b) ∈ R 且 (b, d) ∈ T ∘ S
    rcases hr_comp with ⟨a, b, d, h_eq, hpair1, hpair2⟩
    rw [mem_composition_relation] at hpair2 -- 展開 (b, d) ∈ T ∘ S
    -- 得到：存在 b1, c, d1 使得 (b, d) = (b1, d1) 且 (b1, c) ∈ S 且 (c, d1) ∈ T
    rcases hpair2 with ⟨b1, c, d1, h_eq1, hpair21, hpair22⟩
    rw [mem_composition_relation] -- 目標：證明 x ∈ T ∘ (S ∘ R)
    exists a, c, d -- 使用 (a, c, d) 作為證人
    constructor
    · exact h_eq -- x = (a, d)
    · constructor
      · -- 證明 (a, c) ∈ S ∘ R
        rw [mem_composition_relation]
        exists a, b, c -- 使用 (a, b, c) 作為證人
        constructor
        · rfl -- (a, c) = (a, c)
        · constructor
          · -- 證明 (a, b) ∈ R
            have b_eq_b1 : b = b1 := ordered_pair_eq_left h_eq1 -- 從 (b, d) = (b1, d1) 得到 b = b1
            subst b_eq_b1 -- 替換變數
            exact hpair1 -- 使用 (a, b) ∈ R
          · -- 證明 (b, c) ∈ S
            have b_eq_b1 : b = b1 := ordered_pair_eq_left h_eq1 -- 從 (b, d) = (b1, d1) 得到 b = b1
            subst b_eq_b1 -- 替換變數
            exact hpair21 -- 使用 (b1, c) ∈ S（即 (b, c) ∈ S）
      · -- 證明 (c, d) ∈ T
        have d_eq_d1 : d = d1 := ordered_pair_eq_right h_eq1 -- 從 (b, d) = (b1, d1) 得到 d = d1
        subst d_eq_d1 -- 替換變數
        exact hpair22 -- 使用 (c, d1) ∈ T（即 (c, d) ∈ T）


-- Theorem 3.1.2 (c)：恒等關係與關係的組合
-- 即：I_B ∘ R = R ∘ I_A
-- 數學意義：恒等關係在關係組合中的作用類似於單位元
-- 其中 I_A 是集合 A 上的恒等關係，I_B 是集合 B 上的恒等關係
theorem IB_Comp_R_eq_R_Comp_IA (B A R: ZFSet)(hR: is_relation R A B): identity_relation B ∘ R = R ∘ identity_relation A := by
  apply ZFSet.ext -- 使用外延性公理，證明兩個集合相等
  intro x -- 對任意元素 x
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 x ∈ I_B ∘ R，則 x ∈ R ∘ I_A
    intro h_IB_Comp_R -- 假設 x ∈ I_B ∘ R
    rw [mem_composition_relation] at h_IB_Comp_R -- 展開組合關係的刻畫
    -- 得到：存在 a, b, b1 使得 x = (a, b1) 且 (a, b) ∈ R 且 (b, b1) ∈ I_B
    rcases h_IB_Comp_R with ⟨a, b, b1, h_eq, hpair1, hpair2⟩
    rw [mem_composition_relation] -- 目標：證明 x ∈ R ∘ I_A
    rw [mem_identity_relation] at hpair2 -- 展開恒等關係的刻畫
    -- 得到：存在 b2 ∈ B 使得 (b, b1) = (b2, b2)
    rcases hpair2 with ⟨b2, hb2, hb2_eq⟩
    -- 比對有序對的分量
    have b1_eq_b2 : b1 = b2 := ordered_pair_eq_right hb2_eq -- 從 (b, b1) = (b2, b2) 得到 b1 = b2
    subst b1_eq_b2 -- 替換變數
    have b_eq_b1 : b = b1 := ordered_pair_eq_left hb2_eq -- 從 (b, b1) = (b2, b2) 得到 b = b1
    subst b_eq_b1 -- 替換變數，現在 b = b1 = b2
    rw [is_relation] at hR -- 使用關係的定義
    subst x -- 將 x 替換為 (a, b)
    -- 從 (a, b) ∈ R 和 is_relation 得到 a ∈ A, b ∈ B
    have h_exists : ∃ a1 ∈ A, ∃ b1 ∈ B, ordered_pair a b = ordered_pair a1 b1 := hR (ordered_pair a b) hpair1
    rcases h_exists with ⟨a1, ha1, b1, hb1, h_eq1⟩
    have a_eq_a1 : a = a1 := ordered_pair_eq_left h_eq1 -- 從 (a, b) = (a1, b1) 得到 a = a1
    subst a_eq_a1 -- 替換變數
    exists a, a, b -- 使用 (a, a, b) 作為證人，因為我們要證明 (a, b) ∈ R ∘ I_A
    constructor
    · rfl -- (a, b) = (a, b)
    · constructor
      · -- 證明 (a, a) ∈ I_A
        rw [mem_identity_relation]
        exact ⟨a, ha1, rfl⟩ -- 使用 a 作為證人，a ∈ A，且 (a, a) = (a, a)
      · -- 證明 (a, b) ∈ R
        exact hpair1 -- 直接使用假設
  · -- 方向2：如果 x ∈ R ∘ I_A，則 x ∈ I_B ∘ R
    intro h_R_Comp_IA -- 假設 x ∈ R ∘ I_A
    rw [mem_composition_relation] at h_R_Comp_IA -- 展開組合關係的刻畫
    -- 得到：存在 a, a1, b 使得 x = (a, b) 且 (a, a1) ∈ I_A 且 (a1, b) ∈ R
    rcases h_R_Comp_IA with ⟨a, a1, b, h_eq, hpair1, hpair2⟩
    rw [mem_composition_relation] -- 目標：證明 x ∈ I_B ∘ R
    exists a, b, b -- 使用 (a, b, b) 作為證人，因為我們要證明 (a, b) ∈ I_B ∘ R
    rw [mem_identity_relation] at hpair1 -- 展開恒等關係的刻畫
    -- 得到：存在 a2 ∈ A 使得 (a, a1) = (a2, a2)
    rcases hpair1 with ⟨a2, ha2, ha2_eq⟩
    -- 比對有序對的分量
    have a1_eq_a2 : a1 = a2 := ordered_pair_eq_right ha2_eq -- 從 (a, a1) = (a2, a2) 得到 a1 = a2
    subst a1_eq_a2 -- 替換變數
    have a_eq_a1 : a = a1 := ordered_pair_eq_left ha2_eq -- 從 (a, a1) = (a2, a2) 得到 a = a1
    subst a_eq_a1 -- 替換變數，現在 a = a1 = a2
    constructor
    · exact h_eq -- x = (a, b)
    · constructor
      · -- 證明 (a, b) ∈ R
        exact hpair2 -- 直接使用假設（因為 a = a1，所以 (a1, b) ∈ R 即 (a, b) ∈ R）
      · -- 證明 (b, b) ∈ I_B
        rw [mem_identity_relation]
        -- 需要證明 b ∈ B
        have hbB : b ∈ B := by
          rw [is_relation] at hR -- 使用關係的定義
          -- 從 (a, b) ∈ R 和 is_relation 得到 b ∈ B
          have h_exists : ∃ a1 ∈ A, ∃ b1 ∈ B, ordered_pair a b = ordered_pair a1 b1 := hR (ordered_pair a b) hpair2
          rcases h_exists with ⟨a1, ha1, b1, hb1, h_eq1⟩
          have b_eq_b1 : b = b1 := ordered_pair_eq_right h_eq1 -- 從 (a, b) = (a1, b1) 得到 b = b1
          subst b_eq_b1 -- 替換變數
          exact hb1 -- 使用 b1 ∈ B（即 b ∈ B）
        exact ⟨b, hbB, rfl⟩ -- 使用 b 作為證人，b ∈ B，且 (b, b) = (b, b)


-- Theorem 3.1.2 (d)：組合關係的反關係等於反關係的組合（順序相反）
-- 即：(S ∘ R)⁻¹ = R⁻¹ ∘ S⁻¹
-- 數學意義：關係組合的反關係等於反關係的逆序組合
-- 這類似於函數複合的反函數性質：(f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹
theorem inv_comp_eq_inv_comp_inv (S R : ZFSet) : (S ∘ R)⁻¹ = R⁻¹ ∘ S⁻¹ := by
  apply ZFSet.ext -- 使用外延性公理，證明兩個集合相等
  intro x -- 對任意元素 x
  constructor -- 將 ↔ 分成兩個方向
  · -- 方向1：如果 x ∈ (S ∘ R)⁻¹，則 x ∈ R⁻¹ ∘ S⁻¹
    intro h -- 假設 x ∈ (S ∘ R)⁻¹
    rw [mem_inverse_relation] at h -- 展開反關係的刻畫
    -- 得到：存在 a, c 使得 (a, c) ∈ S ∘ R 且 x = (c, a)
    rcases h with ⟨a, c, h_comp, h_eq_x⟩
    rw [mem_composition_relation] at h_comp -- 展開組合關係的刻畫
    -- 得到：存在 a1, b, c1 使得 (a, c) = (a1, c1) 且 (a1, b) ∈ R 且 (b, c1) ∈ S
    rcases h_comp with ⟨a1, b, c1, h_eq_ac, h_ab, h_bc⟩
    -- 比對有序對的分量以統一變數
    have a_eq : a = a1 := ordered_pair_eq_left h_eq_ac -- 從 (a, c) = (a1, c1) 得到 a = a1
    have c_eq : c = c1 := ordered_pair_eq_right h_eq_ac -- 從 (a, c) = (a1, c1) 得到 c = c1
    subst a_eq c_eq -- 替換變數
    subst h_eq_x -- 將 x 替換為 (c, a)，即 x = (c1, a1)
    rw [mem_composition_relation] -- 目標：證明 (c, a) ∈ R⁻¹ ∘ S⁻¹
    exists c, b, a -- 使用 (c, b, a) 作為證人
    constructor
    · rfl -- (c, a) = (c, a)
    · constructor
      · -- 證明 (c, b) ∈ S⁻¹
        -- 因為 (b, c) ∈ S，所以 (c, b) ∈ S⁻¹
        rw [mem_inverse_relation]
        exact ⟨b, c, h_bc, rfl⟩ -- 使用 (b, c) 作為證人，(b, c) ∈ S，且 (c, b) = (c, b)
      · -- 證明 (b, a) ∈ R⁻¹
        -- 因為 (a, b) ∈ R，所以 (b, a) ∈ R⁻¹
        rw [mem_inverse_relation]
        exact ⟨a, b, h_ab, rfl⟩ -- 使用 (a, b) 作為證人，(a, b) ∈ R，且 (b, a) = (b, a)
  · -- 方向2：如果 x ∈ R⁻¹ ∘ S⁻¹，則 x ∈ (S ∘ R)⁻¹
    intro h -- 假設 x ∈ R⁻¹ ∘ S⁻¹
    rw [mem_composition_relation] at h -- 展開組合關係的刻畫
    -- 得到：存在 c, b, a 使得 x = (c, a) 且 (c, b) ∈ S⁻¹ 且 (b, a) ∈ R⁻¹
    rcases h with ⟨c, b, a, h_eq_x, h_cb, h_ba⟩
    rw [mem_inverse_relation] at h_cb -- 展開反關係的刻畫
    -- 得到：存在 b1, c1 使得 (b1, c1) ∈ S 且 (c, b) = (c1, b1)
    rcases h_cb with ⟨b1, c1, h_bc, h_eq_cb⟩
    -- 比對有序對的分量
    have b_eq1 : b = b1 := ordered_pair_eq_right h_eq_cb -- 從 (c, b) = (c1, b1) 得到 b = b1
    have c_eq1 : c = c1 := ordered_pair_eq_left h_eq_cb -- 從 (c, b) = (c1, b1) 得到 c = c1
    subst b_eq1 c_eq1 -- 替換變數
    rw [mem_inverse_relation] at h_ba -- 展開反關係的刻畫
    -- 得到：存在 a1, b2 使得 (a1, b2) ∈ R 且 (b, a) = (b2, a1)
    rcases h_ba with ⟨a1, b2, h_ab, h_eq_ba⟩
    -- 比對有序對的分量
    have b_eq2 : b = b2 := ordered_pair_eq_left h_eq_ba -- 從 (b, a) = (b2, a1) 得到 b = b2
    have a_eq1 : a = a1 := ordered_pair_eq_right h_eq_ba -- 從 (b, a) = (b2, a1) 得到 a = a1
    subst b_eq2 a_eq1 -- 替換變數
    subst h_eq_x -- 將 x 替換為 (c, a)，即 x = (c1, a1)
    rw [mem_inverse_relation] -- 目標：證明 (c, a) ∈ (S ∘ R)⁻¹
    -- 根據反關係的定義，需要證明存在 a', b' 使得 (a', b') ∈ S ∘ R 且 (c, a) = (b', a')
    -- 我們使用 a 作為 a'，c 作為 b'
    refine ⟨a, c, ?_, rfl⟩
    -- 證明 (a, c) ∈ S ∘ R
    rw [mem_composition_relation]
    refine ⟨a, b, c, rfl, h_ab, h_bc⟩





--Chapter 3.2: Equivalence Relations
def is_reflexive (R A : ZFSet) : Prop :=
  identity_relation A ⊆ R

def is_symmetric (R : ZFSet) : Prop :=
  inverse_relation R ⊆ R

def is_transitive (R : ZFSet) : Prop :=
  R ∘ R ⊆ R

def is_equivalence (R A : ZFSet) : Prop :=
  is_reflexive R A ∧ is_symmetric R ∧ is_transitive R
