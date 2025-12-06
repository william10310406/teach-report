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
-- 關係的定義域 (Domain) 定義
-- ============================================
-- 定義：從集合 A 到集合 B 的關係 R 的定義域是所有 R 中有序對的第一個分量組成的集合
-- 即：domain R = {a ∈ A | ∃ b ∈ B, (a, b) ∈ R}
-- 在函數的語言中，定義域是"輸入"的集合
def domain (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun a => ∃ b ∈ B, ordered_pair a b ∈ R) (A)

-- 定理：a 屬於關係 R 的定義域當且僅當存在 b ∈ B 使得 (a, b) ∈ R
-- 這是定義域定義的直接刻畫
theorem mem_domain (R A B a : ZFSet)(hR : is_relation R A B) :
  a ∈ domain R A B ↔ ∃ b ∈ B, ordered_pair a b ∈ R := by
  rw [domain] -- 展開 domain 的定義：domain R A B = ZFSet.sep (fun a => ∃ b ∈ B, ordered_pair a b ∈ R) (A)
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：a ∈ A ∧ (∃ b ∈ B, ordered_pair a b ∈ R) ↔ (∃ b ∈ B, ordered_pair a b ∈ R)
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 a ∈ domain R A B，即 a ∈ A ∧ (∃ b ∈ B, ordered_pair a b ∈ R)
    exact h.2 -- 直接使用第二個分量，即存在性條件
  · intro h_exist -- 右到左：假設存在 b ∈ B 使得 ordered_pair a b ∈ R
    rcases h_exist with ⟨b, hbB, hpair⟩ -- 分解存在量詞，得到 b ∈ B, hpair : ordered_pair a b ∈ R
    -- 需要證明：a ∈ A ∧ (∃ b ∈ B, ordered_pair a b ∈ R)
    rw [is_relation] at hR -- 展開 is_relation 的定義：hR : ∀ x ∈ R, x ∈ product A B
    -- 使用 hR 證明 ordered_pair a b 在 product A B 中
    have hprod : ordered_pair a b ∈ product A B :=
      hR (ordered_pair a b) hpair -- 應用全稱量詞 hR：因為 ordered_pair a b ∈ R，所以 ordered_pair a b ∈ product A B
    -- 從 ordered_pair a b ∈ product A B 可以推出 a ∈ A
    have haA : a ∈ A := by
      rw [mem_product] at hprod -- 展開 mem_product，得到 ∃ a' ∈ A, ∃ b' ∈ B, ordered_pair a b = ordered_pair a' b'
      rcases hprod with ⟨a', ha', b', hb', h_eq⟩ -- 分解存在量詞
      have ha_eq : a = a' := ordered_pair_eq_left h_eq -- 使用有序對左分量唯一性引理
      rw [ha_eq] -- 將 a 替換為 a'
      exact ha' -- 使用 ha' : a' ∈ A
    exact ⟨haA, ⟨b, hbB, hpair⟩⟩ -- 構造對：第一個分量是 a ∈ A，第二個分量是存在性證明


-- ============================================
-- 關係的值域 (Range) 定義
-- ============================================
-- 定義：從集合 A 到集合 B 的關係 R 的值域是所有 R 中有序對的第二個分量組成的集合
-- 即：range R = {b ∈ B | ∃ a ∈ A, (a, b) ∈ R}
-- 在函數的語言中，值域是"輸出"的集合
def range (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun b => ∃ a ∈ A, ordered_pair a b ∈ R) (B)

-- 定理：b 屬於關係 R 的值域當且僅當存在 a ∈ A 使得 (a, b) ∈ R
-- 這是值域定義的直接刻畫
theorem mem_range (R A B b : ZFSet)(hR : is_relation R A B) :
  b ∈ range R A B ↔ ∃ a ∈ A, ordered_pair a b ∈ R := by
  rw [range] -- 展開 range 的定義：range R A B = ZFSet.sep (fun b => ∃ a ∈ A, ordered_pair a b ∈ R) (B)
  rw [ZFSet.mem_sep] -- 使用分離公理的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  -- 現在目標變成：b ∈ B ∧ (∃ a ∈ A, ordered_pair a b ∈ R) ↔ (∃ a ∈ A, ordered_pair a b ∈ R)
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- 左到右：假設 b ∈ range R A B，即 b ∈ B ∧ (∃ a ∈ A, ordered_pair a b ∈ R)
    exact h.2 -- 直接使用第二個分量，即存在性條件
  · intro h_exist -- 右到左：假設存在 a ∈ A 使得 ordered_pair a b ∈ R
    rcases h_exist with ⟨a, haA, hpair⟩ -- 分解存在量詞，得到 a ∈ A, hpair : ordered_pair a b ∈ R
    -- 需要證明：b ∈ B ∧ (∃ a ∈ A, ordered_pair a b ∈ R)
    rw [is_relation] at hR -- 展開 is_relation 的定義：hR : ∀ x ∈ R, x ∈ product A B
    -- 使用 hR 證明 ordered_pair a b 在 product A B 中
    have hprod : ordered_pair a b ∈ product A B :=
      hR (ordered_pair a b) hpair -- 應用全稱量詞 hR：因為 ordered_pair a b ∈ R，所以 ordered_pair a b ∈ product A B
    -- 從 ordered_pair a b ∈ product A B 可以推出 b ∈ B
    have hbB : b ∈ B := by
      rw [mem_product] at hprod -- 展開 mem_product，得到 ∃ a' ∈ A, ∃ b' ∈ B, ordered_pair a b = ordered_pair a' b'
      rcases hprod with ⟨a', ha', b', hb', h_eq⟩ -- 分解存在量詞
      have hb_eq : b = b' := ordered_pair_eq_right h_eq -- 使用有序對右分量唯一性引理
      rw [hb_eq] -- 將 b 替換為 b'
      exact hb' -- 使用 hb' : b' ∈ B
    exact ⟨hbB, ⟨a, haA, hpair⟩⟩ -- 構造對：第一個分量是 b ∈ B，第二個分量是存在性證明



def inverse_relation (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair b a)
            (product B A)

theorem mem_inverse_relation (R A B x : ZFSet) : x ∈ inverse_relation R A B ↔ ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair b a := by
  rw [inverse_relation] -- 展開 inverse_relation 的定義：inverse_relation R A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair b a ∈ R ∧ x = ordered_pair b a) (product B A)
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- h : x ∈ inverse_relation R A B
    exact h.2 -- 直接使用 h.2
  · intro h_exist
    rcases h_exist with ⟨a, haA, b, hbB, hpair, h_eq⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hpair : ordered_pair b a ∈ R, x = ordered_pair b a
    have hprod : x ∈ product B A := by
      rw [mem_product]
      exact ⟨b, hbB, a, haA, h_eq⟩
    exact ⟨hprod, ⟨a, haA, b, hbB, hpair, h_eq⟩⟩




-- Theorem 2.2.4 (a)：Dom(R⁻¹) = Rng(R)
theorem dom_inv_eq_rng (R A B : ZFSet) (hR : is_relation R A B) : domain (inverse_relation R A B) B A = range R A B := by
  apply ZFSet.ext
  intro y
  constructor
  · intro h_dom
    rw [domain, ZFSet.mem_sep] at h_dom
    rcases h_dom with ⟨y_in_B, h_exist⟩
    rcases h_exist with ⟨a, haA, hpair⟩
    rw [mem_inverse_relation] at hpair
    rw [range, ZFSet.mem_sep]
    rw [is_relation] at hR
    rcases hpair with ⟨b, hbB, a, haA, hpair, h_eq⟩
    have y_eq_b : y = a := ordered_pair_eq_left h_eq
