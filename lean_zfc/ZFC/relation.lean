import Mathlib.SetTheory.ZFC.Basic
--3. Relations and Partitions

-- 有序對 (Ordered Pair) 定義 (Kuratowski definition)
-- (a, b) = {{a}, {a, b}}
def ordered_pair (a b : ZFSet) : ZFSet :=
  {{a}, {a, b}}

theorem mem_ordered_pair (a b x : ZFSet) : x ∈ ordered_pair a b ↔ x = {a} ∨ x = {a, b} :=
  ZFSet.mem_pair

-- Kuratowski ordered pair uniqueness (minimal version)
lemma ordered_pair_eq_left {a b a' b' : ZFSet} :ordered_pair a b = ordered_pair a' b' → a = a' := by
  intro h
  have ha_mem : {a} ∈ ordered_pair a b := by
    rw [ordered_pair]
    rw [ordered_pair, ordered_pair] at h
    apply ZFSet.mem_pair.mpr -- 1. 使用配對公理：x ∈ {y, z} ↔ x = y ∨ x = z
    left                     -- 2. 我們選擇證明左邊的情況 (即 {a} = {a})
    rfl                      -- 3. 左邊等於左邊，證畢
  rw [h] at ha_mem
  rw [ordered_pair] at ha_mem
  rw [ZFSet.mem_pair] at ha_mem
  cases ha_mem with
  | inl h_eq_a =>
    have h_a_in : a ∈ ({a} : ZFSet) := ZFSet.mem_singleton.mpr rfl
    rw [h_eq_a] at h_a_in
    rw [ZFSet.mem_singleton] at h_a_in
    exact h_a_in
  | inr h_eq_a_b =>
    have h_aprime_in : a' ∈ ({a', b'} : ZFSet) := ZFSet.mem_pair.mpr (Or.inl rfl)
    rw [← h_eq_a_b] at h_aprime_in
    rw [ZFSet.mem_singleton] at h_aprime_in
    exact h_aprime_in.symm

lemma ordered_pair_eq_right {a b a' b' : ZFSet} :ordered_pair a b = ordered_pair a' b' → b = b' := by -- 假設兩個有序對相等，目標是推出第二個分量相等
  intro h
  have ha_eq : a = a' := ordered_pair_eq_left h
  rw [← ha_eq] at h
  rw [ordered_pair, ordered_pair] at h
  have h_pair : ({a, b} : ZFSet) = ({a, b'} : ZFSet) := by
    have h_in_lhs : {a, b} ∈ {{a}, {a, b}} := ZFSet.mem_pair.mpr (Or.inr rfl)
    rw [h] at h_in_lhs
    rw [ZFSet.mem_pair] at h_in_lhs
    cases h_in_lhs with
    | inl h_eq_a =>
      rw [h_eq_a] at h
      have h_ab'_in_lhs : {a, b'} ∈ ({ {a}, {a} } : ZFSet) := by
        rw [h]
        apply ZFSet.mem_pair.mpr
        right
        exact rfl
      rw [ZFSet.mem_pair] at h_ab'_in_lhs
      cases h_ab'_in_lhs with
      | inl h_l =>
        rw [h_l]
        exact h_eq_a
      | inr h_r =>
        rw [h_r]
        exact h_eq_a
    | inr h_eq_a_b =>
      exact h_eq_a_b
  have h_b_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl)
  rw [h_pair] at h_b_in
  rw [ZFSet.mem_pair] at h_b_in
  cases h_b_in with
  | inr h_eq_b =>
    exact h_eq_b
  | inl h_eq_a =>
    rw [h_eq_a] at h_pair
    have h_b_in_lhs : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl)
    rw [← h_pair] at h_b_in_lhs
    rw [ZFSet.mem_pair] at h_b_in_lhs
    cases h_b_in_lhs with
    | inl h_l =>
      rw [h_l]
      exact h_eq_a
    | inr h_r =>
      rw [h_r]
      exact h_eq_a


-- 笛卡爾積 (Cartesian Product) 定義
-- A × B = { (a, b) | a ∈ A, b ∈ B }
-- 在 ZFC 中，我們需要從一個足夠大的集合（A ∪ B 的冪集的冪集）中分離出有序對
def product (A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b)
            (ZFSet.powerset (ZFSet.powerset (A ∪ B)))

theorem mem_product (A B x : ZFSet) : x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b := by
  rw [product] -- 展開 product 的定義：product A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_powerset, h_exists⟩
    exact h_exists
  · intro h_exists
    constructor
    · rcases h_exists with ⟨a, ha, b, hb, rfl⟩ --將存在量詞分解成 a ∈ A, b ∈ B, x = ordered_pair a b
      rw [ordered_pair] --展開 ordered_pair 的定義：x = {{a}, {a, b}}
      apply ZFSet.mem_powerset.mpr --使用冪集的成員關係：x ∈ powerset A ↔ x ⊆ A，目標變成 {{a}, {a, b}} ⊆ powerset (A ∪ B)
      intro z hz -- z : any arbitrary element, hz : z ∈ {{a}, {a, b}}
      rw [ZFSet.mem_pair] at hz --將 z ∈ {{a}, {a, b}} 拆成 z = {a} ∨ z = {a, b}
      cases hz with
      | inl hz_eq => -- z = {a}
        rw [hz_eq] --將 z 重寫為 {a}
        apply ZFSet.mem_powerset.mpr --證明 {a} ∈ powerset (A ∪ B)，即 {a} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a}
        rw [ZFSet.mem_singleton] at hw --將 w ∈ {a} 轉換為 w = a
        rw [hw] --將 w 重寫為 a
        rw [ZFSet.mem_union] --將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
        left
        exact ha
      | inr hz_eq => -- z = {a, b}
        rw [hz_eq] --將 z 重寫為 {a, b}
        apply ZFSet.mem_powerset.mpr --證明 {a, b} ∈ powerset (A ∪ B)，即 {a, b} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a, b}
        rw [ZFSet.mem_pair] at hw --將 w ∈ {a, b} 拆成 w = a ∨ w = b
        cases hw with
        | inl hw_eq => -- w = a
          rw [hw_eq] --將 w 重寫為 a
          rw [ZFSet.mem_union] --將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
          left
          exact ha
        | inr hw_eq => -- w = b
          rw [hw_eq] --將 w 重寫為 b
          rw [ZFSet.mem_union] --將 b ∈ A ∪ B 拆成 a ∈ A ∨ b ∈ B
          right
          exact hb
    · exact h_exists -- 直接使用 h_exists


--Definition: A binary relation R from A to B is a subset of A × B.
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



--Definition: The identity relation on A is the set {(a, a) | a ∈ A}.
def identity_relation (A : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a)
            (product A A)

theorem mem_identity_relation (A x :ZFSet) : x ∈ identity_relation A ↔ ∃ a ∈ A, x = ordered_pair a a := by
  rw [identity_relation] -- 展開 identity_relation 的定義：identity_relation A = ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a) (ZFSet.powerset (ZFSet.powerset (A ∪ A)))
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_product_A_A, h_exists⟩
    exact h_exists
  · intro h
    rcases h with ⟨a, ha, h_eq⟩ --將存在量詞分解成 a ∈ A, x = ordered_pair a a
    constructor
    · rw [mem_product]
      exact ⟨a, ha, a, ha, h_eq⟩
    · exact ⟨a, ha, h_eq⟩



--Definition: The domain of a relation R from A to B is the set of all first components of the ordered pairs in R.
def domain (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun a => ∃ b ∈ B, ordered_pair a b ∈ R) (A)

theorem mem_domain (R A B a : ZFSet)(hR : is_relation R A B) :
  a ∈ domain R A B ↔ ∃ b ∈ B, ordered_pair a b ∈ R := by
  rw [domain] -- 展開 domain 的定義：domain R A B = ZFSet.sep (fun a => ∃ b ∈ B, ordered_pair a b ∈ R) (A)
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- h : a ∈ domain R A B
    exact h.2 -- 直接使用 h.2
  · intro h_exist
    rcases h_exist with ⟨b, hbB, hpair⟩ -- 分解存在量詞，得到 b ∈ B, hpair : ordered_pair a b ∈ R
    rw [is_relation] at hR -- 使用 is_relation：ordered_pair a b ∈ R → a ∈ A ∧ b ∈ B
    have hprod : ordered_pair a b ∈ product A B :=
      hR (ordered_pair a b) hpair -- 使用 is_relation：ordered_pair a b ∈ R → a ∈ A ∧ b ∈ B
    have haA : a ∈ A := by
      rw [mem_product] at hprod
      rcases hprod with ⟨a', ha', b', hb', h_eq⟩
      have ha_eq : a = a' := ordered_pair_eq_left h_eq
      rw [ha_eq]
      exact ha'
    exact ⟨haA, ⟨b, hbB, hpair⟩⟩


def range (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun b => ∃ a ∈ A, ordered_pair a b ∈ R) (B)

theorem mem_range (R A B b : ZFSet)(hR : is_relation R A B) :
  b ∈ range R A B ↔ ∃ a ∈ A, ordered_pair a b ∈ R := by
  rw [range] -- 展開 range 的定義：range R A B = ZFSet.sep (fun b => ∃ a ∈ A, ordered_pair a b ∈ R) (B)
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro h -- h : b ∈ range R A B
    exact h.2 -- 直接使用 h.2
  · intro h_exist
    rcases h_exist with ⟨a, haA, hpair⟩ -- 分解存在量詞，得到 a ∈ A, hpair : ordered_pair a b ∈ R
    rw [is_relation] at hR -- 使用 is_relation：ordered_pair a b ∈ R → a ∈ A ∧ b ∈ B
    have hprod : ordered_pair a b ∈ product A B :=
      hR (ordered_pair a b) hpair -- 使用 is_relation：ordered_pair a b ∈ R → a ∈ A ∧ b ∈ B
    have hbB : b ∈ B := by
      rw [mem_product] at hprod
      rcases hprod with ⟨a', ha', b', hb', h_eq⟩
      have hb_eq : b = b' := ordered_pair_eq_right h_eq
      rw [hb_eq]
      exact hb'
    exact ⟨hbB, ⟨a, haA, hpair⟩⟩
