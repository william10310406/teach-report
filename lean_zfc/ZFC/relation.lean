import Mathlib.SetTheory.ZFC.Basic
--2.3 Relations and Partitions

-- 有序對 (Ordered Pair) 定義 (Kuratowski definition)
-- (a, b) = {{a}, {a, b}}
def ordered_pair (a b : ZFSet) : ZFSet :=
  {{a}, {a, b}}

theorem mem_ordered_pair (a b x : ZFSet) : x ∈ ordered_pair a b ↔ x = {a} ∨ x = {a, b} :=
  ZFSet.mem_pair

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
def is_relation (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair a b)
            (product A B)

theorem mem_is_relation (R A B x : ZFSet) : x ∈ is_relation R A B ↔ x ∈ product A B ∧ x ∈ R := by
  rw [is_relation] -- 展開 is_relation 的定義：is_relation R A B = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_product_A_B, h_exists⟩
    rcases h_exists with ⟨a, ha, b, hb, hR, h_eq⟩ --將存在量詞分解成 a ∈ A, b ∈ B, ordered_pair a b ∈ R, x = ordered_pair a b
    constructor
    · exact hx_in_product_A_B
    · rw [h_eq] --將 x = ordered_pair a b 重寫為 x = ordered_pair a b
      exact hR
  · intro ⟨hx_in_product_A_B, hx_in_R⟩
    constructor
    · exact hx_in_product_A_B
    · rw [mem_product] at hx_in_product_A_B
      rcases hx_in_product_A_B with ⟨a, ha, b, hb, h_eq⟩
      rw [h_eq] at hx_in_R
      exact ⟨a, ha, b, hb, hx_in_R, h_eq⟩



--Definition: The identity relation on A is the set {(a, a) | a ∈ A}.
def identity_relation (A : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a)
            (ZFSet.powerset (ZFSet.powerset (A ∪ A)))

theorem mem_identity_relation (A x :ZFSet) : x ∈ identity_relation A ↔ ∃ a ∈ A, x = ordered_pair a a := by
  rw [identity_relation] -- 展開 identity_relation 的定義：identity_relation A = ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a) (ZFSet.powerset (ZFSet.powerset (A ∪ A)))
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_powerset, h_exists⟩
    exact h_exists
  · intro h_exists
    constructor
    · rcases h_exists with ⟨a, ha, h_eq⟩ --將存在量詞分解成 a ∈ A, x = ordered_pair a a
      rw [ordered_pair] at h_eq
      apply ZFSet.mem_powerset.mpr --證明 {{a}, {a, a}} ∈ powerset (A ∪ A)，即 {{a}, {a, a}} ⊆ A ∪ A
      intro z hz -- z : any arbitrary element, hz : z ∈ {{a}, {a, a}}
      rw [h_eq] at hz --將 x = ordered_pair a a 重寫為 z = {{a}, {a, a}}
      rw [ZFSet.mem_pair] at hz --將 z ∈ {{a}, {a, a}} 拆成 z = {a} ∨ z = {a, a}
      cases hz with
      | inl hz_eq => -- z = {a}
        rw [hz_eq] --將 z 重寫為 {a}
        apply ZFSet.mem_powerset.mpr --證明 {a} ∈ powerset (A ∪ A)，即 {a} ⊆ A ∪ A
        intro w hw -- w : any arbitrary element, hw : w ∈ {a}
        rw [ZFSet.mem_singleton] at hw --將 w ∈ {a} 轉換為 w = a
        rw [hw] --將 w 重寫為 a
        rw [ZFSet.mem_union] --將 a ∈ A ∪ A 拆成 a ∈ A ∨ a ∈ A
        left
