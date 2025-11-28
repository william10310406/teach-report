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
  · intro (hx_in_powerset, h_exists)
    exact h_exists
  · intro h_exists -- hx_in_powerset : x ∈ ZFSet.powerset (ZFSet.powerset (A ∪ B)), h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b

--Definition: A binary relation R from A to B is a subset of A × B.
def is_relation (R A B : ZFSet) : Prop := R ⊆ product A B

--Definition: The identity relation on A is the set {(a, a) | a ∈ A}.
def identity_relation (A : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, x = ordered_pair a a)
            (ZFSet.powerset (ZFSet.powerset (A ∪ A)))

--Definition: The domain of a relation R from A to B is the set of all first components of the ordered pairs in R.
def domain (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun a => ∃ b ∈ B, ordered_pair a b ∈ R)
            (ZFSet.powerset A)
--Definition: The range of a relation R from A to B is the set of all second components of the ordered pairs in R.
def range (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun b => ∃ a ∈ A, ordered_pair a b ∈ R)
            (ZFSet.powerset B)

def inverse (R A B : ZFSet) : ZFSet :=
  ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B, ordered_pair a b ∈ R ∧ x = ordered_pair b a)
            (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
