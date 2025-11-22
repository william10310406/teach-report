import Mathlib.SetTheory.ZFC.Basic

namespace ZFC

-- ============================================
-- 第一部分：使用 ZF 公設構造自然數
-- ============================================
-- 在 ZFC 中，自然數使用 von Neumann 構造法：
-- 0 = ∅ (空集)
def nat_zero : ZFSet := ZFSet.empty
-- 證明0的性質：0是空集
theorem nat_zero_is_empty : nat_zero = ZFSet.empty := rfl
-- 1 = {0} = {∅}
-- 注意：我們使用 insert 來定義，因為這樣更容易與 omega_succ 配合
def nat_one : ZFSet := insert nat_zero nat_zero
-- 證明 1 的性質：1 包含 0
theorem nat_one_contains_zero : nat_zero ∈ nat_one := by
  -- nat_one = insert nat_zero nat_zero
  rw [nat_one]
  -- 使用 ZFSet.mem_insert：x ∈ insert x y
  exact ZFSet.mem_insert nat_zero nat_zero
-- 2 = {0, 1} = {∅, {∅}}
-- 在 von Neumann 構造中，2 = insert 1 1 = {0, 1}
def nat_two : ZFSet := insert nat_one nat_one
-- 證明 2 的性質：2 包含 0 和 1
theorem nat_two_contains_one : nat_one ∈ nat_two := by
  rw [nat_two]
  -- 使用 ZFSet.mem_insert：x ∈ insert x y
  exact ZFSet.mem_insert nat_one nat_one

theorem nat_two_contains_zero : nat_zero ∈ nat_two := by
  rw [nat_two]
  -- nat_zero ∈ insert nat_one nat_one 意味著 nat_zero = nat_one 或 nat_zero ∈ nat_one
  -- 我們選擇第二個選項：nat_zero ∈ nat_one
  rw [ZFSet.mem_insert_iff]
  right
  exact nat_one_contains_zero
-- 3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}
-- 注意：配對公設只能構造兩個元素的集合
-- 要構造三個元素，我們使用聯集：3 = {0, 1} ∪ {2} = nat_two ∪ {nat_two}
def nat_three : ZFSet := nat_two ∪ {nat_two}

-- 證明 3 的性質：3 包含 0、1 和 2
theorem nat_three_contains_zero : nat_zero ∈ nat_three := by
  rw [nat_three]
  -- 使用聯集的性質：x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
  rw [ZFSet.mem_union]
  left
  exact nat_two_contains_zero

theorem nat_three_contains_one : nat_one ∈ nat_three := by
  rw [nat_three]
  rw [ZFSet.mem_union]
  left
  exact nat_two_contains_one

theorem nat_three_contains_two : nat_two ∈ nat_three := by
  rw [nat_three]
  -- nat_two ∈ nat_two ∪ {nat_two} 意味著 nat_two ∈ nat_two 或 nat_two ∈ {nat_two}
  -- 我們選擇第二個選項：nat_two ∈ {nat_two}
  rw [ZFSet.mem_union]
  right
  -- 使用 ZFSet.mem_singleton：nat_two ∈ {nat_two} ↔ nat_two = nat_two
  rw [ZFSet.mem_singleton]
-- ...
-- 定義後繼函數：n 的後繼是 n ∪ {n}
def succ (n : ZFSet) : ZFSet := n ∪ {n}
-- 證明後繼的性質：n 屬於它的後繼
theorem mem_succ_self (n : ZFSet) : n ∈ succ n := by
  rw [succ]
  rw [ZFSet.mem_union]
  right
  rw [ZFSet.mem_singleton]
-- 自然數集合就是 ω (omega)，我們已經在無窮公設中看到它
-- 證明我們定義的自然數都在 omega 中
theorem nat_zero_in_omega : nat_zero ∈ ZFSet.omega := ZFSet.omega_zero

theorem nat_one_in_omega : nat_one ∈ ZFSet.omega := by
  -- nat_one = insert nat_zero nat_zero
  rw [nat_one]
  -- 使用 ZFSet.omega_succ：如果 nat_zero ∈ omega，則 insert nat_zero nat_zero ∈ omega
  apply ZFSet.omega_succ
  exact nat_zero_in_omega

theorem nat_two_in_omega : nat_two ∈ ZFSet.omega := by
  -- nat_two = insert nat_one nat_one
  rw [nat_two]
  -- 使用 ZFSet.omega_succ：如果 nat_one ∈ omega，則 insert nat_one nat_one ∈ omega
  apply ZFSet.omega_succ
  exact nat_one_in_omega

theorem nat_three_in_omega : nat_three ∈ ZFSet.omega := by
  -- nat_three = nat_two ∪ {nat_two}
  -- 在 von Neumann 構造中，insert nat_two nat_two = nat_two ∪ {nat_two}
  -- 所以我們需要證明 nat_two ∪ {nat_two} = insert nat_two nat_two
  -- 然後使用 ZFSet.omega_succ
  have h_eq : nat_three = insert nat_two nat_two := by
    -- 證明 nat_two ∪ {nat_two} = insert nat_two nat_two
    -- 這需要檢查 insert 的定義：insert x y = {x} ∪ y
    -- 所以 insert nat_two nat_two = {nat_two} ∪ nat_two = nat_two ∪ {nat_two}
    ext x
    rw [nat_three]
    -- x ∈ nat_two ∪ {nat_two} ↔ x ∈ nat_two ∨ x ∈ {nat_two}
    rw [ZFSet.mem_union]
    -- x ∈ insert nat_two nat_two ↔ x = nat_two ∨ x ∈ nat_two
    rw [ZFSet.mem_insert_iff]
    -- 這兩個等價，因為 x ∈ {nat_two} ↔ x = nat_two
    rw [ZFSet.mem_singleton]
    -- 現在需要證明 x ∈ nat_two ∨ x = nat_two ↔ x = nat_two ∨ x ∈ nat_two
    -- 這兩個等價，因為 ∨ 是交換的
    rw [or_comm]
  rw [h_eq]
  -- 現在可以使用 ZFSet.omega_succ
  apply ZFSet.omega_succ
  exact nat_two_in_omega

-- ============================================
-- 驗證：實際展示自然數的構造
-- ============================================

-- 注意：在 Lean 的 InfoView 中，將游標放在下面的定義上就能看到類型信息
-- 你也可以在文件中取消註釋下面的 #check 命令來查看

-- 驗證 1：檢查自然數的類型（將游標放在這些定義上查看）
-- 注意：InfoView 中顯示的 "ZFC.nat_zero.{u_1} : ZFSet.{u_1}" 不是錯誤！
-- 這是 #check 命令的正常輸出，表示 nat_zero 的類型是 ZFSet
#check nat_zero  -- 會顯示：ZFC.nat_zero.{u_1} : ZFSet.{u_1}
#check nat_one   -- 會顯示：ZFC.nat_one.{u_1} : ZFSet.{u_1}
#check nat_two   -- 會顯示：ZFC.nat_two.{u_1} : ZFSet.{u_1}
#check nat_three -- 會顯示：ZFC.nat_three.{u_1} : ZFSet.{u_1}

-- 驗證 2：檢查自然數之間的關係
#check nat_zero_in_omega
#check nat_one_in_omega
#check nat_two_in_omega
#check nat_three_in_omega

-- 驗證 3：創建一些可以在 InfoView 中直接查看的示例
-- 將游標放在這些定義上，InfoView 會顯示它們的類型和值

-- 這些等式可以在 InfoView 中查看，顯示自然數的構造方式
example : nat_zero = ZFSet.empty := rfl
example : nat_one = insert nat_zero nat_zero := rfl
example : nat_two = insert nat_one nat_one := rfl
example : nat_three = nat_two ∪ {nat_two} := rfl

-- 如果你想要在 InfoView 中看到自然數的定義，將游標放在下面這些行：
-- nat_zero  -- 會顯示：nat_zero : ZFSet
-- nat_one   -- 會顯示：nat_one : ZFSet
-- nat_two   -- 會顯示：nat_two : ZFSet
-- nat_three -- 會顯示：nat_three : ZFSet

-- 這些可以在 InfoView 中查看的成員關係證明
example : nat_zero ∈ nat_one := nat_one_contains_zero
example : nat_one ∈ nat_two := nat_two_contains_one
example : nat_two ∈ nat_three := nat_three_contains_two
example : nat_zero ∈ nat_two := nat_two_contains_zero
example : nat_zero ∈ nat_three := nat_three_contains_zero
example : nat_one ∈ nat_three := nat_three_contains_one

-- 驗證 3：證明自然數的順序關係（在 von Neumann 構造中，m < n 當且僅當 m ∈ n）
theorem show_zero_in_one : nat_zero ∈ nat_one := nat_one_contains_zero
theorem show_one_in_two : nat_one ∈ nat_two := nat_two_contains_one
theorem show_two_in_three : nat_two ∈ nat_three := nat_three_contains_two

-- 驗證 4：證明後繼函數的性質
-- 證明：nat_one 是 nat_zero 的後繼
theorem show_one_is_succ_zero : nat_one = succ nat_zero := by
  -- nat_one = insert nat_zero nat_zero
  -- succ nat_zero = nat_zero ∪ {nat_zero} = insert nat_zero nat_zero
  ext x
  rw [nat_one]
  rw [succ]
  rw [ZFSet.mem_insert_iff]
  rw [ZFSet.mem_union]
  rw [ZFSet.mem_singleton]
  rw [or_comm]

-- 證明：nat_two 是 nat_one 的後繼
theorem show_two_is_succ_one : nat_two = succ nat_one := by
  ext x
  rw [nat_two]
  rw [succ]
  rw [ZFSet.mem_insert_iff]
  rw [ZFSet.mem_union]
  rw [ZFSet.mem_singleton]
  rw [or_comm]

-- 證明：nat_three 是 nat_two 的後繼
theorem show_three_is_succ_two : nat_three = succ nat_two := by
  -- 使用之前證明的等式
  have h_eq : nat_three = insert nat_two nat_two := by
    ext x
    rw [nat_three]
    rw [ZFSet.mem_union]
    rw [ZFSet.mem_insert_iff]
    rw [ZFSet.mem_singleton]
    rw [or_comm]
  rw [h_eq]
  rw [succ]
  ext x
  rw [ZFSet.mem_insert_iff]
  rw [ZFSet.mem_union]
  rw [ZFSet.mem_singleton]
  rw [or_comm]

-- 驗證 5：證明 0 不是任何數的後繼（Peano 公設）
theorem show_zero_not_successor (n : ZFSet) : succ n ≠ nat_zero := by
  intro h_eq
  have h_mem : n ∈ succ n := mem_succ_self n
  rw [h_eq] at h_mem
  rw [nat_zero_is_empty] at h_mem
  exact ZFSet.notMem_empty n h_mem

-- 驗證 6：展示自然數的包含關係
-- 在 von Neumann 構造中，每個自然數都包含所有比它小的自然數
theorem show_zero_in_two : nat_zero ∈ nat_two := nat_two_contains_zero
theorem show_zero_in_three : nat_zero ∈ nat_three := nat_three_contains_zero
theorem show_one_in_three : nat_one ∈ nat_three := nat_three_contains_one

-- 驗證 7：證明所有自然數都在 omega 中
-- 這已經證明了！我們可以總結：
theorem all_naturals_in_omega :
  nat_zero ∈ ZFSet.omega ∧
  nat_one ∈ ZFSet.omega ∧
  nat_two ∈ ZFSet.omega ∧
  nat_three ∈ ZFSet.omega := by
  constructor
  · exact nat_zero_in_omega
  · constructor
    · exact nat_one_in_omega
    · constructor
      · exact nat_two_in_omega
      · exact nat_three_in_omega

-- ============================================
-- 如何在 InfoView 中查看自然數
-- ============================================
--
-- 方法 1：將游標放在定義上（如 nat_zero, nat_one 等）
--         在 InfoView 中會顯示類型：ZFSet
--
-- 方法 2：將游標放在 example 語句上（如第 139-150 行）
--         會顯示證明的類型，例如：nat_zero ∈ nat_one
--
-- 方法 3：取消註釋 #check 命令（第 126-135 行）
--         將游標放在 #check 行上，InfoView 會顯示結果
--
-- 方法 4：將游標放在任何 theorem 名稱上
--         會顯示該定理的完整類型簽名
--
-- 提示：如果你想要看到自然數的"值"，可以查看：
--       - example : nat_zero = ZFSet.empty := rfl  (第 139 行)
--       - example : nat_one = insert nat_zero nat_zero := rfl  (第 140 行)
--       將游標放在這些 example 上，InfoView 會顯示它們的類型

-- 總結：我們已經成功構造了自然數！
-- 1. 定義了 0, 1, 2, 3
-- 2. 證明了它們都在 omega 中
-- 3. 證明了它們之間的順序關係
-- 4. 證明了後繼函數的性質
-- 5. 證明了 Peano 公設的一部分（0 不是任何數的後繼）

-- ============================================
-- 第二部分：使用自然數構造整數
-- ============================================
-- 現在我們將使用剛剛構造的自然數來構造整數
-- 我們會一步一步地進行，就像構造自然數一樣

-- ============================================
-- 第一步：理解整數的表示方法
-- ============================================
-- 整數 (a, b) 表示 a - b
-- 例如：(3, 1) 表示 3 - 1 = 2
--      (1, 3) 表示 1 - 3 = -2
--      (2, 2) 表示 2 - 2 = 0
--
-- 注意：同一個整數可以用不同的有序對表示
-- 例如：2 可以表示為 (2, 0) 或 (3, 1) 或 (5, 3)
-- 它們都滿足：第一個數 - 第二個數 = 2
--
-- 這就是為什麼我們需要：
-- 1. 等價關係（equivalence relation）：定義哪些有序對表示同一個整數
-- 2. 等價類（equivalence classes/partition）：每個整數就是一個等價類
--
-- 等價關係：(a, b) ~ (c, d) 當且僅當 a + d = b + c
-- 這對應於：a - b = c - d

-- ============================================
-- 第二步：定義有序對（Kuratowski 配對）
-- ============================================
-- 在 ZFC 中，有序對 (a, b) 定義為 {{a}, {a, b}}
-- 這確保了 (a, b) = (c, d) 當且僅當 a = c 且 b = d
--
-- 為什麼這樣定義？
-- 1. 只使用集合（符合 ZFC）
-- 2. 可以區分順序：(a, b) ≠ (b, a)（當 a ≠ b 時）
-- 3. 可以判斷兩個有序對是否相等
--
-- 注意：{{a}, {a, b}} 有兩個元素：
--   - {a}（單元素集合）
--   - {a, b}（雙元素集合，當 a ≠ b 時）
--   當 a = b 時，{{a}, {a, a}} = {{a}}（只有一個元素）
--
-- 現在請你定義：
-- 1. ordered_pair 函數：def ordered_pair (a b : ZFSet) : ZFSet := {{a}, {a, b}}
def ordered_pair (a b : ZFSet) : ZFSet := {{a}, {a, b}}
#check ordered_pair
-- 2. 一些測試用例：int_zero_pair, int_one_pair, int_neg_one_pair
def int_zero_pair : ZFSet := ordered_pair nat_zero nat_zero
def int_one_pair : ZFSet := ordered_pair nat_one nat_zero
def int_neg_one_pair : ZFSet := ordered_pair nat_zero nat_one
-- 3. 使用 #check 來驗證類型
#check int_zero_pair
#check int_one_pair
#check int_neg_one_pair

-- ============================================
-- 第三步：定義關係（Relation）
-- ============================================
-- 在數學中，關係是一個重要的概念
-- 二元關係 R 是一個集合，其元素是有序對 (a, b)
-- 我們通常寫作 a R b 或 (a, b) ∈ R
--
-- 在 ZFC 中，關係可以定義為：
-- 1. 一個包含有序對的集合：R = {(a₁, b₁), (a₂, b₂), ...}
-- 2. 或者，作為一個謂詞：R : ZFSet → ZFSet → Prop
--
-- 對於我們的用途，我們使用第二種方法（謂詞），因為它更靈活
-- 但我們也可以定義第一種方法（集合）作為補充
--
-- 請你定義：
-- 1. 二元關係的類型：一個函數，接受兩個 ZFSet，返回 Prop
--    注意：函數類型的類型層級比 Type 高，所以我們使用 Type 1
--    def binary_relation : Type 1 := ZFSet → ZFSet → Prop
--    或者，我們可以直接使用類型別名：
--    def binary_relation := ZFSet → ZFSet → Prop
def binary_relation : Type 1 := ZFSet → ZFSet → Prop
-- 2. 或者，定義一個關係為一個包含有序對的集合：
--    注意：ZFSet 的類型層級比 Type 高，所以我們使用 Type 1
--    或者直接使用類型推斷
--    def relation_as_set : Type 1 := ZFSet  -- 關係是一個集合，其元素是有序對
--    或者：
--    def relation_as_set := ZFSet
def relation_as_set : Type 1 := ZFSet
-- 3. 關係的成員關係：如果 R 是一個關係，a R b 表示 (a, b) ∈ R
def rel_mem (R : ZFSet) (a b : ZFSet) : Prop := ordered_pair a b ∈ R

-- 自反性（Reflexivity）：關係 R 是自反的，當且僅當對於所有 a，有 (a, a) ∈ R
-- 也就是說：對於所有 a，有 rel_mem R a a
--反身性
def reflexive (R : ZFSet) : Prop := ∀ a : ZFSet, rel_mem R a a
--對稱性
def symmetric (R : ZFSet) : Prop := ∀ a b : ZFSet, rel_mem R a b → rel_mem R b a
--傳遞性
def transitive (R : ZFSet) : Prop := ∀ a b c : ZFSet, rel_mem R a b → rel_mem R b c → rel_mem R a c
--等價關係
def equivalence_relation (R : ZFSet) : Prop := reflexive R ∧ symmetric R ∧ transitive R
#check equivalence_relation

def disjoint (A B : ZFSet) : Prop := A ∩ B = ∅

-- Theorem 2.2.1 (a)：對於所有集合 A, B，有 A ⊆ A ∪ B
theorem subset_union_left (A B : ZFSet) : A ⊆ A ∪ B := by
  intro x hx
  -- 只要套用聯集的成員等價式，就能將目標改寫為「x ∈ A 或 x ∈ B」
  have hx_union : x ∈ A ∨ x ∈ B := Or.inl hx
  simpa [ZFSet.mem_union] using hx_union
theorem subset_intersection_left (A B : ZFSet) : A ∩ B ⊆ A := by
  intro x hx
  -- 交集成員同時滿足「在 A 且在 B」
  have x_in_A_and_B : x ∈ A ∧ x ∈ B := by
    simpa [ZFSet.mem_inter] using hx
  exact x_in_A_and_B.left
theorem inter_empty_eq (A : ZFSet) : A ∩ ∅ = ∅ := by
  -- 「集合相等」可轉成「每個元素在左邊 ↔ 在右邊」
  ext x
  constructor
  · intro hx
    -- 使用 `mem_inter` 的等價式把 hx 拆成同時落在 A 與 ∅
    have hx_pair := (ZFSet.mem_inter.mp hx)
    -- 由於交集的第二個條件是 x ∈ ∅，直接回傳即可
    exact hx_pair.right
  · intro hx
    -- x 不可能在空集中；用 `notMem_empty` 得到矛盾，再推出任意命題
    have : False := ZFSet.notMem_empty x hx
    exact this.elim


end ZFC
