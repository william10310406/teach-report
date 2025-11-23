# Lean 4 集合論證明教學

本教學基於 `textbook.lean` 檔案，詳細講解 Lean 4 中集合論證明的語法和技巧。適合大一學生學習形式化數學證明。

---

## 目錄

1. [基礎語法](#基礎語法)
2. [證明策略詳解](#證明策略詳解)
3. [邏輯連接詞的處理](#邏輯連接詞的處理)
4. [集合運算的證明](#集合運算的證明)
   - [前置知識：`.mp` 和 `.mpr` 的基本概念](#前置知識mp-和-mpr-的基本概念)
   - [聯集（`∪`）](#3-聯集)
   - [交集（`∩`）](#4-交集)
   - [綜合範例：分配律（聯集對交集的分配律）](#45-綜合範例分配律聯集對交集的分配律)
   - [綜合範例：分配律（交集對聯集的分配律）](#46-綜合範例分配律交集對聯集的分配律)
   - [綜合範例：冪集合與子集合關係的等價關係](#47-綜合範例冪集合與子集合關係的等價關係)
   - [綜合範例：子集合關係與集合相等的等價關係（聯集版本）](#48-綜合範例子集合關係與集合相等的等價關係聯集版本)
   - [綜合範例：子集合關係與集合相等的等價關係（交集版本）](#49-綜合範例子集合關係與集合相等的等價關係交集版本)
5. [常見證明模式](#常見證明模式)
6. [完整證明範例](#完整證明範例)
7. [常用技巧總結](#常用技巧總結)

---

## 基礎語法

### 1. 定理宣告

```lean
theorem 定理名稱(參數 : 類型) : 要證明的命題 := by
  -- 證明步驟
```

**範例：**
```lean
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- 證明步驟
```

**解釋：**
- `theorem`：宣告一個定理
- `theorem_2_1_1_a`：定理的名稱
- `(A : ZFSet)`：參數 A，類型是 ZFSet（集合）
- `: ∅ ⊆ A`：要證明的命題（空集合合是 A 的子集合）
- `:= by`：開始證明

### 2. 註解

```lean
-- 這是單行註解
-- 可以解釋證明步驟的含義
```

---

## 證明策略詳解

### 1. `intro` - 引入假設

**作用：** 將目標中的 `∀`（全稱量詞）或 `→`（蘊含）的前件引入為假設。

**語法：**
```lean
intro 變數名
```

**範例 1：處理全稱量詞**
```lean
theorem example1 (A : ZFSet) : A ⊆ A := by
  intro x hx  -- 引入 ∀ x, x ∈ A → x ∈ A 中的 x 和 x ∈ A
  exact hx     -- 直接使用假設 hx : x ∈ A
```

**解釋：**
- 目標：`A ⊆ A`，展開為 `∀ x, x ∈ A → x ∈ A`
- `intro x`：引入任意元素 x
- `intro hx`：引入假設 `x ∈ A`
- 新目標：`x ∈ A`
- `exact hx`：直接使用假設完成證明

**範例 2：處理蘊含**
```lean
theorem example2 (A B : ZFSet) : (A ⊆ B) → (A ⊆ B) := by
  intro h  -- 引入前提 A ⊆ B 作為假設 h
  exact h   -- 直接使用假設
```

### 2. `exact` - 直接完成證明

**作用：** 當目標正好等於某個已有的假設或定理時，直接使用它完成證明。

**語法：**
```lean
exact 表達式
```

**範例：**
```lean
theorem example3 (A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx  -- hx 正好是目標 x ∈ A
```

### 3. `have` - 宣告中間步驟

**作用：** 在證明過程中宣告一個中間結果，可以給这个結果命名并在後續使用。

**語法：**
```lean
have 名稱 : 類型 := 證明
```

**範例：**
```lean
theorem example4 (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h
  rcases h with ⟨hAB, hBC⟩
  intro x hxA
  have hxB : x ∈ B := hAB hxA  -- 宣告中間步驟：x ∈ B
  have hxC : x ∈ C := hBC hxB  -- 使用上一步的結果
  exact hxC
```

**解釋：**
- `have hxB : x ∈ B := hAB hxA`：
  - `hxB`：給这个中間結果命名
  - `: x ∈ B`：这个中間結果的類型
  - `:= hAB hxA`：如何證明它（使用 hAB 和 hxA）

### 4. `rcases` - 分解合取/析取

**作用：** 將合取（`∧`）或析取（`∨`）分解成多個假設。

**語法：**
```lean
rcases 假設 with ⟨假設1, 假設2, ...⟩  -- 合取
rcases 假設 with 假設1 | 假設2         -- 析取
```

**範例 1：分解合取**
```lean
theorem example5 (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h  -- h : A ⊆ B ∧ B ⊆ C
  rcases h with ⟨hAB, hBC⟩  -- 分解：hAB : A ⊆ B, hBC : B ⊆ C
  -- 現在可以使用 hAB 和 hBC
```

**範例 2：分解析取**
```lean
theorem example6 (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h
  rcases h with hx | hx  -- 分两种情況：x ∈ A 或 x ∈ B
  · exact Or.inl hx
  · exact Or.inr hx
```

### 5. `constructor` - 分解雙條件

**作用：** 將雙條件 `↔` 分解成兩個方向：`→` 和 `←`。

**語法：**
```lean
constructor
· -- 證明第一個方向
· -- 證明第二个方向
```

**範例：**
```lean
theorem example7 (A B x : ZFSet) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  constructor
  · intro h  -- 方向1：x ∈ A ∩ B → x ∈ A ∧ x ∈ B
    -- 證明步驟
  · intro h  -- 方向2：x ∈ A ∧ x ∈ B → x ∈ A ∩ B
    -- 證明步驟
```

### 6. `apply` - 應用定理

**作用：** 當目標匹配某個定理的结论時，應用该定理，目標变成證明该定理的前提。

**語法：**
```lean
apply 定理名
```

**範例：**
```lean
theorem example8 (A : ZFSet) : A = A := by
  apply ZFSet.ext  -- 應用外延性公理
  -- 目標从 A = A 变成 ∀ x, x ∈ A ↔ x ∈ A
  intro x
  constructor
  · intro hx; exact hx
  · intro hx; exact hx
```

**解釋：**
- `ZFSet.ext` 是外延性公理：`A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`
- `apply ZFSet.ext` 后，目標从 `A = A` 变成 `∀ x, x ∈ A ↔ x ∈ A`

### 7. `rw` / `rewrite` - 重寫

**作用：** 使用等式或等价关系重寫目標或假設。

**語法：**
```lean
rw [等式]           -- 在目標中重寫
rw [等式] at 假設    -- 在假設中重寫
rw [← 等式]         -- 反向重寫（从右到左）
```

**範例：**
```lean
theorem example9 (A B : ZFSet) : A = B → A = B := by
  intro h  -- h : A = B
  rw [h]   -- 將目標中的 A 替换為 B，目標变成 B = B
  rfl      -- 自反性
```

**範例 2：在假設中重寫**
```lean
theorem example10 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h
  rcases h with ⟨hA, hB⟩
  rw [hA] at hB  -- 在 hB 中將 A 替换為 ∅
  -- 現在 hB : ∅ = ∅
```

### 8. `calc` - 鏈式等式

**作用：** 通过一系列等式鏈式證明。

**語法：**
```lean
calc
  表達式1 = 表達式2 := 證明1
  _ = 表達式3 := 證明2
  _ = 表達式4 := 證明3
```

**範例：**
```lean
theorem example11 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h
  rcases h with ⟨hA, hB⟩
  calc
    A = ∅ := hA      -- A = ∅
    _ = B := hB.symm -- ∅ = B（hB.symm 將 B = ∅ 轉換為 ∅ = B）
```

**解釋：**
- `_` 表示上一步的表達式（这里是 `∅`）
- `hB.symm` 是 `hB : B = ∅` 的对称形式：`∅ = B`

### 9. `by_contra` - 反證法

**作用：** 假設结论的否定，推出矛盾。

**語法：**
```lean
by_contra 假設名  -- 假設结论的否定
-- 證明步驟，最终推出矛盾
```

**範例：**
```lean
theorem example12 (A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  by_contra hx_in_A  -- 假設 x ∈ A（要證明 x ∉ A，所以假設其否定）
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A  -- 推出 x ∈ B
  exact hx_notin_B hx_in_B  -- 矛盾：x ∉ B 和 x ∈ B
```

**解釋：**
- 要證明 `x ∉ A`，使用反證法假設 `x ∈ A`
- 从 `x ∈ A` 和 `A ⊆ B` 推出 `x ∈ B`
- 但前提有 `x ∉ B`，矛盾
- 因此 `x ∉ A` 成立

### 10. `cases` - 分情況討論

**作用：** 对析取命題（`∨`）进行分情況討論。

**語法：**
```lean
cases 假設 with
| inl 假設1 => -- 左分支的情況
| inr 假設2 => -- 右分支的情況
```

**範例：**
```lean
theorem example13 (A x : ZFSet) : x ∈ A ∪ ∅ → x ∈ A := by
  intro h  -- h : x ∈ A ∪ ∅
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ ∅
  cases h with
  | inl hx => exact hx        -- 情況1：x ∈ A，直接得到目標
  | inr hx => exact False.elim (ZFSet.notMem_empty x hx)  -- 情況2：x ∈ ∅，矛盾
```

**解釋：**
- `inl`：Left，表示析取的左分支
- `inr`：Right，表示析取的右分支
- 两种情況都要處理

---

## 邏輯連接詞的處理

### 1. 合取（`∧`）- "且"

**構造：** 使用 `⟨證明1, 證明2⟩`
```lean
have h : P ∧ Q := ⟨證明P, 證明Q⟩
```

**分解：** 使用 `rcases` 或 `.left` / `.right`
```lean
rcases h with ⟨hP, hQ⟩
-- 或
have hP : P := h.left
have hQ : Q := h.right
```

**範例：**
```lean
theorem example14 (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h  -- h : x ∈ A ∩ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.left  -- 取出 x ∈ A
```

### 2. 析取（`∨`）- "或"

#### 2.1 構造析取：`Or.inl` 和 `Or.inr`

**類型签名：**
```lean
Or.inl {a b : Prop} (h : a) : a ∨ b  -- 左注入（Left injection）
Or.inr {a b : Prop} (h : b) : a ∨ b  -- 右注入（Right injection）
```

**詳細说明：**

- **`Or.inl`**：將類型為 `a` 的證明注入到 `a ∨ b` 的左分支
  - 如果 `h : a`，則 `Or.inl h : a ∨ b`
  - 表示"選擇左分支"，即"a 成立"

- **`Or.inr`**：將類型為 `b` 的證明注入到 `a ∨ b` 的右分支
  - 如果 `h : b`，則 `Or.inr h : a ∨ b`
  - 表示"選擇右分支"，即"b 成立"

**構造語法：**
```lean
have h : P ∨ Q := Or.inl 證明P  -- 左分支：證明 P，得到 P ∨ Q
have h : P ∨ Q := Or.inr 證明Q  -- 右分支：證明 Q，得到 P ∨ Q
```

**重要理解：**

1. **`Or.inl` 和 `Or.inr` 的選擇取決於目標類型**
   - 如果目標是 `P ∨ Q`，且我们有 `h : P`，則用 `Or.inl h`
   - 如果目標是 `P ∨ Q`，且我们有 `h : Q`，則用 `Or.inr h`

2. **在聯集證明中的應用**
   - `x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ A`，要證明 `x ∈ A ∪ B`，需要構造 `x ∈ A ∨ x ∈ B`
   - 因為 `x ∈ A` 是 `x ∈ A ∨ x ∈ B` 的**左分支**，所以用 `Or.inl hx`
   - 如果 `hx : x ∈ B`，要證明 `x ∈ A ∪ B`，需要構造 `x ∈ A ∨ x ∈ B`
   - 因為 `x ∈ B` 是 `x ∈ A ∨ x ∈ B` 的**右分支**，所以用 `Or.inr hx`

**範例 1：基本用法**
```lean
theorem example15 (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 目標：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ A，這是 x ∈ A ∨ x ∈ B 的左分支
  exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl 選擇左分支
```

**範例 2：使用右分支**
```lean
theorem example15_right (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  -- 目標：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ B，這是 x ∈ A ∨ x ∈ B 的右分支
  exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr 選擇右分支
```

**範例 3：在聯集交换律中的應用**
```lean
theorem example_union_comm (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，這是 x ∈ B ∨ x ∈ A 的右分支
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr（注意：在 B ∨ A 中，A 是右分支）
  | inr hx =>  -- hx : x ∈ B
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，這是 x ∈ B ∨ x ∈ A 的左分支
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl（注意：在 B ∨ A 中，B 是左分支）
```

**關鍵要点：**

- **`Or.inl`** = "Left injection" = 注入到左分支
- **`Or.inr`** = "Right injection" = 注入到右分支
- 選擇哪个取決於**目標析取類型中證明所在的位置**
  - 如果證明在目標類型的**左邊**，用 `Or.inl`
  - 如果證明在目標類型的**右邊**，用 `Or.inr`

**常見錯誤：**

```lean
-- ❌ 錯誤範例
theorem wrong (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  exact ZFSet.mem_union.mpr (Or.inl hx)  -- 錯誤！x ∈ B 是 x ∈ A ∨ x ∈ B 的右分支，应该用 Or.inr

-- ✅ 正確範例
theorem correct (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  exact ZFSet.mem_union.mpr (Or.inr hx)  -- 正確！x ∈ B 是 x ∈ A ∨ x ∈ B 的右分支
```

#### 2.2 分解析取：`cases` 和 `rcases`

**分解語法：**
```lean
cases h with
| inl hP => -- 處理 P 的情況（hP : P）
| inr hQ => -- 處理 Q 的情況（hQ : Q）
```

**範例：**
```lean
theorem example16 (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx => exact Or.inl hx  -- 情況1：hx : x ∈ A，構造 x ∈ A ∨ x ∈ B 的左分支
  | inr hx => exact Or.inr hx  -- 情況2：hx : x ∈ B，構造 x ∈ A ∨ x ∈ B 的右分支
```

### 3. 蘊含（`→`）- "如果...那么"

**引入：** 使用 `intro`
```lean
intro h  -- 引入前提作為假設
```

**應用：** 直接使用函數應用
```lean
have hQ : Q := hP_to_Q hP  -- 如果 hP_to_Q : P → Q，hP : P，則 hQ : Q
```

**範例：**
```lean
theorem example16 (A B x : ZFSet) : A ⊆ B → (x ∈ A → x ∈ B) := by
  intro hAB hxA  -- hAB : A ⊆ B, hxA : x ∈ A
  exact hAB hxA  -- 直接應用 hAB 到 hxA
```

### 4. 雙條件（`↔`）- "當且仅當"

**分解：** 使用 `constructor`
```lean
constructor
· -- 證明 P → Q
· -- 證明 Q → P
```

**範例：**
```lean
theorem example17 (A B x : ZFSet) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  constructor
  · intro h  -- 方向1：x ∈ A ∩ B → x ∈ A ∧ x ∈ B
    exact ZFSet.mem_inter.mp h
  · intro h  -- 方向2：x ∈ A ∧ x ∈ B → x ∈ A ∩ B
    exact ZFSet.mem_inter.mpr h
```

### 5. 否定（`¬`）- "非"

**否定引入：** 使用 `by_contra` 或 `intro`
```lean
by_contra h  -- 假設 P，推出矛盾，从而證明 ¬P
```

**否定消除：** 直接應用
```lean
have : False := h_notP hP  -- 如果 h_notP : ¬P，hP : P，則矛盾
```

**範例：**
```lean
theorem example18 (A x : ZFSet) : x ∉ ∅ := by
  exact ZFSet.notMem_empty x  -- 空集合合沒有元素
```

---

## 集合運算的證明

### 前置知識：`.mp` 和 `.mpr` 的基本概念

在 Lean 中，當有一個等價關係 `P ↔ Q`（雙條件）時，我們可以使用 `.mp` 和 `.mpr` 來提取不同方向的蘊含：

- **`.mp`**：**M**odus **P**onens，從左到右使用等價關係
  - 如果 `h : P ↔ Q`，則 `h.mp : P → Q`
  - 含義：從 `P` 推出 `Q`
  - 用於「分解」：將等價關係的左邊轉換為右邊

- **`.mpr`**：**M**odus **P**onens **R**everse，從右到左使用等價關係
  - 如果 `h : P ↔ Q`，則 `h.mpr : Q → P`
  - 含義：從 `Q` 推出 `P`
  - 用於「構造」：將等價關係的右邊轉換為左邊

**記憶技巧：**
- `.mp` = "正向"（從左到右，Modus Ponens）
- `.mpr` = "反向"（從右到左，Modus Ponens Reverse）

在集合運算中，我們會頻繁使用 `.mp` 和 `.mpr` 來轉換成員關係和邏輯連接詞。

---

### 1. 子集合關係（`⊆`）

**定義：** `A ⊆ B := ∀ x, x ∈ A → x ∈ B`

**證明模式：**
```lean
theorem subset_proof (A B : ZFSet) : A ⊆ B := by
  intro x hx  -- 引入任意 x 和假設 x ∈ A
  -- 證明 x ∈ B
```

**範例：**
```lean
theorem example19 (A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx  -- 直接使用假設
```

### 2. 集合相等（`=`）

**使用外延性公理：**
```lean
apply ZFSet.ext  -- 將 A = B 轉換為 ∀ x, x ∈ A ↔ x ∈ B
intro x
constructor
· -- 證明 x ∈ A → x ∈ B
· -- 證明 x ∈ B → x ∈ A
```

**範例：**
```lean
theorem example20 (A : ZFSet) : A = A := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx; exact hx
  · intro hx; exact hx
```

### 3. 聯集（`∪`）

#### 3.1 基本定義

**成員關係：** `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`

**類型簽名：**
```lean
ZFSet.mem_union : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

ZFSet.mem_union.mp   : x ∈ A ∪ B → x ∈ A ∨ x ∈ B  -- 從聯集成員關係推出析取
ZFSet.mem_union.mpr  : x ∈ A ∨ x ∈ B → x ∈ A ∪ B  -- 從析取推出聯集成員關係
```

**詳細說明：**

`ZFSet.mem_union` 是一個等價關係，表示：
- `x ∈ A ∪ B`（x 是 A 和 B 的聯集的成員）
- 當且僅當
- `x ∈ A ∨ x ∈ B`（x 屬於 A 或 x 屬於 B）

#### 3.2 `ZFSet.mem_union.mpr` 詳解

**作用：** `ZFSet.mem_union.mpr` 將析取（`∨`）轉換為聯集成員關係（`∈ A ∪ B`）。

**使用場景：**

當我們需要證明 `x ∈ A ∪ B` 時，通常的步驟是：

1. **構造析取**：先證明 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ A`，用 `Or.inl hx` 構造 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ B`，用 `Or.inr hx` 構造 `x ∈ A ∨ x ∈ B`

2. **轉換為聯集**：使用 `ZFSet.mem_union.mpr` 將析取轉換為聯集成員關係
   - `ZFSet.mem_union.mpr (Or.inl hx)` 或
   - `ZFSet.mem_union.mpr (Or.inr hx)`

**詳細步驟解析：**

讓我們以 `have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx)` 為例，詳細解釋每一步的轉換過程：

1. **起始點**：`hx : x ∈ A`
   - 我們有一個證明 `hx`，表示 `x` 屬於集合 `A`

2. **構造析取**：`Or.inl hx : x ∈ A ∨ x ∈ B`
   - `Or.inl` 是「左注入」（Left injection），將 `x ∈ A` 注入到析取 `x ∈ A ∨ x ∈ B` 的左分支
   - 結果：我們得到 `x ∈ A ∨ x ∈ B` 的證明

3. **理解等價關係**：`ZFSet.mem_union : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`
   - `ZFSet.mem_union` 是一個等價關係，表示：
     - `x ∈ A ∪ B`（x 是 A 和 B 的聯集的成員）
     - 當且僅當
     - `x ∈ A ∨ x ∈ B`（x 屬於 A 或 x 屬於 B）

4. **提取反向蘊含**：`ZFSet.mem_union.mpr : (x ∈ A ∨ x ∈ B) → x ∈ A ∪ B`
   - `.mpr` 是「反向 Modus Ponens」，從等價關係的右邊推出左邊
   - 類型：`(x ∈ A ∨ x ∈ B) → x ∈ A ∪ B`
   - 含義：如果我們有 `x ∈ A ∨ x ∈ B` 的證明，就可以得到 `x ∈ A ∪ B` 的證明

5. **應用轉換**：`ZFSet.mem_union.mpr (Or.inl hx) : x ∈ A ∪ B`
   - 將 `ZFSet.mem_union.mpr` 應用到 `Or.inl hx`（類型為 `x ∈ A ∨ x ∈ B`）
   - 結果：我們得到 `x ∈ A ∪ B` 的證明

**完整的轉換鏈：**
```
hx : x ∈ A
  ↓
Or.inl hx : x ∈ A ∨ x ∈ B  -- 構造析取（左分支）
  ↓
ZFSet.mem_union.mpr (Or.inl hx) : x ∈ A ∪ B  -- 轉換為聯集成員關係
```

**記憶要點：**
- `Or.inl` / `Or.inr`：構造析取（`∨`）
- `ZFSet.mem_union.mpr`：將析取轉換為聯集成員關係
- 順序：先構造析取，再用 `.mpr` 轉換

**完整範例 1：基本用法（左分支）**
```lean
theorem example21 (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 步驟 1：構造析取 x ∈ A ∨ x ∈ B
  have h_or : x ∈ A ∨ x ∈ B := Or.inl hx  -- 用 Or.inl 選擇左分支
  -- 步驟 2：轉換為聯集成員關係
  exact ZFSet.mem_union.mpr h_or
  -- 或者直接寫成：
  -- exact ZFSet.mem_union.mpr (Or.inl hx)
```

**完整範例 2：基本用法（右分支）**
```lean
theorem example21_right (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  -- 目標：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我們有 hx : x ∈ B，這是 x ∈ A ∨ x ∈ B 的右分支
  -- 所以用 Or.inr hx 構造 x ∈ A ∨ x ∈ B
  exact ZFSet.mem_union.mpr (Or.inr hx)
```

**常見模式：**

```lean
-- 模式 1：x ∈ A → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inl hx)  -- hx : x ∈ A

-- 模式 2：x ∈ B → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inr hx)  -- hx : x ∈ B

-- 模式 3：在分情況討論中使用
cases h with
| inl hx => exact ZFSet.mem_union.mpr (Or.inl hx)  -- 情況1：x ∈ A
| inr hx => exact ZFSet.mem_union.mpr (Or.inr hx)  -- 情況2：x ∈ B
```

#### 3.3 `ZFSet.mem_union.mp` 詳解

**作用：** `ZFSet.mem_union.mp` 將聯集成員關係轉換為析取。

**使用場景：**

當我們有 `h : x ∈ A ∪ B` 時，可以使用 `ZFSet.mem_union.mp` 將其轉換為析取：

```lean
have h_or : x ∈ A ∨ x ∈ B := ZFSet.mem_union.mp h
-- 現在可以使用 cases 進行分情況討論
```

**完整範例：**
```lean
theorem example_union_mp (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h  -- h : x ∈ A ∪ B
  exact ZFSet.mem_union.mp h  -- 轉換為 x ∈ A ∨ x ∈ B
```

#### 3.4 實際應用範例（聯集交換律）

```lean
theorem example_union_comm (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我們有 hx : x ∈ A，這是 x ∈ B ∨ x ∈ A 的右分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ A 是右分支！
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr（右分支）
  | inr hx =>  -- hx : x ∈ B
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我們有 hx : x ∈ B，這是 x ∈ B ∨ x ∈ A 的左分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ B 是左分支！
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl（左分支）
```

**關鍵理解：**

在證明 `x ∈ A ∪ B` 時：
1. 首先理解目標：`x ∈ A ∪ B` 等價於 `x ∈ A ∨ x ∈ B`
2. 確定你有的證明：`hx : x ∈ A` 或 `hx : x ∈ B`
3. 判斷在 `x ∈ A ∨ x ∈ B` 中的位置：
   - 如果 `hx : x ∈ A`，它在**左分支**，用 `Or.inl hx`
   - 如果 `hx : x ∈ B`，它在**右分支**，用 `Or.inr hx`
4. 使用 `ZFSet.mem_union.mpr` 將析取轉換為聯集成員關係

**總結：**
- `ZFSet.mem_union.mpr` 是證明 `x ∈ A ∪ B` 的關鍵工具
- 它需要配合 `Or.inl` 或 `Or.inr` 使用
- 記住：先構造析取，再用 `.mpr` 轉換為聯集成員關係

### 4. 交集（`∩`）

#### 4.1 基本定義

**成員關係：** `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`

**類型簽名：**
```lean
ZFSet.mem_inter : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B

ZFSet.mem_inter.mp   : x ∈ A ∩ B → x ∈ A ∧ x ∈ B  -- 從交集成員關係推出合取
ZFSet.mem_inter.mpr  : x ∈ A ∧ x ∈ B → x ∈ A ∩ B  -- 從合取推出交集成員關係
```

**詳細說明：**

`ZFSet.mem_inter` 是一個等價關係，表示：
- `x ∈ A ∩ B`（x 是 A 和 B 的交集的成員）
- 當且僅當
- `x ∈ A ∧ x ∈ B`（x 屬於 A 且 x 屬於 B）

#### 4.2 `ZFSet.mem_inter.mp` 詳解

**作用：** `ZFSet.mem_inter.mp` 將交集成員關係（`∈ A ∩ B`）轉換為合取（`∧`）。

**使用場景：**

當我們有 `h : x ∈ A ∩ B` 時，可以使用 `ZFSet.mem_inter.mp` 將其分解為合取：

```lean
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
-- 現在可以使用 h_pair.left : x ∈ A 和 h_pair.right : x ∈ B
```

**完整範例 1：從交集推出單個集合的成員關係**
```lean
theorem example22 (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h  -- h : x ∈ A ∩ B
  -- 步驟 1：將交集成員關係轉換為合取
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  -- 步驟 2：從合取中取出左部分
  exact h_pair.left  -- h_pair.left : x ∈ A
```

**完整範例 2：從交集推出右邊集合的成員關係**
```lean
theorem example_inter_right (A B x : ZFSet) : x ∈ A ∩ B → x ∈ B := by
  intro h  -- h : x ∈ A ∩ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.right  -- h_pair.right : x ∈ B
```

#### 4.3 `ZFSet.mem_inter.mpr` 詳解

**作用：** `ZFSet.mem_inter.mpr` 將合取（`∧`）轉換為交集成員關係（`∈ A ∩ B`）。

**使用場景：**

當我們需要證明 `x ∈ A ∩ B` 時，通常的步驟是：

1. **證明合取**：先證明 `x ∈ A ∧ x ∈ B`
   - 如果 `hxA : x ∈ A` 且 `hxB : x ∈ B`，用 `⟨hxA, hxB⟩` 構造 `x ∈ A ∧ x ∈ B`

2. **轉換為交集**：使用 `ZFSet.mem_inter.mpr` 將合取轉換為交集成員關係
   - `ZFSet.mem_inter.mpr ⟨hxA, hxB⟩`

**完整範例 3：從兩個成員關係推出交集**
```lean
theorem example_inter_mpr (A B x : ZFSet) : (x ∈ A ∧ x ∈ B) → x ∈ A ∩ B := by
  intro h  -- h : x ∈ A ∧ x ∈ B
  -- 直接使用 .mpr 轉換為交集成員關係
  exact ZFSet.mem_inter.mpr h
```

**完整範例 4：從兩個獨立的假設構造交集**
```lean
theorem example_inter_construct (A B x : ZFSet) : (x ∈ A) → (x ∈ B) → x ∈ A ∩ B := by
  intro hxA hxB  -- hxA : x ∈ A, hxB : x ∈ B
  -- 步驟 1：構造合取 x ∈ A ∧ x ∈ B
  have h_pair : x ∈ A ∧ x ∈ B := ⟨hxA, hxB⟩
  -- 步驟 2：轉換為交集成員關係
  exact ZFSet.mem_inter.mpr h_pair
  -- 或者直接寫成：
  -- exact ZFSet.mem_inter.mpr ⟨hxA, hxB⟩
```

**常見模式：**

```lean
-- 模式 1：從交集分解出左邊
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
exact h_pair.left  -- 得到 x ∈ A

-- 模式 2：從交集分解出右邊
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
exact h_pair.right  -- 得到 x ∈ B

-- 模式 3：從兩個成員關係構造交集
exact ZFSet.mem_inter.mpr ⟨hxA, hxB⟩  -- hxA : x ∈ A, hxB : x ∈ B

-- 模式 4：在證明中使用
have h_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨hxA, hxB⟩
```

#### 4.4 實際應用範例（交集交換律）

```lean
theorem thm_2_2_1_j (A B x : ZFSet) : x ∈ A ∩ B → x ∈ B ∩ A := by
  intro h  -- h : x ∈ A ∩ B
  -- 步驟 1：將 x ∈ A ∩ B 轉換為 x ∈ A ∧ x ∈ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  -- 步驟 2：交換順序，構造 x ∈ B ∧ x ∈ A
  have h_pair_swap : x ∈ B ∧ x ∈ A := ⟨h_pair.right, h_pair.left⟩
  -- 步驟 3：轉換為 x ∈ B ∩ A
  exact ZFSet.mem_inter.mpr h_pair_swap
  -- 或者更簡潔地寫成：
  -- exact ZFSet.mem_inter.mpr ⟨(ZFSet.mem_inter.mp h).right, (ZFSet.mem_inter.mp h).left⟩
```

**關鍵理解：**

1. **`.mp` 用於"分解"**：當我們有交集成員關係（`x ∈ A ∩ B`）時，用 `.mp` 轉換為合取（`x ∈ A ∧ x ∈ B`），然後可以使用 `.left` 或 `.right` 提取單個成員關係

2. **`.mpr` 用於"構造"**：當我們有合取（`x ∈ A ∧ x ∈ B`）時，用 `.mpr` 轉換為交集成員關係（`x ∈ A ∩ B`）

3. **配合合取構造使用**：
   - 構造合取：`⟨hxA, hxB⟩`（其中 `hxA : x ∈ A`，`hxB : x ∈ B`）
   - 轉換為交集：`ZFSet.mem_inter.mpr ⟨hxA, hxB⟩`

4. **與聯集的對比**：
   - 聯集使用析取（`∨`）和 `Or.inl`/`Or.inr`
   - 交集使用合取（`∧`）和 `⟨...⟩` 構造

**總結：**
- `ZFSet.mem_inter.mp` 用於分解交集成員關係，提取單個集合的成員關係
- `ZFSet.mem_inter.mpr` 用於構造交集成員關係，需要同時證明元素屬於兩個集合
- 記住：交集需要兩個條件都成立（合取），而聯集只需要一個條件成立（析取）

#### 4.5 綜合範例：分配律（聯集對交集的分配律）

**定理：** `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`

這是一個重要的集合運算性質，展示了如何同時處理聯集和交集。這個證明結合了多種技巧，包括：
- 聯集和交集的轉換
- 嵌套的分情況討論（`cases`）
- 析取和合取的構造與分解

**完整證明：**

```lean
theorem theorem_2_2_1_n (A B C : ZFSet) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply ZFSet.ext -- 根據外延性公設，轉換為 ∀ x, x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_union -- hx_union: x ∈ A ∪ (B ∩ C)
    -- 方向1：x ∈ A ∪ (B ∩ C) → x ∈ (A ∪ B) ∩ (A ∪ C)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ (B ∩ C) 拆成 x ∈ A ∨ x ∈ B ∩ C
    cases hx_union with
    | inl hx => -- 情況1：hx : x ∈ A
      have h1 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx) -- x ∈ A, so x ∈ A ∪ B
      have h2 : x ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inl hx) -- x ∈ A, so x ∈ A ∪ C
      exact ZFSet.mem_inter.mpr ⟨h1, h2⟩ -- x ∈ A ∪ B ∧ x ∈ A ∪ C, so x ∈ (A ∪ B) ∩ (A ∪ C)
    | inr hx => -- 情況2：hx : x ∈ B ∩ C
      have h1_pair : x ∈ B ∧ x ∈ C := ZFSet.mem_inter.mp hx -- 將 x ∈ B ∩ C 拆成 x ∈ B ∧ x ∈ C
      have h2 : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inr h1_pair.left) -- x ∈ B, so x ∈ A ∪ B
      have h3 : x ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inr h1_pair.right) -- x ∈ C, so x ∈ A ∪ C
      exact ZFSet.mem_inter.mpr ⟨h2, h3⟩ -- x ∈ A ∪ B ∧ x ∈ A ∪ C, so x ∈ (A ∪ B) ∩ (A ∪ C)
  · intro hx_inter -- hx_inter: x ∈ (A ∪ B) ∩ (A ∪ C)
    -- 方向2：x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ (B ∩ C)
    have h1 : x ∈ A ∪ B ∧ x ∈ A ∪ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ (A ∪ B) ∩ (A ∪ C) 拆成 x ∈ A ∪ B ∧ x ∈ A ∪ C
    have h2 : x ∈ A ∨ x ∈ B := ZFSet.mem_union.mp h1.left -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
    have h3 : x ∈ A ∨ x ∈ C := ZFSet.mem_union.mp h1.right -- 將 x ∈ A ∪ C 拆成 x ∈ A ∨ x ∈ C
    -- 目標：證明 x ∈ A ∪ (B ∩ C)，即 x ∈ A ∨ x ∈ B ∩ C
    -- 我們有 h2 : x ∈ A ∨ x ∈ B 和 h3 : x ∈ A ∨ x ∈ C
    -- 需要分情況討論：如果 x ∈ A，直接得到目標；如果 x ∈ B，需要看 x ∈ C 的情況
    cases h2 with
    | inl hx_A => exact ZFSet.mem_union.mpr (Or.inl hx_A) -- 情況1：x ∈ A，直接得到 x ∈ A ∪ (B ∩ C)
    | inr hx_B => -- 情況2：x ∈ B（h2 的右分支），此時需要看 h3 的情況
      cases h3 with
      | inl hx_A2 => exact ZFSet.mem_union.mpr (Or.inl hx_A2) -- 子情況2.1：x ∈ A，直接得到 x ∈ A ∪ (B ∩ C)
      | inr hx_C => -- 子情況2.2：x ∈ C（h3 的右分支），此時 x ∈ B 且 x ∈ C
        have h4 : x ∈ B ∩ C := ZFSet.mem_inter.mpr ⟨hx_B, hx_C⟩ -- x ∈ B ∧ x ∈ C，所以 x ∈ B ∩ C
        exact ZFSet.mem_union.mpr (Or.inr h4) -- x ∈ B ∩ C，所以 x ∈ A ∪ (B ∩ C)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ A ∪ (B ∩ C) → x ∈ (A ∪ B) ∩ (A ∪ C)`

**目標：** 證明如果 `x ∈ A ∪ (B ∩ C)`，則 `x ∈ (A ∪ B) ∩ (A ∪ C)`

**步驟 1：分解聯集**
- `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ A ∪ (B ∩ C)` 轉換為 `x ∈ A ∨ x ∈ B ∩ C`
- 現在需要分兩種情況討論

**情況 1：`x ∈ A`**
- 如果 `x ∈ A`，則：
  - `x ∈ A ∪ B`（因為 `x ∈ A`，用 `Or.inl` 構造）
  - `x ∈ A ∪ C`（因為 `x ∈ A`，用 `Or.inl` 構造）
- 因此 `x ∈ (A ∪ B) ∩ (A ∪ C)`（用 `ZFSet.mem_inter.mpr` 構造）

**情況 2：`x ∈ B ∩ C`**
- 如果 `x ∈ B ∩ C`，則：
  - 用 `ZFSet.mem_inter.mp` 分解得到 `x ∈ B ∧ x ∈ C`
  - `x ∈ A ∪ B`（因為 `x ∈ B`，用 `Or.inr` 構造）
  - `x ∈ A ∪ C`（因為 `x ∈ C`，用 `Or.inr` 構造）
- 因此 `x ∈ (A ∪ B) ∩ (A ∪ C)`（用 `ZFSet.mem_inter.mpr` 構造）

**關鍵理解：**
- 聯集只需要一個條件成立（`x ∈ A` 或 `x ∈ B ∩ C`）
- 交集需要兩個條件都成立（`x ∈ A ∪ B` 且 `x ∈ A ∪ C`）
- 無論哪種情況，都能證明 `x ∈ (A ∪ B) ∩ (A ∪ C)`

#### 第二個方向：`x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ (B ∩ C)`

**目標：** 證明如果 `x ∈ (A ∪ B) ∩ (A ∪ C)`，則 `x ∈ A ∪ (B ∩ C)`

**步驟 1：分解交集**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ (A ∪ B) ∩ (A ∪ C)` 轉換為 `x ∈ A ∪ B ∧ x ∈ A ∪ C`
- 現在有兩個條件：`x ∈ A ∪ B` 和 `x ∈ A ∪ C`

**步驟 2：分解兩個聯集**
- `ZFSet.mem_union.mp h1.left`：將 `x ∈ A ∪ B` 轉換為 `x ∈ A ∨ x ∈ B`
- `ZFSet.mem_union.mp h1.right`：將 `x ∈ A ∪ C` 轉換為 `x ∈ A ∨ x ∈ C`

**步驟 3：嵌套的分情況討論**

這是這個證明的關鍵部分！我們需要同時考慮兩個析取的所有可能組合：

**第一層分情況（基於 `h2 : x ∈ A ∨ x ∈ B`）：**

- **情況 1：`x ∈ A`**
  - 如果 `x ∈ A`，則直接得到 `x ∈ A ∪ (B ∩ C)`（用 `Or.inl` 選擇左分支）
  - 不需要看 `h3` 的情況，因為已經滿足目標

- **情況 2：`x ∈ B`**
  - 如果 `x ∈ B`，還需要看 `h3 : x ∈ A ∨ x ∈ C` 的情況
  - 進入第二層分情況討論

**第二層分情況（基於 `h3 : x ∈ A ∨ x ∈ C`，在 `x ∈ B` 的前提下）：**

- **子情況 2.1：`x ∈ A`**
  - 如果 `x ∈ A`，則直接得到 `x ∈ A ∪ (B ∩ C)`（用 `Or.inl` 選擇左分支）

- **子情況 2.2：`x ∈ C`**
  - 如果 `x ∈ C`，此時我們有：
    - `x ∈ B`（從第一層的情況 2）
    - `x ∈ C`（從第二層的子情況 2.2）
  - 因此 `x ∈ B ∧ x ∈ C`，用 `ZFSet.mem_inter.mpr` 構造 `x ∈ B ∩ C`
  - 最後用 `ZFSet.mem_union.mpr (Or.inr h4)` 得到 `x ∈ A ∪ (B ∩ C)`

**為什麼需要嵌套的 `cases`？**

因為我們需要考慮所有可能的組合：
- `x ∈ A` 或 `x ∈ B`（從 `h2`）
- `x ∈ A` 或 `x ∈ C`（從 `h3`）

總共有 4 種可能的組合：
1. `x ∈ A` 且 `x ∈ A` → `x ∈ A` → 目標成立
2. `x ∈ A` 且 `x ∈ C` → `x ∈ A` → 目標成立
3. `x ∈ B` 且 `x ∈ A` → `x ∈ A` → 目標成立
4. `x ∈ B` 且 `x ∈ C` → `x ∈ B ∩ C` → 目標成立

但實際上，如果 `x ∈ A`，無論 `h3` 的情況如何，目標都成立。所以我們可以簡化：
- 如果 `x ∈ A`，直接完成
- 如果 `x ∈ B`，再看 `x ∈ C` 的情況

**關鍵技巧總結：**

1. **聯集和交集的轉換**：
   - 聯集 ↔ 析取：`ZFSet.mem_union.mp` / `ZFSet.mem_union.mpr`
   - 交集 ↔ 合取：`ZFSet.mem_inter.mp` / `ZFSet.mem_inter.mpr`

2. **嵌套的分情況討論**：
   - 當有多個析取需要同時考慮時，使用嵌套的 `cases`
   - 如果某個情況已經滿足目標，可以直接完成，不需要繼續分情況

3. **邏輯推理**：
   - 聯集：只需要一個條件成立
   - 交集：需要兩個條件都成立
   - 分配律：聯集對交集的分配，展示了兩種運算的交互

**記憶要點：**
- 分配律 `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)` 展示了聯集如何「分配」到交集中
- 證明時需要同時處理聯集和交集，使用對應的轉換方法
- 嵌套的 `cases` 用於處理多個析取的組合情況

#### 4.6 綜合範例：分配律（交集對聯集的分配律）

**定理：** `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`

這是另一個重要的分配律，與前面的分配律相對應。這個證明展示了如何處理交集和聯集的組合，以及如何從交集中提取信息並構造聯集。

**完整證明：**

```lean
theorem theorem_2_2_1_m (A B C : ZFSet) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ZFSet.ext -- 根據外延性公設，轉換為 ∀ x, x ∈ A ∩ (B ∪ C) ↔ x ∈ (A ∩ B) ∪ (A ∩ C)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ A ∩ (B ∪ C)
    -- 方向1：x ∈ A ∩ (B ∪ C) → x ∈ (A ∩ B) ∪ (A ∩ C)
    have h1 : x ∈ A ∧ x ∈ B ∪ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ (B ∪ C) 拆成 x ∈ A ∧ x ∈ B ∪ C
    have h2_pair : x ∈ B ∨ x ∈ C := ZFSet.mem_union.mp h1.right -- 將 x ∈ B ∪ C 拆成 x ∈ B ∨ x ∈ C
    cases h2_pair with
    | inl hx_B => -- 情況1：hx_B : x ∈ B
      have h3 : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨h1.left, hx_B⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
      exact ZFSet.mem_union.mpr (Or.inl h3) -- x ∈ A ∩ B, so x ∈ (A ∩ B) ∪ (A ∩ C)（用 Or.inl 選擇左分支）
    | inr hx_C => -- 情況2：hx_C : x ∈ C
      have h3 : x ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨h1.left, hx_C⟩ -- x ∈ A ∧ x ∈ C, so x ∈ A ∩ C
      exact ZFSet.mem_union.mpr (Or.inr h3) -- x ∈ A ∩ C, so x ∈ (A ∩ B) ∪ (A ∩ C)（用 Or.inr 選擇右分支）
  · intro hx_union -- hx_union : x ∈ (A ∩ B) ∪ (A ∩ C)
    -- 方向2：x ∈ (A ∩ B) ∪ (A ∩ C) → x ∈ A ∩ (B ∪ C)
    have h1 : x ∈ A ∩ B ∨ x ∈ A ∩ C := ZFSet.mem_union.mp hx_union -- 將 x ∈ (A ∩ B) ∪ (A ∩ C) 拆成 x ∈ A ∩ B ∨ x ∈ A ∩ C
    cases h1 with
    | inl hx_B => -- 情況1：hx_B : x ∈ A ∩ B
      have h2 : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_B -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      have h3 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inl h2.right) -- x ∈ B, so x ∈ B ∪ C（用 Or.inl 選擇左分支）
      exact ZFSet.mem_inter.mpr ⟨h2.left, h3⟩ -- x ∈ A ∧ x ∈ B ∪ C, so x ∈ A ∩ (B ∪ C)
    | inr hx_C => -- 情況2：hx_C : x ∈ A ∩ C
      have h2 : x ∈ A ∧ x ∈ C := ZFSet.mem_inter.mp hx_C -- 將 x ∈ A ∩ C 拆成 x ∈ A ∧ x ∈ C
      have h3 : x ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inr h2.right) -- x ∈ C, so x ∈ B ∪ C（用 Or.inr 選擇右分支）
      exact ZFSet.mem_inter.mpr ⟨h2.left, h3⟩ -- x ∈ A ∧ x ∈ B ∪ C, so x ∈ A ∩ (B ∪ C)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ A ∩ (B ∪ C) → x ∈ (A ∩ B) ∪ (A ∩ C)`

**目標：** 證明如果 `x ∈ A ∩ (B ∪ C)`，則 `x ∈ (A ∩ B) ∪ (A ∩ C)`

**步驟 1：分解交集**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ A ∩ (B ∪ C)` 轉換為 `x ∈ A ∧ x ∈ B ∪ C`
- 現在我們有：`x ∈ A` 和 `x ∈ B ∪ C`

**步驟 2：分解聯集**
- `ZFSet.mem_union.mp h1.right`：將 `x ∈ B ∪ C` 轉換為 `x ∈ B ∨ x ∈ C`
- 現在需要分兩種情況討論

**情況 1：`x ∈ B`**
- 如果 `x ∈ B`，則：
  - 我們有 `x ∈ A`（從 `h1.left`）
  - 我們有 `x ∈ B`（從情況假設）
  - 因此 `x ∈ A ∩ B`（用 `ZFSet.mem_inter.mpr` 構造）
  - 因此 `x ∈ (A ∩ B) ∪ (A ∩ C)`（用 `Or.inl` 選擇左分支）

**情況 2：`x ∈ C`**
- 如果 `x ∈ C`，則：
  - 我們有 `x ∈ A`（從 `h1.left`）
  - 我們有 `x ∈ C`（從情況假設）
  - 因此 `x ∈ A ∩ C`（用 `ZFSet.mem_inter.mpr` 構造）
  - 因此 `x ∈ (A ∩ B) ∪ (A ∩ C)`（用 `Or.inr` 選擇右分支）

**關鍵理解：**
- 交集需要兩個條件都成立：`x ∈ A` 且 `x ∈ B ∪ C`
- 聯集只需要一個條件成立：`x ∈ A ∩ B` 或 `x ∈ A ∩ C`
- 無論 `x ∈ B` 還是 `x ∈ C`，都能證明 `x ∈ (A ∩ B) ∪ (A ∩ C)`

#### 第二個方向：`x ∈ (A ∩ B) ∪ (A ∩ C) → x ∈ A ∩ (B ∪ C)`

**目標：** 證明如果 `x ∈ (A ∩ B) ∪ (A ∩ C)`，則 `x ∈ A ∩ (B ∪ C)`

**步驟 1：分解聯集**
- `ZFSet.mem_union.mp hx_union`：將 `x ∈ (A ∩ B) ∪ (A ∩ C)` 轉換為 `x ∈ A ∩ B ∨ x ∈ A ∩ C`
- 現在需要分兩種情況討論

**情況 1：`x ∈ A ∩ B`**
- 如果 `x ∈ A ∩ B`，則：
  - 用 `ZFSet.mem_inter.mp` 分解得到 `x ∈ A ∧ x ∈ B`
  - `x ∈ B`，所以 `x ∈ B ∪ C`（用 `Or.inl` 構造）
  - `x ∈ A` 且 `x ∈ B ∪ C`，因此 `x ∈ A ∩ (B ∪ C)`（用 `ZFSet.mem_inter.mpr` 構造）

**情況 2：`x ∈ A ∩ C`**
- 如果 `x ∈ A ∩ C`，則：
  - 用 `ZFSet.mem_inter.mp` 分解得到 `x ∈ A ∧ x ∈ C`
  - `x ∈ C`，所以 `x ∈ B ∪ C`（用 `Or.inr` 構造）
  - `x ∈ A` 且 `x ∈ B ∪ C`，因此 `x ∈ A ∩ (B ∪ C)`（用 `ZFSet.mem_inter.mpr` 構造）

**關鍵理解：**
- 聯集只需要一個條件成立：`x ∈ A ∩ B` 或 `x ∈ A ∩ C`
- 交集需要兩個條件都成立：`x ∈ A` 且 `x ∈ B ∪ C`
- 無論哪種情況，都能提取出 `x ∈ A`，並證明 `x ∈ B ∪ C`

**與前一個分配律的對比：**

| 分配律 | 形式 | 關鍵差異 |
|--------|------|----------|
| 聯集對交集 | `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)` | 需要嵌套的 `cases`（兩個析取） |
| 交集對聯集 | `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)` | 只需要一層 `cases`（一個析取） |

**為什麼這個證明更簡單？**

1. **第一個方向**：
   - 從 `x ∈ A ∩ (B ∪ C)` 開始
   - 分解交集得到 `x ∈ A` 和 `x ∈ B ∪ C`
   - 分解聯集得到 `x ∈ B ∨ x ∈ C`
   - 只需要一層分情況討論

2. **第二個方向**：
   - 從 `x ∈ (A ∩ B) ∪ (A ∩ C)` 開始
   - 分解聯集得到 `x ∈ A ∩ B ∨ x ∈ A ∩ C`
   - 只需要一層分情況討論
   - 每種情況都能直接提取 `x ∈ A`

**關鍵技巧總結：**

1. **交集的分解**：
   - 使用 `ZFSet.mem_inter.mp` 將 `x ∈ A ∩ B` 轉換為 `x ∈ A ∧ x ∈ B`
   - 然後可以使用 `.left` 和 `.right` 提取單個成員關係

2. **聯集的構造**：
   - 使用 `ZFSet.mem_union.mpr` 將 `x ∈ A ∨ x ∈ B` 轉換為 `x ∈ A ∪ B`
   - 需要配合 `Or.inl` 或 `Or.inr` 使用

3. **分情況討論的簡化**：
   - 如果某個情況已經滿足目標，可以直接完成
   - 不需要考慮所有可能的組合

**記憶要點：**
- 分配律 `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)` 展示了交集如何「分配」到聯集中
- 這個證明比聯集對交集的分配律更簡單，因為只需要一層分情況討論
- 關鍵是理解如何從交集中提取信息，並構造聯集

#### 4.7 綜合範例：冪集合與子集合關係的等價關係

**定理：** `A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)`

這是一個非常重要的定理，它建立了子集合關係和冪集合之間的等價關係。這個證明展示了：
- 如何使用冪集合的成員關係
- 如何利用子集合關係的傳遞性
- 如何構造冪集合的成員

**完整證明：**

```lean
theorem theorem_2_1_5(A B : ZFSet) : A ⊆ B ↔ ZFSet.powerset A ⊆ ZFSet.powerset B := by
  constructor
  -- 方向 1：A ⊆ B → 𝒫(A) ⊆ 𝒫(B)
  · intro h x hx -- h : A ⊆ B, hx : x ∈ 𝒫(A)，即 x ∈ ZFSet.powerset A
    -- 要證明 x ∈ 𝒫(B)，即 x ∈ ZFSet.powerset B，需要證明 x ⊆ B
    -- 首先，從 x ∈ 𝒫(A) 推出 x ⊆ A
    have hx_subset_A : x ⊆ A := ZFSet.mem_powerset.mp hx
    -- 由於 x ⊆ A 且 A ⊆ B，所以 x ⊆ B
    have hx_subset_B : x ⊆ B := fun y hy => h (hx_subset_A hy)
    -- 因此 x ∈ 𝒫(B)
    exact ZFSet.mem_powerset.mpr hx_subset_B
  -- 方向 2：𝒫(A) ⊆ 𝒫(B) → A ⊆ B
  · intro h x hx -- h : 𝒫(A) ⊆ 𝒫(B), hx : x ∈ A
    -- 要證明 x ∈ B
    -- 首先，注意到 A 本身是 A 的子集合，所以 A ∈ 𝒫(A)
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun y hy => hy)
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := h hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B
    -- 由於 x ∈ A 且 A ⊆ B，所以 x ∈ B
    exact hA_subset_B hx
```

**詳細步驟解析：**

#### 第一個方向：`A ⊆ B → 𝒫(A) ⊆ 𝒫(B)`

**目標：** 證明如果 `A ⊆ B`，則 `𝒫(A) ⊆ 𝒫(B)`

**步驟 1：引入假設**
- `intro h x hx`：引入 `A ⊆ B` 和 `x ∈ 𝒫(A)`
- 目標：證明 `x ∈ 𝒫(B)`，即 `x ⊆ B`

**步驟 2：從冪集合提取子集合關係**
- `ZFSet.mem_powerset.mp hx`：將 `x ∈ 𝒫(A)` 轉換為 `x ⊆ A`
- 現在我們有：`x ⊆ A` 和 `A ⊆ B`

**步驟 3：利用傳遞性**
- 因為 `x ⊆ A` 且 `A ⊆ B`，所以 `x ⊆ B`
- 使用函數構造：`fun y hy => h (hx_subset_A hy)`
  - 對於任意 `y ∈ x`，因為 `x ⊆ A`，所以 `y ∈ A`
  - 因為 `A ⊆ B`，所以 `y ∈ B`
  - 因此 `x ⊆ B`

**步驟 4：構造冪集合成員關係**
- `ZFSet.mem_powerset.mpr hx_subset_B`：將 `x ⊆ B` 轉換為 `x ∈ 𝒫(B)`

**關鍵理解：**
- 如果 `A ⊆ B`，則 `A` 的所有子集合都是 `B` 的子集合
- 因此 `𝒫(A)` 的所有元素都在 `𝒫(B)` 中
- 所以 `𝒫(A) ⊆ 𝒫(B)`

#### 第二個方向：`𝒫(A) ⊆ 𝒫(B) → A ⊆ B`

**目標：** 證明如果 `𝒫(A) ⊆ 𝒫(B)`，則 `A ⊆ B`

**步驟 1：引入假設**
- `intro h x hx`：引入 `𝒫(A) ⊆ 𝒫(B)` 和 `x ∈ A`
- 目標：證明 `x ∈ B`

**步驟 2：利用 `A` 本身**
- `A` 是 `A` 的子集合（自反性），所以 `A ∈ 𝒫(A)`
- 使用 `ZFSet.mem_powerset.mpr (fun y hy => hy)` 構造
  - `fun y hy => hy` 表示：對於任意 `y ∈ A`，有 `y ∈ A`（自反性）

**步驟 3：應用子集合關係**
- 因為 `𝒫(A) ⊆ 𝒫(B)` 且 `A ∈ 𝒫(A)`，所以 `A ∈ 𝒫(B)`
- 使用 `h hA_in_powerset_A` 得到 `A ∈ 𝒫(B)`

**步驟 4：從冪集合提取子集合關係**
- `ZFSet.mem_powerset.mp hA_in_powerset_B`：將 `A ∈ 𝒫(B)` 轉換為 `A ⊆ B`

**步驟 5：應用子集合關係**
- 因為 `x ∈ A` 且 `A ⊆ B`，所以 `x ∈ B`
- 使用 `hA_subset_B hx` 完成證明

**關鍵理解：**
- 如果 `𝒫(A) ⊆ 𝒫(B)`，則 `A` 本身（作為 `A` 的子集合）必須在 `𝒫(B)` 中
- 因此 `A ⊆ B`
- 這展示了如何利用集合本身來證明子集合關係

**為什麼這個定理很重要？**

1. **建立等價關係**：它告訴我們，`A ⊆ B` 和 `𝒫(A) ⊆ 𝒫(B)` 是等價的
   - 這意味著我們可以用冪集合來描述子集合關係
   - 也可以用子集合關係來描述冪集合的包含關係

2. **實際應用**：
   - 當我們需要證明 `A ⊆ B` 時，可以改為證明 `𝒫(A) ⊆ 𝒫(B)`
   - 當我們需要證明 `𝒫(A) ⊆ 𝒫(B)` 時，可以改為證明 `A ⊆ B`

3. **直觀理解**：
   - `A ⊆ B` 意味著 `A` 的所有元素都在 `B` 中
   - `𝒫(A) ⊆ 𝒫(B)` 意味著 `A` 的所有子集合都是 `B` 的子集合
   - 這兩個描述在本質上是相同的

**關鍵技巧總結：**

1. **冪集合的轉換**：
   - `ZFSet.mem_powerset.mp`：將 `x ∈ 𝒫(A)` 轉換為 `x ⊆ A`
   - `ZFSet.mem_powerset.mpr`：將 `x ⊆ A` 轉換為 `x ∈ 𝒫(A)`

2. **子集合關係的傳遞性**：
   - 如果 `x ⊆ A` 且 `A ⊆ B`，則 `x ⊆ B`
   - 使用函數構造：`fun y hy => h (hx_subset_A hy)`

3. **利用集合本身**：
   - `A` 是 `A` 的子集合（自反性）
   - 因此 `A ∈ 𝒫(A)`
   - 這是證明第二個方向的關鍵

**記憶要點：**
- `A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)` 建立了子集合關係和冪集合包含關係的等價關係
- 證明時需要分別證明兩個方向
- 第一個方向使用傳遞性
- 第二個方向利用集合本身（`A ∈ 𝒫(A)`）

#### 4.8 綜合範例：子集合關係與集合相等的等價關係（聯集版本）

**定理：** `A ⊆ B ↔ A ∪ B = B`

這是一個非常重要的定理，它建立了子集合關係和集合相等之間的等價關係。這個證明展示了：
- 如何證明雙條件（`↔`）
- 如何使用外延性公理證明集合相等
- 如何使用等式重寫（`rw`）
- 如何結合子集合關係和聯集運算

**完整證明：**

```lean
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
```

**詳細步驟解析：**

#### 第一個方向：`A ⊆ B → A ∪ B = B`

**目標：** 證明如果 `A ⊆ B`，則 `A ∪ B = B`

**步驟 1：使用外延性公理**
- `apply ZFSet.ext`：將 `A ∪ B = B` 轉換為 `∀ x, x ∈ A ∪ B ↔ x ∈ B`
- 現在需要證明：對於任意 `x`，`x ∈ A ∪ B` 當且僅當 `x ∈ B`

**步驟 2：證明雙條件 `x ∈ A ∪ B ↔ x ∈ B`**

**方向 1.1：`x ∈ A ∪ B → x ∈ B`**
- 分解 `x ∈ A ∪ B` 得到 `x ∈ A ∨ x ∈ B`
- 分情況討論：
  - **情況 1：`x ∈ A`**
    - 因為 `A ⊆ B`（從假設 `hAB`），所以 `x ∈ B`
    - 使用 `hAB hx_A` 直接得到 `x ∈ B`
  - **情況 2：`x ∈ B`**
    - 直接成立，使用 `hx_B`

**方向 1.2：`x ∈ B → x ∈ A ∪ B`**
- 如果 `x ∈ B`，則 `x ∈ A ∪ B`（因為 `x ∈ B` 是 `x ∈ A ∨ x ∈ B` 的右分支）
- 使用 `ZFSet.mem_union.mpr (Or.inr hx_B)` 構造

**關鍵理解：**
- 如果 `A ⊆ B`，則 `A` 的所有元素都在 `B` 中
- 因此 `A ∪ B` 的所有元素都在 `B` 中（因為 `A` 的元素在 `B` 中，`B` 的元素也在 `B` 中）
- 同時，`B` 的所有元素都在 `A ∪ B` 中
- 所以 `A ∪ B = B`

#### 第二個方向：`A ∪ B = B → A ⊆ B`

**目標：** 證明如果 `A ∪ B = B`，則 `A ⊆ B`

**步驟 1：引入假設**
- `intro h_eq x hx_A`：引入 `A ∪ B = B` 和 `x ∈ A`
- 目標：證明 `x ∈ B`

**步驟 2：利用等式**
- 因為 `x ∈ A`，所以 `x ∈ A ∪ B`（用 `Or.inl` 構造）
- 因為 `A ∪ B = B`，所以 `x ∈ B`（用 `rw [h_eq]` 重寫）

**關鍵理解：**
- 如果 `A ∪ B = B`，則 `A` 的所有元素都在 `A ∪ B` 中
- 因為 `A ∪ B = B`，所以 `A` 的所有元素都在 `B` 中
- 因此 `A ⊆ B`

**為什麼這個定理很重要？**

1. **建立等價關係**：它告訴我們，`A ⊆ B` 和 `A ∪ B = B` 是等價的
   - 這意味著我們可以用集合相等來描述子集合關係
   - 也可以用子集合關係來描述集合相等

2. **實際應用**：
   - 當我們需要證明 `A ⊆ B` 時，可以改為證明 `A ∪ B = B`
   - 當我們需要證明 `A ∪ B = B` 時，可以改為證明 `A ⊆ B`

3. **直觀理解**：
   - `A ⊆ B` 意味著 `A` 的所有元素都在 `B` 中
   - `A ∪ B = B` 意味著 `A` 和 `B` 的聯集就是 `B` 本身
   - 這兩個描述在本質上是相同的

**關鍵技巧總結：**

1. **外延性公理的使用**：
   - 證明集合相等時，使用 `apply ZFSet.ext`
   - 轉換為證明所有元素的成員關係等價

2. **等式重寫（`rw`）**：
   - `rw [h_eq] at h1`：在假設 `h1` 中將等式的一邊重寫為另一邊
   - 這是利用等式的重要方法

3. **子集合關係的應用**：
   - `hAB : A ⊆ B` 是一個函數，可以應用到 `x ∈ A` 得到 `x ∈ B`
   - 直接使用 `hAB hx_A` 即可

4. **聯集的構造**：
   - 如果 `x ∈ A`，用 `Or.inl` 構造 `x ∈ A ∪ B`
   - 如果 `x ∈ B`，用 `Or.inr` 構造 `x ∈ A ∪ B`

**記憶要點：**
- `A ⊆ B ↔ A ∪ B = B` 建立了子集合關係和集合相等的等價關係
- 證明時需要分別證明兩個方向
- 第一個方向使用外延性公理和分情況討論
- 第二個方向使用等式重寫，這是利用等式的重要技巧

#### 4.9 綜合範例：子集合關係與集合相等的等價關係（交集版本）

**定理：** `A ⊆ B ↔ A ∩ B = A`

這是前一個定理的對應版本，使用交集而不是聯集。這個定理同樣建立了子集合關係和集合相等之間的等價關係，但從交集的角度來理解。

**完整證明：**

```lean
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
```

**詳細步驟解析：**

#### 第一個方向：`A ⊆ B → A ∩ B = A`

**目標：** 證明如果 `A ⊆ B`，則 `A ∩ B = A`

**步驟 1：使用外延性公理**
- `apply ZFSet.ext`：將 `A ∩ B = A` 轉換為 `∀ x, x ∈ A ∩ B ↔ x ∈ A`
- 現在需要證明：對於任意 `x`，`x ∈ A ∩ B` 當且僅當 `x ∈ A`

**步驟 2：證明雙條件 `x ∈ A ∩ B ↔ x ∈ A`**

**方向 1.1：`x ∈ A ∩ B → x ∈ A`**
- 直接從交集定義得到：`x ∈ A ∩ B` 意味著 `x ∈ A ∧ x ∈ B`
- 使用 `(ZFSet.mem_inter.mp hx_inter).left` 提取 `x ∈ A`
- 這一步很簡單，因為交集本身就包含 `x ∈ A` 這個條件

**方向 1.2：`x ∈ A → x ∈ A ∩ B`**
- 如果 `x ∈ A`，因為 `A ⊆ B`（從假設 `hAB`），所以 `x ∈ B`
- 因此 `x ∈ A ∧ x ∈ B`，所以 `x ∈ A ∩ B`
- 使用 `ZFSet.mem_inter.mpr ⟨hx_A, hx_B⟩` 構造

**關鍵理解：**
- 如果 `A ⊆ B`，則 `A` 的所有元素都在 `B` 中
- 因此 `A` 的所有元素都在 `A ∩ B` 中（因為 `x ∈ A` 且 `x ∈ B`）
- 同時，`A ∩ B` 的所有元素都在 `A` 中（因為交集是 `A` 的子集合）
- 所以 `A ∩ B = A`

#### 第二個方向：`A ∩ B = A → A ⊆ B`

**目標：** 證明如果 `A ∩ B = A`，則 `A ⊆ B`

**步驟 1：引入假設**
- `intro h_eq x hx_A`：引入 `A ∩ B = A` 和 `x ∈ A`
- 目標：證明 `x ∈ B`

**步驟 2：利用等式（反向重寫）**
- 因為 `A ∩ B = A`，所以 `x ∈ A` 意味著 `x ∈ A ∩ B`
- 使用 `rw [← h_eq]` 將 `hx_A` 中的 `A` 重寫為 `A ∩ B`（注意 `←` 表示反向，從右到左）
- 現在 `hx_A` 變成 `x ∈ A ∩ B`
- 從 `x ∈ A ∩ B` 可以提取 `x ∈ B`（使用 `.right`）

**關鍵理解：**
- 如果 `A ∩ B = A`，則 `A` 的所有元素都在 `A ∩ B` 中
- 因為 `A ∩ B` 的元素必須同時在 `A` 和 `B` 中
- 所以 `A` 的所有元素都在 `B` 中
- 因此 `A ⊆ B`

**與前一個定理的對比：**

| 定理 | 形式 | 關鍵差異 |
|------|------|----------|
| 聯集版本 | `A ⊆ B ↔ A ∪ B = B` | 使用聯集，需要分情況討論 |
| 交集版本 | `A ⊆ B ↔ A ∩ B = A` | 使用交集，直接提取即可 |

**為什麼這個證明更簡單？**

1. **第一個方向**：
   - 方向 1.1：直接從交集提取 `x ∈ A`，不需要分情況
   - 方向 1.2：利用 `A ⊆ B` 證明 `x ∈ B`，然後構造交集

2. **第二個方向**：
   - 使用反向等式重寫（`rw [← h_eq]`）
   - 直接從交集提取 `x ∈ B`
   - 不需要分情況討論

**關鍵技巧總結：**

1. **反向等式重寫（`rw [← h_eq]`）**：
   - `←` 表示反向，從右到左使用等式
   - `rw [← h_eq] at hx_A`：將 `hx_A` 中的等式右邊重寫為左邊
   - 例如：如果 `h_eq : A ∩ B = A`，則 `rw [← h_eq]` 將 `A` 重寫為 `A ∩ B`

2. **交集的提取**：
   - `(ZFSet.mem_inter.mp hx_inter).left`：提取 `x ∈ A`
   - `(ZFSet.mem_inter.mp hx_inter).right`：提取 `x ∈ B`

3. **交集的構造**：
   - `ZFSet.mem_inter.mpr ⟨hx_A, hx_B⟩`：從 `x ∈ A` 和 `x ∈ B` 構造 `x ∈ A ∩ B`

**記憶要點：**
- `A ⊆ B ↔ A ∩ B = A` 是聯集版本的對應定理
- 這個證明比聯集版本更簡單，因為不需要分情況討論
- 關鍵是理解反向等式重寫（`rw [← h_eq]`）的使用
- 交集版本和聯集版本都建立了子集合關係和集合相等的等價關係

#### 4.9 綜合範例：冪集合與子集合關係的等價關係

**定理：** `A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)`

這是一個非常重要的定理，它建立了子集合關係和冪集合之間的等價關係。這個證明展示了：
- 如何使用冪集合的成員關係
- 如何利用子集合關係的傳遞性
- 如何構造冪集合的成員

**完整證明：**

```lean
theorem theorem_2_1_5(A B : ZFSet) : A ⊆ B ↔ ZFSet.powerset A ⊆ ZFSet.powerset B := by
  constructor
  -- 方向 1：A ⊆ B → 𝒫(A) ⊆ 𝒫(B)
  · intro h x hx -- h : A ⊆ B, hx : x ∈ 𝒫(A)，即 x ∈ ZFSet.powerset A
    -- 要證明 x ∈ 𝒫(B)，即 x ∈ ZFSet.powerset B，需要證明 x ⊆ B
    -- 首先，從 x ∈ 𝒫(A) 推出 x ⊆ A
    have hx_subset_A : x ⊆ A := ZFSet.mem_powerset.mp hx
    -- 由於 x ⊆ A 且 A ⊆ B，所以 x ⊆ B
    have hx_subset_B : x ⊆ B := fun y hy => h (hx_subset_A hy)
    -- 因此 x ∈ 𝒫(B)
    exact ZFSet.mem_powerset.mpr hx_subset_B
  -- 方向 2：𝒫(A) ⊆ 𝒫(B) → A ⊆ B
  · intro h x hx -- h : 𝒫(A) ⊆ 𝒫(B), hx : x ∈ A
    -- 要證明 x ∈ B
    -- 首先，注意到 A 本身是 A 的子集合，所以 A ∈ 𝒫(A)
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun y hy => hy)
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := h hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B
    -- 由於 x ∈ A 且 A ⊆ B，所以 x ∈ B
    exact hA_subset_B hx
```

**詳細步驟解析：**

#### 第一個方向：`A ⊆ B → 𝒫(A) ⊆ 𝒫(B)`

**目標：** 證明如果 `A ⊆ B`，則 `𝒫(A) ⊆ 𝒫(B)`

**步驟 1：引入假設**
- `intro h x hx`：引入 `A ⊆ B` 和 `x ∈ 𝒫(A)`
- 目標：證明 `x ∈ 𝒫(B)`，即 `x ⊆ B`

**步驟 2：從冪集合提取子集合關係**
- `ZFSet.mem_powerset.mp hx`：將 `x ∈ 𝒫(A)` 轉換為 `x ⊆ A`
- 現在我們有：`x ⊆ A` 和 `A ⊆ B`

**步驟 3：利用傳遞性**
- 因為 `x ⊆ A` 且 `A ⊆ B`，所以 `x ⊆ B`
- 使用函數構造：`fun y hy => h (hx_subset_A hy)`
  - 對於任意 `y ∈ x`，因為 `x ⊆ A`，所以 `y ∈ A`
  - 因為 `A ⊆ B`，所以 `y ∈ B`
  - 因此 `x ⊆ B`

**步驟 4：構造冪集合成員關係**
- `ZFSet.mem_powerset.mpr hx_subset_B`：將 `x ⊆ B` 轉換為 `x ∈ 𝒫(B)`

**關鍵理解：**
- 如果 `A ⊆ B`，則 `A` 的所有子集合都是 `B` 的子集合
- 因此 `𝒫(A)` 的所有元素都在 `𝒫(B)` 中
- 所以 `𝒫(A) ⊆ 𝒫(B)`

#### 第二個方向：`𝒫(A) ⊆ 𝒫(B) → A ⊆ B`

**目標：** 證明如果 `𝒫(A) ⊆ 𝒫(B)`，則 `A ⊆ B`

**步驟 1：引入假設**
- `intro h x hx`：引入 `𝒫(A) ⊆ 𝒫(B)` 和 `x ∈ A`
- 目標：證明 `x ∈ B`

**步驟 2：利用 `A` 本身**
- `A` 是 `A` 的子集合（自反性），所以 `A ∈ 𝒫(A)`
- 使用 `ZFSet.mem_powerset.mpr (fun y hy => hy)` 構造
  - `fun y hy => hy` 表示：對於任意 `y ∈ A`，有 `y ∈ A`（自反性）

**步驟 3：應用子集合關係**
- 因為 `𝒫(A) ⊆ 𝒫(B)` 且 `A ∈ 𝒫(A)`，所以 `A ∈ 𝒫(B)`
- 使用 `h hA_in_powerset_A` 得到 `A ∈ 𝒫(B)`

**步驟 4：從冪集合提取子集合關係**
- `ZFSet.mem_powerset.mp hA_in_powerset_B`：將 `A ∈ 𝒫(B)` 轉換為 `A ⊆ B`

**步驟 5：應用子集合關係**
- 因為 `x ∈ A` 且 `A ⊆ B`，所以 `x ∈ B`
- 使用 `hA_subset_B hx` 完成證明

**關鍵理解：**
- 如果 `𝒫(A) ⊆ 𝒫(B)`，則 `A` 本身（作為 `A` 的子集合）必須在 `𝒫(B)` 中
- 因此 `A ⊆ B`
- 這展示了如何利用集合本身來證明子集合關係

**為什麼這個定理很重要？**

1. **建立等價關係**：它告訴我們，`A ⊆ B` 和 `𝒫(A) ⊆ 𝒫(B)` 是等價的
   - 這意味著我們可以用冪集合來描述子集合關係
   - 也可以用子集合關係來描述冪集合的包含關係

2. **實際應用**：
   - 當我們需要證明 `A ⊆ B` 時，可以改為證明 `𝒫(A) ⊆ 𝒫(B)`
   - 當我們需要證明 `𝒫(A) ⊆ 𝒫(B)` 時，可以改為證明 `A ⊆ B`

3. **直觀理解**：
   - `A ⊆ B` 意味著 `A` 的所有元素都在 `B` 中
   - `𝒫(A) ⊆ 𝒫(B)` 意味著 `A` 的所有子集合都是 `B` 的子集合
   - 這兩個描述在本質上是相同的

**關鍵技巧總結：**

1. **冪集合的轉換**：
   - `ZFSet.mem_powerset.mp`：將 `x ∈ 𝒫(A)` 轉換為 `x ⊆ A`
   - `ZFSet.mem_powerset.mpr`：將 `x ⊆ A` 轉換為 `x ∈ 𝒫(A)`

2. **子集合關係的傳遞性**：
   - 如果 `x ⊆ A` 且 `A ⊆ B`，則 `x ⊆ B`
   - 使用函數構造：`fun y hy => h (hx_subset_A hy)`

3. **利用集合本身**：
   - `A` 是 `A` 的子集合（自反性）
   - 因此 `A ∈ 𝒫(A)`
   - 這是證明第二個方向的關鍵

**記憶要點：**
- `A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)` 建立了子集合關係和冪集合包含關係的等價關係
- 證明時需要分別證明兩個方向
- 第一個方向使用傳遞性
- 第二個方向利用集合本身（`A ∈ 𝒫(A)`）

### 5. 差集合（`A - B`）

**定義：** `set_diff A B = {x ∈ A : x ∉ B}`

**成員關係：** `x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B`

**使用：**
```lean
(mem_diff A B x).mp   -- x ∈ A - B → x ∈ A ∧ x ∉ B
(mem_diff A B x).mpr  -- x ∈ A ∧ x ∉ B → x ∈ A - B
```

**範例：**
```lean
theorem example23 (A x : ZFSet) : x ∈ A → x ∈ set_diff A ∅ := by
  intro hx
  exact (mem_diff A ∅ x).mpr ⟨hx, ZFSet.notMem_empty x⟩
```

### 6. 補集合（`Aᶜ`）

**定義：** 設 `U` 為全域集合，`A ⊆ U`，則 `A` 的補集合 `compl U A = U - A`

**成員關係：** `x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`

**使用：**
```lean
compl U A              -- A 的補集合（相對於全域集合 U）
(mem_compl U A x).mp   -- x ∈ compl U A → x ∈ U ∧ x ∉ A
(mem_compl U A x).mpr  -- x ∈ U ∧ x ∉ A → x ∈ compl U A
```

**詳細說明：**

補集合是相對於全域集合 `U` 定義的。`A` 的補集合 `compl U A` 表示在全域集合 `U` 中不屬於 `A` 的所有元素。

**定義解析：**
- `compl U A = set_diff U A`：補集合就是差集合 `U - A`
- `x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`：元素 `x` 屬於補集合當且僅當 `x` 在全域集合 `U` 中且不在 `A` 中

**範例：**
```lean
theorem example_compl (U A x : ZFSet) : x ∈ compl U A ↔ x ∈ U ∧ x ∉ A := by
  exact mem_compl U A x  -- 直接使用補集合的定義
```

**與差集合的關係：**
- 補集合是差集合的特殊情況
- `compl U A = set_diff U A`
- 補集合的成員關係與差集合相同：`mem_compl U A x = mem_diff U A x`

---

## 常見證明模式

### 模式 1：傳遞性證明

**模式：** 證明 `A ⊆ B` 和 `B ⊆ C` 推出 `A ⊆ C`

```lean
theorem transitivity (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h
  rcases h with ⟨hAB, hBC⟩
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  have hxC : x ∈ C := hBC hxB
  exact hxC
```

### 模式 2：外延性證明

**模式：** 證明兩個集合相等

```lean
theorem extensionality (A B : ZFSet) : A = B := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx  -- x ∈ A → x ∈ B
    -- 證明步驟
  · intro hx  -- x ∈ B → x ∈ A
    -- 證明步驟
```

### 模式 3：反證法

**模式：** 假設结论的否定，推出矛盾

```lean
theorem by_contradiction (A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  by_contra hx_in_A  -- 假設 x ∈ A
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A
  exact hx_notin_B hx_in_B  -- 矛盾
```

### 模式 4：分情況討論

**模式：** 对析取命題分情況處理

```lean
theorem case_analysis (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h
  rw [ZFSet.mem_union] at h
  cases h with
  | inl hx => exact Or.inl hx
  | inr hx => exact Or.inr hx
```

### 模式 5：空真命題

**模式：** 从矛盾推出任何结论

```lean
theorem vacuous_truth (A : ZFSet) : ∅ ⊆ A := by
  intro x hx  -- hx : x ∈ ∅（這是矛盾的）
  have : False := ZFSet.notMem_empty x hx
  exact this.elim  -- 从矛盾推出任何东西
```

---

## 完整證明範例

### 範例 1：空集合合是任何集合的子集合

```lean
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- hx : x ∈ ∅，但空集合合沒有元素，這是矛盾的
  have : False := ZFSet.notMem_empty x hx
  -- 从矛盾可以推出任何东西（包括 x ∈ A）
  exact this.elim
```

**步驟解析：**
1. `intro x hx`：引入 `∀ x, x ∈ ∅ → x ∈ A` 中的 x 和 `x ∈ ∅`
2. `have : False := ZFSet.notMem_empty x hx`：从 `x ∈ ∅` 推出矛盾
3. `exact this.elim`：从矛盾推出任何结论（包括 `x ∈ A`）

**關鍵理解：**
- 這是「空真命題」（Vacuous Truth）的典型例子
- 前提 `x ∈ ∅` 永遠為假（因為空集合沒有元素）
- 從假的前提可以推出任何結論
- 這是邏輯中的一個重要原理：`False → P` 對任何命題 `P` 都成立

### 範例 1.5：集合的自反性

```lean
theorem theorem_2_1_1_b(A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx
```

**步驟解析：**
1. `intro x hx`：引入 `∀ x, x ∈ A → x ∈ A` 中的 x 和 `x ∈ A`
2. `exact hx`：直接使用假設 `hx : x ∈ A` 完成證明

**關鍵理解：**
- 這是最簡單的證明之一
- 目標是 `x ∈ A`，而我們已經有 `hx : x ∈ A`
- 直接使用 `exact` 即可完成
- 這展示了集合包含關係的自反性：任何集合都是自己的子集合

### 範例 2：集合包含關係的傳遞性

```lean
theorem theorem_2_1_1_c(A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h  -- h: A ⊆ B ∧ B ⊆ C
  rcases h with ⟨hxAB, hxBC⟩  -- 分解：hxAB: A ⊆ B, hxBC: B ⊆ C
  intro x hxA  -- hxA: x ∈ A
  have hxB : x ∈ B := hxAB hxA  -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B
  have hxC : x ∈ C := hxBC hxB  -- ∵ x ∈ B ∧ B ⊆ C ∴ x ∈ C
  exact hxC
```

**步驟解析：**
1. `intro h`：引入前提 `A ⊆ B ∧ B ⊆ C`
2. `rcases h with ⟨hxAB, hxBC⟩`：分解合取，得到兩個子集合關係
3. `intro x hxA`：引入任意元素 x 和假設 `x ∈ A`
4. `have hxB : x ∈ B := hxAB hxA`：應用 `A ⊆ B` 得到 `x ∈ B`
5. `have hxC : x ∈ C := hxBC hxB`：應用 `B ⊆ C` 得到 `x ∈ C`
6. `exact hxC`：完成證明

### 範例 3：使用外延性公理證明集合相等

```lean
theorem thm2_1_2 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h  -- h: A = ∅ ∧ B = ∅
  rcases h with ⟨hA, hB⟩  -- hA: A = ∅, hB: B = ∅
  -- 使用 calc 进行鏈式等式證明：A = ∅ = B
  calc
    A = ∅ := hA  -- hA: A = ∅
    _ = B := hB.symm  -- hB : B = ∅，所以 hB.symm : ∅ = B
```

**步驟解析：**
1. `intro h`：引入前提
2. `rcases h with ⟨hA, hB⟩`：分解合取
3. `calc`：使用鏈式等式
   - `A = ∅ := hA`：第一步
   - `_ = B := hB.symm`：第二步（`_` 表示上一步的結果 `∅`）

### 範例 4：反證法

```lean
theorem exercise_2_1_7(A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h  -- h: x ∉ B ∧ A ⊆ B
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  -- By contradiction, suppose x ∈ A
  by_contra hx_in_A  -- 假設 x ∈ A（要證明 x ∉ A，所以假設其否定）
  -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A
  -- ∵ x ∈ B ∧ x ∉ B ∴ False
  exact hx_notin_B hx_in_B
```

**步驟解析：**
1. `intro h`：引入前提
2. `rcases h with ⟨hx_notin_B, hA_subset_B⟩`：分解合取
3. `by_contra hx_in_A`：假設 `x ∈ A`（要證明 `x ∉ A`）
4. `have hx_in_B : x ∈ B := hA_subset_B hx_in_A`：推出 `x ∈ B`
5. `exact hx_notin_B hx_in_B`：矛盾（`x ∉ B` 和 `x ∈ B`）

### 範例 4.5：非空子集合的性質（結合反證法和外延性公理）

**定理：** `(A ⊆ B ∧ A ≠ ∅) → B ≠ ∅`

這是一個重要的定理，展示了如何結合反證法和外延性公理來證明集合的非空性。這個證明結合了多種技巧：
- 反證法（`by_contra`）
- 等式重寫（`rw`）
- 外延性公理（`ZFSet.ext`）
- 從矛盾推出結論（`False.elim`）

**完整證明：**

```lean
theorem theorem_2_1_3(A B : ZFSet) : (A ⊆ B ∧ A ≠ ∅) → B ≠ ∅ := by
  -- 引入前提條件
  intro h -- h: A ⊆ B ∧ A ≠ ∅
  -- 分解合取命題：hxAB: A ⊆ B, hA_nonempty: A ≠ ∅
  rcases h with ⟨hxAB, hA_nonempty⟩
  -- 使用反證法：假設 B = ∅
  by_contra hB_empty -- hB_empty: B = ∅
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
```

**詳細步驟解析：**

**步驟 1：引入和分解前提**
- `intro h`：引入 `A ⊆ B ∧ A ≠ ∅`
- `rcases h with ⟨hxAB, hA_nonempty⟩`：分解合取，得到 `A ⊆ B` 和 `A ≠ ∅`

**步驟 2：使用反證法**
- `by_contra hB_empty`：假設 `B = ∅`（要證明 `B ≠ ∅`，所以假設其否定）
- 目標：推出矛盾

**步驟 3：證明 `A ⊆ ∅`**
- 因為 `A ⊆ B` 且 `B = ∅`，所以 `A ⊆ ∅`
- 使用 `rw [hB_empty] at hxAB` 將 `hxAB` 中的 `B` 替換為 `∅`
- 現在 `hxAB` 變成 `A ⊆ ∅`

**步驟 4：證明 `A = ∅`**
- 這是證明的關鍵部分，需要使用外延性公理
- `apply ZFSet.ext`：將 `A = ∅` 轉換為 `∀ x, x ∈ A ↔ x ∈ ∅`
- `intro x`：引入任意元素 `x`
- `constructor`：將雙條件分解成兩個方向

**方向 4.1：`x ∈ A → x ∈ ∅`**
- 如果 `x ∈ A`，因為 `A ⊆ ∅`，所以 `x ∈ ∅`
- 但空集合沒有元素，這是矛盾的
- 使用 `False.elim` 從矛盾推出任何結論

**方向 4.2：`x ∈ ∅ → x ∈ A`**
- 如果 `x ∈ ∅`，這本身就是矛盾的（空集合沒有元素）
- 使用 `False.elim` 從矛盾推出任何結論

**步驟 5：推出矛盾**
- 我們證明了 `A = ∅`（`hA_empty`）
- 但前提有 `A ≠ ∅`（`hA_nonempty`）
- 這兩個命題矛盾
- 使用 `exact hA_nonempty hA_empty` 完成證明

**關鍵理解：**

1. **反證法的使用**：
   - 要證明 `B ≠ ∅`，假設 `B = ∅`
   - 從這個假設推出矛盾
   - 因此 `B ≠ ∅` 成立

2. **外延性公理的使用**：
   - 證明 `A = ∅` 時，使用 `apply ZFSet.ext`
   - 轉換為證明所有元素的成員關係等價
   - 兩個方向都從矛盾推出，這是空集合的特性

3. **等式重寫的使用**：
   - `rw [hB_empty] at hxAB`：在假設中重寫等式
   - 將 `A ⊆ B` 轉換為 `A ⊆ ∅`

4. **從矛盾推出結論**：
   - `False.elim`：從 `False` 可以推出任何命題
   - 這是邏輯中的一個基本原理

**為什麼這個證明很重要？**

1. **展示了多種技巧的結合**：
   - 反證法
   - 外延性公理
   - 等式重寫
   - 從矛盾推出結論

2. **實際應用**：
   - 當我們知道 `A ⊆ B` 且 `A` 非空時，可以推出 `B` 非空
   - 這在證明集合非空性時很有用

3. **邏輯推理**：
   - 如果 `A` 有元素，且 `A` 的所有元素都在 `B` 中
   - 則 `B` 也必須有元素（至少 `A` 的元素）

**記憶要點：**
- 反證法是證明否定命題的重要方法
- 外延性公理是證明集合相等的標準方法
- 等式重寫可以改變假設的形式
- 從矛盾可以推出任何結論（`False.elim`）

### 範例 5：复杂的外延性證明

```lean
theorem exercise_2_1_18_a(A B : ZFSet) : A = B ↔ ZFSet.powerset A = ZFSet.powerset B := by
  constructor
  · intro h  -- h: A = B
    rw [h]  -- 如果 A = B，直接重寫即可得到 𝒫(A) = 𝒫(B)
  · intro h  -- h: 𝒫(A) = 𝒫(B)
    -- 步驟 1：證明 A ∈ 𝒫(A)（因為 A ⊆ A）
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun x hx => hx)
    -- 步驟 2：由于 𝒫(A) = 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
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
    apply ZFSet.ext  -- 將 A = B 轉換為 ∀ x, x ∈ A ↔ x ∈ B
    intro x  -- 引入任意元素 x，需要證明 x ∈ A ↔ x ∈ B
    constructor  -- 將雙條件 ↔ 分解成兩個方向
    · exact fun hx => hA_subset_B hx  -- 方向1：x ∈ A → x ∈ B
    · exact fun hx => hB_subset_A hx  -- 方向2：x ∈ B → x ∈ A
```

**步驟解析：**
1. `constructor`：分解雙條件 `↔`
2. 第一個方向：`A = B → 𝒫(A) = 𝒫(B)`，直接重寫
3. 第二个方向：`𝒫(A) = 𝒫(B) → A = B`
   - 證明 `A ∈ 𝒫(A)`（因為 `A ⊆ A`）
   - 利用 `𝒫(A) = 𝒫(B)` 得到 `A ∈ 𝒫(B)`，即 `A ⊆ B`
   - 類似地得到 `B ⊆ A`
   - 使用外延性公理得到 `A = B`

### 範例 6：循環包含關係與集合相等

**定理：** `(A ⊆ B ∧ B ⊆ C ∧ C ⊆ A) → (A = B ∧ B = C)`

這是一個重要的定理，展示了當三個集合形成循環包含關係時，它們必須相等。這個證明展示了：
- 如何使用傳遞性定理
- 如何結合多個子集合關係
- 如何使用外延性公理證明集合相等
- 如何使用等式重寫

**完整證明：**

```lean
theorem exercise_2_1_9(A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C ∧ C ⊆ A) → (A = B ∧ B = C) := by
  intro h -- h: A ⊆ B ∧ B ⊆ C ∧ C ⊆ A
  rcases h with ⟨hA_subset_B, hB_subset_C, hC_subset_A⟩
  -- hA_subset_B: A ⊆ B
  -- hB_subset_C: B ⊆ C
  -- hC_subset_A: C ⊆ A
  -- A ⊆ B ∧ B ⊆ C → A ⊆ C
  have hA_subset_C : A ⊆ C := theorem_2_1_1_c A B C ⟨hA_subset_B, hB_subset_C⟩
  -- A ⊆ C ∧ C ⊆ A → A = C
  have hA_eq_C : A = C := by
    apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => hA_subset_C hx -- hA_subset_C : A ⊆ C，應用到 x 和 hx : x ∈ A 得到 x ∈ C
    · exact fun hx => hC_subset_A hx -- hC_subset_A : C ⊆ A，應用到 x 和 hx : x ∈ C 得到 x ∈ A
  -- C ⊆ A ∧ A ⊆ B → C ⊆ B
  have hC_subset_B : C ⊆ B := theorem_2_1_1_c C A B ⟨hC_subset_A, hA_subset_B⟩
  -- C ⊆ B ∧ B ⊆ C → B = C
  have hB_eq_C : B = C := by
    apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => hB_subset_C hx -- hB_subset_C : B ⊆ C，應用到 x 和 hx : x ∈ B 得到 x ∈ C
    · exact fun hx => hC_subset_B hx -- hC_subset_B : C ⊆ B，應用到 x 和 hx : x ∈ C 得到 x ∈ B
  -- A = C ∧ B = C → A = B
  constructor
  · -- prove A = B
    rw [hA_eq_C, hB_eq_C]
  · -- prove B = C
    exact hB_eq_C
```

**詳細步驟解析：**

**步驟 1：引入和分解前提**
- `intro h`：引入 `A ⊆ B ∧ B ⊆ C ∧ C ⊆ A`
- `rcases h with ⟨hA_subset_B, hB_subset_C, hC_subset_A⟩`：分解三元合取，得到三個子集合關係

**步驟 2：證明 `A ⊆ C`**
- 因為 `A ⊆ B` 且 `B ⊆ C`，使用傳遞性定理 `theorem_2_1_1_c` 得到 `A ⊆ C`
- 使用 `theorem_2_1_1_c A B C ⟨hA_subset_B, hB_subset_C⟩` 構造證明

**步驟 3：證明 `A = C`**
- 因為 `A ⊆ C` 且 `C ⊆ A`，使用外延性公理證明 `A = C`
- `apply ZFSet.ext`：將 `A = C` 轉換為 `∀ x, x ∈ A ↔ x ∈ C`
- `intro x`：引入任意元素 `x`
- `constructor`：將雙條件分解成兩個方向
  - 方向 1：`x ∈ A → x ∈ C`，使用 `hA_subset_C`
  - 方向 2：`x ∈ C → x ∈ A`，使用 `hC_subset_A`

**步驟 4：證明 `C ⊆ B`**
- 因為 `C ⊆ A` 且 `A ⊆ B`，使用傳遞性定理得到 `C ⊆ B`
- 使用 `theorem_2_1_1_c C A B ⟨hC_subset_A, hA_subset_B⟩` 構造證明

**步驟 5：證明 `B = C`**
- 因為 `C ⊆ B` 且 `B ⊆ C`，使用外延性公理證明 `B = C`
- `apply ZFSet.ext`：將 `B = C` 轉換為 `∀ x, x ∈ B ↔ x ∈ C`
- `intro x`：引入任意元素 `x`
- `constructor`：將雙條件分解成兩個方向
  - 方向 1：`x ∈ B → x ∈ C`，使用 `hB_subset_C`
  - 方向 2：`x ∈ C → x ∈ B`，使用 `hC_subset_B`

**步驟 6：證明 `A = B` 和 `B = C`**
- `constructor`：將合取 `A = B ∧ B = C` 分解成兩個部分
- 第一部分：證明 `A = B`
  - 使用 `rw [hA_eq_C, hB_eq_C]`：將 `A` 重寫為 `C`，然後將 `C` 重寫為 `B`，得到 `A = B`
- 第二部分：證明 `B = C`
  - 直接使用 `exact hB_eq_C`

**關鍵理解：**

1. **循環包含關係的性質**：
   - 如果 `A ⊆ B`、`B ⊆ C`、`C ⊆ A`，則三個集合必須相等
   - 這是因為循環包含關係意味著每個集合都是其他集合的子集合

2. **傳遞性的應用**：
   - 從 `A ⊆ B` 和 `B ⊆ C` 推出 `A ⊆ C`
   - 從 `C ⊆ A` 和 `A ⊆ B` 推出 `C ⊆ B`
   - 這展示了傳遞性定理的實際應用

3. **外延性公理的使用**：
   - 當兩個集合互為子集合時（`A ⊆ C` 且 `C ⊆ A`），它們相等
   - 使用 `ZFSet.ext` 將集合相等轉換為所有元素的成員關係等價

4. **等式重寫的技巧**：
   - `rw [hA_eq_C, hB_eq_C]`：鏈式重寫
   - 先將 `A` 重寫為 `C`，再將 `C` 重寫為 `B`，最終得到 `A = B`

**為什麼這個定理很重要？**

1. **建立循環包含關係的性質**：
   - 它告訴我們，循環包含關係意味著集合相等
   - 這在證明集合相等時很有用

2. **實際應用**：
   - 當我們有三個集合的循環包含關係時，可以推出它們相等
   - 這簡化了證明過程

3. **邏輯推理**：
   - 如果 `A ⊆ B`、`B ⊆ C`、`C ⊆ A`，則 `A`、`B`、`C` 有相同的元素
   - 因此它們相等

**關鍵技巧總結：**

1. **傳遞性定理的應用**：
   - `theorem_2_1_1_c`：從 `A ⊆ B` 和 `B ⊆ C` 推出 `A ⊆ C`
   - 可以應用多次來建立新的子集合關係

2. **外延性公理的使用**：
   - 當兩個集合互為子集合時，使用 `ZFSet.ext` 證明它們相等
   - 轉換為證明所有元素的成員關係等價

3. **等式重寫的鏈式使用**：
   - `rw [hA_eq_C, hB_eq_C]`：鏈式重寫多個等式
   - 這可以簡化證明過程

**記憶要點：**
- 循環包含關係 `A ⊆ B ∧ B ⊆ C ∧ C ⊆ A` 意味著 `A = B = C`
- 證明時需要使用傳遞性定理建立新的子集合關係
- 當兩個集合互為子集合時，使用外延性公理證明它們相等
- 等式重寫可以鏈式使用來簡化證明

### 範例 7：子集合關係與聯集的保持性

**定理：** `A ⊆ B → A ∪ C ⊆ B ∪ C`

這是一個重要的定理，展示了子集合關係在聯集運算下的保持性。如果 `A` 是 `B` 的子集合，則 `A` 與任意集合 `C` 的聯集也是 `B` 與 `C` 的聯集的子集合。這個證明展示了：
- 如何使用分情況討論處理聯集
- 如何應用子集合關係
- 如何構造聯集成員關係

**完整證明：**

```lean
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
```

**詳細步驟解析：**

**步驟 1：引入假設**
- `intro hA_B x hx_union`：引入 `A ⊆ B`、任意元素 `x` 和 `x ∈ A ∪ C`
- 目標：證明 `x ∈ B ∪ C`

**步驟 2：分解聯集**
- `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ A ∪ C` 轉換為 `x ∈ A ∨ x ∈ C`
- 現在需要分兩種情況討論

**情況 1：`x ∈ A`**
- 如果 `x ∈ A`，因為 `A ⊆ B`（從假設 `hA_B`），所以 `x ∈ B`
- 使用 `hA_B hx_A` 應用子集合關係，得到 `hx_B : x ∈ B`
- 因為 `x ∈ B`，所以 `x ∈ B ∪ C`（用 `Or.inl` 選擇左分支）
- 使用 `ZFSet.mem_union.mpr (Or.inl hx_B)` 構造聯集成員關係

**情況 2：`x ∈ C`**
- 如果 `x ∈ C`，則 `x ∈ B ∪ C`（因為 `x ∈ C` 是 `x ∈ B ∨ x ∈ C` 的右分支）
- 使用 `ZFSet.mem_union.mpr (Or.inr hx_C)` 構造聯集成員關係

**關鍵理解：**

1. **子集合關係的應用**：
   - `hA_B : A ⊆ B` 是一個函數，可以應用到 `x ∈ A` 得到 `x ∈ B`
   - 直接使用 `hA_B hx_A` 即可

2. **分情況討論的必要性**：
   - `x ∈ A ∪ C` 意味著 `x ∈ A` 或 `x ∈ C`
   - 兩種情況都需要處理
   - 情況 1 需要使用子集合關係
   - 情況 2 直接成立

3. **聯集的構造**：
   - 情況 1：`x ∈ B`，用 `Or.inl` 構造 `x ∈ B ∪ C`
   - 情況 2：`x ∈ C`，用 `Or.inr` 構造 `x ∈ B ∪ C`
   - 注意：在 `x ∈ B ∨ x ∈ C` 中，`x ∈ B` 是左分支，`x ∈ C` 是右分支

**為什麼這個定理很重要？**

1. **展示子集合關係的保持性**：
   - 它告訴我們，子集合關係在聯集運算下是保持的
   - 如果 `A ⊆ B`，則 `A ∪ C ⊆ B ∪ C` 對任意集合 `C` 都成立

2. **實際應用**：
   - 當我們需要證明 `A ∪ C ⊆ B ∪ C` 時，可以改為證明 `A ⊆ B`
   - 這簡化了證明過程

3. **直觀理解**：
   - 如果 `A` 的所有元素都在 `B` 中
   - 則 `A` 和 `C` 的聯集的所有元素都在 `B` 和 `C` 的聯集中
   - 因為 `A` 的元素在 `B` 中，`C` 的元素在 `C` 中

**關鍵技巧總結：**

1. **分情況討論**：
   - 當有 `x ∈ A ∪ C` 時，使用 `cases` 分兩種情況
   - 情況 1：`x ∈ A`，需要使用子集合關係
   - 情況 2：`x ∈ C`，直接構造聯集

2. **子集合關係的應用**：
   - `hA_B : A ⊆ B` 可以應用到 `x ∈ A` 得到 `x ∈ B`
   - 直接使用 `hA_B hx_A` 即可

3. **聯集的構造**：
   - 如果 `x ∈ B`，用 `Or.inl` 構造 `x ∈ B ∪ C`
   - 如果 `x ∈ C`，用 `Or.inr` 構造 `x ∈ B ∪ C`
   - 記住：`Or.inl` 用於左分支，`Or.inr` 用於右分支

**與其他定理的對比：**

| 定理 | 形式 | 關鍵差異 |
|------|------|----------|
| 聯集交換律 | `A ∪ B = B ∪ A` | 證明集合相等，需要雙方向 |
| 聯集結合律 | `A ∪ (B ∪ C) = (A ∪ B) ∪ C` | 證明集合相等，需要雙方向 |
| 子集合保持性 | `A ⊆ B → A ∪ C ⊆ B ∪ C` | 只證明一個方向，使用分情況討論 |

**記憶要點：**
- `A ⊆ B → A ∪ C ⊆ B ∪ C` 展示了子集合關係在聯集運算下的保持性
- 證明時需要分情況討論：`x ∈ A` 或 `x ∈ C`
- 情況 1 需要使用子集合關係，情況 2 直接構造聯集
- 關鍵是理解如何應用子集合關係和構造聯集成員關係

### 範例 8：子集合關係與交集的保持性

**定理：** `A ⊆ B → A ∩ C ⊆ B ∩ C`

這是範例 7 的對應版本，使用交集而不是聯集。這個定理展示了子集合關係在交集運算下的保持性。如果 `A` 是 `B` 的子集合，則 `A` 與任意集合 `C` 的交集也是 `B` 與 `C` 的交集的子集合。這個證明展示了：
- 如何分解交集成員關係
- 如何應用子集合關係
- 如何構造交集成員關係
- 與聯集版本的對比

**完整證明：**

```lean
theorem theorem_2_2_1_r (A B C : ZFSet) : A ⊆ B → A ∩ C ⊆ B ∩ C := by 
  intro hA_B x hx_inter -- hA_B : A ⊆ B, x : any arbitrary element, hx_inter : x ∈ A ∩ C
  -- 目標：證明 x ∈ B ∩ C
  have h1 : x ∈ A ∧ x ∈ C := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ C 拆成 x ∈ A ∧ x ∈ C（使用 .mp 分解交集成員關係）
  have hx_B : x ∈ B := hA_B h1.left -- 應用 hA_B : A ⊆ B 到 h1.left : x ∈ A，得到 x ∈ B
  have hx_C : x ∈ C := h1.right -- 從 x ∈ A ∧ x ∈ C 提取 x ∈ C（使用 .right 提取合取的右部分）
  exact ZFSet.mem_inter.mpr ⟨hx_B, hx_C⟩ -- x ∈ B ∧ x ∈ C，所以 x ∈ B ∩ C（使用 .mpr 構造交集成員關係）
```

**詳細步驟解析：**

**步驟 1：引入假設**
- `intro hA_B x hx_inter`：引入 `A ⊆ B`、任意元素 `x` 和 `x ∈ A ∩ C`
- 目標：證明 `x ∈ B ∩ C`

**步驟 2：分解交集成員關係**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ A ∩ C` 轉換為 `x ∈ A ∧ x ∈ C`
- 使用 `.mp` 分解交集成員關係，得到合取 `h1 : x ∈ A ∧ x ∈ C`

**步驟 3：提取合取的部分**
- `h1.left`：從 `x ∈ A ∧ x ∈ C` 提取 `x ∈ A`
- `h1.right`：從 `x ∈ A ∧ x ∈ C` 提取 `x ∈ C`
- 現在我們有：`x ∈ A` 和 `x ∈ C`

**步驟 4：應用子集合關係**
- `hA_B h1.left`：應用 `hA_B : A ⊆ B` 到 `h1.left : x ∈ A`，得到 `hx_B : x ∈ B`
- 因為 `A ⊆ B` 且 `x ∈ A`，所以 `x ∈ B`

**步驟 5：構造交集成員關係**
- 現在我們有：`hx_B : x ∈ B` 和 `hx_C : x ∈ C`
- 使用 `⟨hx_B, hx_C⟩` 構造合取 `x ∈ B ∧ x ∈ C`
- 使用 `ZFSet.mem_inter.mpr` 將合取轉換為交集成員關係 `x ∈ B ∩ C`

**關鍵理解：**

1. **交集的分解**：
   - `x ∈ A ∩ C` 意味著 `x ∈ A` 且 `x ∈ C`
   - 使用 `ZFSet.mem_inter.mp` 分解交集成員關係
   - 然後使用 `.left` 和 `.right` 提取單個成員關係

2. **子集合關係的應用**：
   - `hA_B : A ⊆ B` 可以應用到 `x ∈ A` 得到 `x ∈ B`
   - 直接使用 `hA_B h1.left` 即可

3. **交集的構造**：
   - 需要同時證明 `x ∈ B` 和 `x ∈ C`
   - 使用 `⟨hx_B, hx_C⟩` 構造合取
   - 使用 `ZFSet.mem_inter.mpr` 轉換為交集成員關係

**為什麼這個定理很重要？**

1. **展示子集合關係的保持性**：
   - 它告訴我們，子集合關係在交集運算下也是保持的
   - 如果 `A ⊆ B`，則 `A ∩ C ⊆ B ∩ C` 對任意集合 `C` 都成立

2. **實際應用**：
   - 當我們需要證明 `A ∩ C ⊆ B ∩ C` 時，可以改為證明 `A ⊆ B`
   - 這簡化了證明過程

3. **直觀理解**：
   - 如果 `A` 的所有元素都在 `B` 中
   - 則 `A` 和 `C` 的交集的所有元素都在 `B` 和 `C` 的交集中
   - 因為 `A ∩ C` 的元素必須同時在 `A` 和 `C` 中，而 `A` 的元素都在 `B` 中

**關鍵技巧總結：**

1. **交集的分解**：
   - 使用 `ZFSet.mem_inter.mp` 將 `x ∈ A ∩ C` 轉換為 `x ∈ A ∧ x ∈ C`
   - 使用 `.left` 和 `.right` 提取單個成員關係

2. **子集合關係的應用**：
   - `hA_B : A ⊆ B` 可以應用到 `x ∈ A` 得到 `x ∈ B`
   - 直接使用 `hA_B h1.left` 即可

3. **交集的構造**：
   - 需要同時證明 `x ∈ B` 和 `x ∈ C`
   - 使用 `⟨hx_B, hx_C⟩` 構造合取
   - 使用 `ZFSet.mem_inter.mpr` 轉換為交集成員關係

**與聯集版本的對比：**

| 特性 | 聯集版本 | 交集版本 |
|------|----------|----------|
| 定理 | `A ⊆ B → A ∪ C ⊆ B ∪ C` | `A ⊆ B → A ∩ C ⊆ B ∩ C` |
| 證明方法 | 分情況討論（`cases`） | 直接分解和構造 |
| 複雜度 | 需要處理兩種情況 | 只需要一個流程 |
| 關鍵步驟 | `cases` + `Or.inl`/`Or.inr` | `.mp` + `.left`/`.right` + `.mpr` |

**為什麼交集版本更簡單？**

1. **不需要分情況討論**：
   - 聯集版本需要分 `x ∈ A` 或 `x ∈ C` 兩種情況
   - 交集版本直接從 `x ∈ A ∩ C` 得到 `x ∈ A` 和 `x ∈ C`

2. **直接提取**：
   - 從 `x ∈ A ∩ C` 可以直接提取 `x ∈ A` 和 `x ∈ C`
   - 不需要考慮多種可能性

3. **構造更直接**：
   - 只需要證明 `x ∈ B` 和 `x ∈ C`，然後構造交集
   - 不需要選擇分支（`Or.inl`/`Or.inr`）

**記憶要點：**
- `A ⊆ B → A ∩ C ⊆ B ∩ C` 展示了子集合關係在交集運算下的保持性
- 證明時不需要分情況討論，直接分解交集即可
- 關鍵步驟：分解交集 → 應用子集合關係 → 構造交集
- 交集版本比聯集版本更簡單，因為不需要分情況討論

### 範例 9：補集合的定義

**定義：** 設 `U` 為全域集合，`A ⊆ U`。`A` 的補集合 `Aᶜ` 定義為 `U - A`

補集合是集合論中的一個重要概念，它表示在全域集合 `U` 中不屬於 `A` 的所有元素。這個定義展示了：
- 補集合與差集合的關係
- 補集合的成員關係
- 如何使用差集合來表示補集合

**完整證明：**

```lean
-- Definition Let U be the universe and A ⊆ U. The complement of A is the set Aᶜ = U - A
-- 補集合的定義：相對於全域集合 U，A 的補集合定義為 U - A
-- 這個定理展示補集合的成員關係：x ∈ compl U A ↔ x ∈ U ∧ x ∉ A
-- 使用新定義的 compl 函數和 mem_compl 定理
theorem definition_2_2_1_a (U A x : ZFSet) : x ∈ compl U A ↔ x ∈ U ∧ x ∉ A := by
  exact mem_compl U A x -- 根據補集合的定義 mem_compl，x ∈ compl U A ↔ x ∈ U ∧ x ∉ A
```

**詳細步驟解析：**

**步驟 1：理解補集合的定義**
- 補集合 `compl U A` 定義為 `set_diff U A`（即 `U - A`）
- 補集合的成員關係：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`

**步驟 2：使用補集合的定義**
- `mem_compl U A x` 是補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 直接使用 `mem_compl` 即可完成證明

**關鍵理解：**

1. **補集合與差集合的關係**：
   - 補集合 `compl U A` 定義為差集合 `set_diff U A`（即 `U - A`）
   - 補集合的成員關係與差集合完全相同：`mem_compl U A x = mem_diff U A x`

2. **補集合的成員關係**：
   - `x ∈ compl U A` 當且僅當 `x ∈ U` 且 `x ∉ A`
   - 這意味著補集合包含所有在全域集合中但不屬於 `A` 的元素

3. **定義的簡潔性**：
   - 補集合使用 `compl` 函數定義，實際上是差集合的特殊情況
   - 使用 `mem_compl` 來處理補集合的成員關係

**為什麼這個定義很重要？**

1. **建立補集合的概念**：
   - 它告訴我們補集合是什麼
   - 補集合是相對於全域集合定義的

2. **實際應用**：
   - 當我們需要表示「不屬於 `A` 的元素」時，可以使用補集合
   - 補集合在邏輯運算和集合運算中都有重要應用

3. **直觀理解**：
   - 補集合就像「反面」或「補充」
   - 如果 `A` 是某個性質的集合，那麼 `Aᶜ` 就是不滿足該性質的集合

**關鍵技巧總結：**

1. **補集合的定義**：
   - 補集合 `compl U A` 定義為 `set_diff U A`（即 `U - A`）
   - 補集合的成員關係：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`

2. **使用補集合函數**：
   - 使用 `compl U A` 來表示補集合
   - 使用 `mem_compl` 來處理補集合的成員關係

3. **簡潔的證明**：
   - 因為補集合定義為差集合，所以證明很簡單
   - 直接使用 `mem_compl` 即可

**與差集合的對比：**

| 特性 | 差集合 | 補集合 |
|------|--------|--------|
| 定義 | `set_diff A B = {x ∈ A : x ∉ B}` | `compl U A = set_diff U A` |
| 成員關係 | `x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B` | `x ∈ compl U A ↔ x ∈ U ∧ x ∉ A` |
| 函數 | `set_diff` | `compl` |
| 定理 | `mem_diff` | `mem_compl` |
| 關係 | 通用概念 | 差集合的特殊情況（相對於全域集合） |

**記憶要點：**
- 補集合 `compl U A` 定義為 `set_diff U A`（即 `U - A`），其中 `U` 是全域集合
- 補集合的成員關係：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 使用 `mem_compl` 來處理補集合的成員關係
- 補集合是差集合的特殊情況，所以可以使用差集合的性質
- 補集合在邏輯運算和集合運算中都有重要應用

### 範例 10：雙重補集合定理

**定理：** `(Aᶜ)ᶜ = A`，即 `compl U (compl U A) = A`

這是一個重要的補集合性質，展示了補集合的「雙重否定」特性。對一個集合取兩次補集合會回到原集合。這個證明展示了：
- 如何使用外延性公理證明集合相等
- 如何使用反證法證明否定命題
- 如何結合補集合的定義和子集合關係

**完整證明：**

```lean
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
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ compl U (compl U A) → x ∈ A`

**目標：** 證明如果 `x ∈ compl U (compl U A)`，則 `x ∈ A`

**步驟 1：分解補集合成員關係**
- `(mem_compl U (compl U A) x).mp hx_compl_compl`：將 `x ∈ compl U (compl U A)` 轉換為 `x ∈ U ∧ x ∉ compl U A`
- 現在我們有：`x ∈ U` 和 `x ∉ compl U A`

**步驟 2：使用反證法**
- `by_contra hx_not_in_A`：假設 `x ∉ A`（要證明 `x ∈ A`，所以假設其否定）
- 目標：推出矛盾

**步驟 3：構造補集合成員關係**
- 如果 `x ∉ A` 且 `x ∈ U`，則 `x ∈ compl U A`
- 使用 `(mem_compl U A x).mpr ⟨h1.left, hx_not_in_A⟩` 構造

**步驟 4：推出矛盾**
- 我們有：`x ∉ compl U A`（從 `h1.right`）
- 我們有：`x ∈ compl U A`（從 `hx_in_compl`）
- 這兩個命題矛盾
- 因此 `x ∈ A` 成立

**關鍵理解：**
- 如果 `x ∈ compl U (compl U A)`，則 `x ∉ compl U A`
- 如果 `x ∉ A`，則 `x ∈ compl U A`（因為 `x ∈ U`）
- 這兩個條件矛盾，所以 `x ∈ A`

#### 第二個方向：`x ∈ A → x ∈ compl U (compl U A)`

**目標：** 證明如果 `x ∈ A`，則 `x ∈ compl U (compl U A)`

**步驟 1：應用子集合關係**
- `hA_subset_U hx_A`：因為 `A ⊆ U` 且 `x ∈ A`，所以 `x ∈ U`
- 現在我們有：`x ∈ U` 和 `x ∈ A`

**步驟 2：證明 `x ∉ compl U A`**
- 要證明 `x ∈ compl U (compl U A)`，需要 `x ∈ U` 和 `x ∉ compl U A`
- 我們已經有 `x ∈ U`，現在需要證明 `x ∉ compl U A`
- 使用 `have hx_not_compl : x ∉ compl U A := by` 開始證明

**步驟 3：使用反證法證明 `x ∉ compl U A`**
- `by_contra hx_in_compl`：假設 `x ∈ compl U A`（要證明 `x ∉ compl U A`，所以假設其否定）
- 目標：推出矛盾

**步驟 4：分解補集合成員關係**
- `(mem_compl U A x).mp hx_in_compl`：將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
- 現在我們有：`x ∉ A`（從 `h2.right`）

**步驟 5：推出矛盾**
- 我們有：`x ∉ A`（從 `h2.right`）
- 我們有：`x ∈ A`（從 `hx_A`）
- 這兩個命題矛盾
- 因此 `x ∉ compl U A` 成立

**步驟 6：構造補集合成員關係**
- 現在我們有：`x ∈ U` 和 `x ∉ compl U A`
- 使用 `(mem_compl U (compl U A) x).mpr ⟨hx_in_U, hx_not_compl⟩` 構造 `x ∈ compl U (compl U A)`

**關鍵理解：**
- 如果 `x ∈ A`，則 `x ∉ compl U A`（因為補集合的元素都不在 `A` 中）
- 因此 `x ∈ compl U (compl U A)`（因為 `x ∈ U` 且 `x ∉ compl U A`）

**為什麼這個定理很重要？**

1. **展示補集合的雙重否定性質**：
   - 它告訴我們，對一個集合取兩次補集合會回到原集合
   - 這類似於邏輯中的雙重否定：`¬¬P = P`

2. **實際應用**：
   - 當我們需要證明 `A = B` 時，可以改為證明 `(Aᶜ)ᶜ = (Bᶜ)ᶜ`
   - 這在處理補集合相關的證明時很有用

3. **直觀理解**：
   - 補集合是「反面」，取兩次反面就回到正面
   - 如果 `A` 是「滿足某性質的集合」，那麼 `Aᶜ` 是「不滿足該性質的集合」，`(Aᶜ)ᶜ` 又是「滿足該性質的集合」，即 `A`

**關鍵技巧總結：**

1. **外延性公理的使用**：
   - 證明集合相等時，使用 `apply ZFSet.ext`
   - 轉換為證明所有元素的成員關係等價

2. **反證法的使用**：
   - 兩個方向都使用反證法
   - 第一個方向：假設 `x ∉ A`，推出 `x ∈ compl U A`，與 `x ∉ compl U A` 矛盾
   - 第二個方向：假設 `x ∈ compl U A`，推出 `x ∉ A`，與 `x ∈ A` 矛盾

3. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

4. **子集合關係的應用**：
   - `hA_subset_U : A ⊆ U` 可以應用到 `x ∈ A` 得到 `x ∈ U`
   - 這是證明第二個方向的關鍵

**記憶要點：**
- `(Aᶜ)ᶜ = A` 展示了補集合的雙重否定性質
- 證明時需要使用外延性公理和反證法
- 兩個方向都使用反證法來證明否定命題
- 需要假設 `A ⊆ U` 來確保 `x ∈ A` 時有 `x ∈ U`
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`

---

## 常用技巧總結

本節總結一些在證明中常用的通用技巧。關於集合運算的 `.mp` 和 `.mpr` 詳細說明，請參見「集合運算的證明」部分。

### 1. `.mp` 和 `.mpr` - 等價關係的方向轉換

**基本概念：**

在 Lean 中，當有一個等價關係 `P ↔ Q`（雙條件）時，我們可以使用 `.mp` 和 `.mpr` 來提取不同方向的蘊含：

- **`.mp`**：**M**odus **P**onens，從左到右使用等價關係
  - 如果 `h : P ↔ Q`，則 `h.mp : P → Q`
  - 含義：從 `P` 推出 `Q`
  - 用於「分解」：將等價關係的左邊轉換為右邊

- **`.mpr`**：**M**odus **P**onens **R**everse，從右到左使用等價關係
  - 如果 `h : P ↔ Q`，則 `h.mpr : Q → P`
  - 含義：從 `Q` 推出 `P`
  - 用於「構造」：將等價關係的右邊轉換為左邊

**記憶技巧：**
- `.mp` = "正向"（從左到右）
- `.mpr` = "反向"（從右到左）

**在集合運算中的應用：**

```lean
-- 聯集
ZFSet.mem_union.mp   -- x ∈ A ∪ B → x ∈ A ∨ x ∈ B
ZFSet.mem_union.mpr  -- x ∈ A ∨ x ∈ B → x ∈ A ∪ B

-- 交集
ZFSet.mem_inter.mp   -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B
ZFSet.mem_inter.mpr  -- x ∈ A ∧ x ∈ B → x ∈ A ∩ B

-- 差集合（使用自定義的 mem_diff）
(mem_diff A B x).mp   -- x ∈ A - B → x ∈ A ∧ x ∉ B
(mem_diff A B x).mpr  -- x ∈ A ∧ x ∉ B → x ∈ A - B

-- 冪集合
ZFSet.mem_powerset.mp   -- x ∈ 𝒫(A) → x ⊆ A
ZFSet.mem_powerset.mpr  -- x ⊆ A → x ∈ 𝒫(A)
```

**詳細說明請參見：**
- 聯集的 `.mp` 和 `.mpr`：參見「集合運算的證明」→「3. 聯集（`∪`）」
- 交集的 `.mp` 和 `.mpr`：參見「集合運算的證明」→「4. 交集（`∩`）」

### 2. `.left` 和 `.right`

**類型签名：**
```lean
ZFSet.mem_union : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

ZFSet.mem_union.mp   : x ∈ A ∪ B → x ∈ A ∨ x ∈ B  -- 从聯集成員關係推出析取
ZFSet.mem_union.mpr  : x ∈ A ∨ x ∈ B → x ∈ A ∪ B  -- 从析取推出聯集成員關係
```

**詳細说明：**

`ZFSet.mem_union` 是一個等价关系，表示：
- `x ∈ A ∪ B`（x 是 A 和 B 的聯集的成员）
- 當且仅當
- `x ∈ A ∨ x ∈ B`（x 属于 A 或 x 属于 B）

**`ZFSet.mem_union.mpr` 的作用：**

`ZFSet.mem_union.mpr` 將析取（`∨`）轉換為聯集成員關係（`∈ A ∪ B`）。

**使用場景：**

當我们需要證明 `x ∈ A ∪ B` 時，通常的步驟是：

1. **構造析取**：先證明 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ A`，用 `Or.inl hx` 構造 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ B`，用 `Or.inr hx` 構造 `x ∈ A ∨ x ∈ B`

2. **轉換為聯集**：使用 `ZFSet.mem_union.mpr` 將析取轉換為聯集成員關係
   - `ZFSet.mem_union.mpr (Or.inl hx)` 或
   - `ZFSet.mem_union.mpr (Or.inr hx)`

**完整範例：**

```lean
theorem example_union_left (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 步驟 1：構造析取 x ∈ A ∨ x ∈ B
  have h_or : x ∈ A ∨ x ∈ B := Or.inl hx  -- 用 Or.inl 選擇左分支
  -- 步驟 2：轉換為聯集成員關係
  exact ZFSet.mem_union.mpr h_or
  -- 或者直接写成：
  -- exact ZFSet.mem_union.mpr (Or.inl hx)
```

**常見模式：**

```lean
-- 模式 1：x ∈ A → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inl hx)  -- hx : x ∈ A

-- 模式 2：x ∈ B → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inr hx)  -- hx : x ∈ B

-- 模式 3：在分情況討論中使用
cases h with
| inl hx => exact ZFSet.mem_union.mpr (Or.inl hx)  -- 情況1：x ∈ A
| inr hx => exact ZFSet.mem_union.mpr (Or.inr hx)  -- 情況2：x ∈ B
```

**`ZFSet.mem_union.mp` 的作用（反向）：**

`ZFSet.mem_union.mp` 將聯集成員關係轉換為析取：

```lean
theorem example_union_mp (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h  -- h : x ∈ A ∪ B
  exact ZFSet.mem_union.mp h  -- 轉換為 x ∈ A ∨ x ∈ B
```

**其他集合運算的類似用法：**

```lean
-- 交集
ZFSet.mem_inter.mp   -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B
ZFSet.mem_inter.mpr  -- x ∈ A ∧ x ∈ B → x ∈ A ∩ B

-- 差集合（使用自定義的 mem_diff）
(mem_diff A B x).mp   -- x ∈ A - B → x ∈ A ∧ x ∉ B
(mem_diff A B x).mpr  -- x ∈ A ∧ x ∉ B → x ∈ A - B

-- 冪集合
ZFSet.mem_powerset.mp   -- x ∈ 𝒫(A) → x ⊆ A
ZFSet.mem_powerset.mpr  -- x ⊆ A → x ∈ 𝒫(A)
```

**關鍵理解：**

1. **`.mpr` 用于"構造"**：當我们有析取（`x ∈ A ∨ x ∈ B`）時，用 `.mpr` 轉換為聯集成員關係（`x ∈ A ∪ B`）

2. **`.mp` 用于"分解"**：當我们有聯集成員關係（`x ∈ A ∪ B`）時，用 `.mp` 轉換為析取（`x ∈ A ∨ x ∈ B`）

3. **配合 `Or.inl` 和 `Or.inr` 使用**：
   - 先構造析取：`Or.inl hx` 或 `Or.inr hx`
   - 再轉換為聯集：`ZFSet.mem_union.mpr (Or.inl hx)`

**實際應用範例（聯集交换律）：**

```lean
theorem thm_2_2_1_i (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，這是 x ∈ B ∨ x ∈ A 的右分支
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 .mpr 轉換為聯集
  | inr hx =>  -- hx : x ∈ B
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，這是 x ∈ B ∨ x ∈ A 的左分支
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 .mpr 轉換為聯集
```

**總結：**

- `ZFSet.mem_union.mpr` 是證明 `x ∈ A ∪ B` 的關鍵工具
- 它需要配合 `Or.inl` 或 `Or.inr` 使用
- 記住：先構造析取，再用 `.mpr` 轉換為聯集成員關係

#### 1.3 `ZFSet.mem_inter` 詳解

**類型簽名：**
```lean
ZFSet.mem_inter : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B

ZFSet.mem_inter.mp   : x ∈ A ∩ B → x ∈ A ∧ x ∈ B  -- 從交集成員關係推出合取
ZFSet.mem_inter.mpr  : x ∈ A ∧ x ∈ B → x ∈ A ∩ B  -- 從合取推出交集成員關係
```

**詳細說明：**

`ZFSet.mem_inter` 是一個等價關係，表示：
- `x ∈ A ∩ B`（x 是 A 和 B 的交集的成員）
- 當且僅當
- `x ∈ A ∧ x ∈ B`（x 屬於 A 且 x 屬於 B）

**`ZFSet.mem_inter.mp` 的作用：**

`ZFSet.mem_inter.mp` 將交集成員關係（`∈ A ∩ B`）轉換為合取（`∧`）。

**使用場景：**

當我們有 `h : x ∈ A ∩ B` 時，可以使用 `ZFSet.mem_inter.mp` 將其分解為合取：

```lean
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
-- 現在可以使用 h_pair.left : x ∈ A 和 h_pair.right : x ∈ B
```

**完整範例 1：從交集推出單個集合的成員關係**

```lean
theorem example_inter_left (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h  -- h : x ∈ A ∩ B
  -- 步驟 1：將交集成員關係轉換為合取
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  -- 步驟 2：從合取中取出左部分
  exact h_pair.left  -- h_pair.left : x ∈ A
```

**完整範例 2：從交集推出右邊集合的成員關係**

```lean
theorem example_inter_right (A B x : ZFSet) : x ∈ A ∩ B → x ∈ B := by
  intro h  -- h : x ∈ A ∩ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.right  -- h_pair.right : x ∈ B
```

**`ZFSet.mem_inter.mpr` 的作用：**

`ZFSet.mem_inter.mpr` 將合取（`∧`）轉換為交集成員關係（`∈ A ∩ B`）。

**使用場景：**

當我們需要證明 `x ∈ A ∩ B` 時，通常的步驟是：

1. **證明合取**：先證明 `x ∈ A ∧ x ∈ B`
   - 如果 `hxA : x ∈ A` 且 `hxB : x ∈ B`，用 `⟨hxA, hxB⟩` 構造 `x ∈ A ∧ x ∈ B`

2. **轉換為交集**：使用 `ZFSet.mem_inter.mpr` 將合取轉換為交集成員關係
   - `ZFSet.mem_inter.mpr ⟨hxA, hxB⟩`

**完整範例 3：從兩個成員關係推出交集**

```lean
theorem example_inter_mpr (A B x : ZFSet) : (x ∈ A ∧ x ∈ B) → x ∈ A ∩ B := by
  intro h  -- h : x ∈ A ∧ x ∈ B
  -- 直接使用 .mpr 轉換為交集成員關係
  exact ZFSet.mem_inter.mpr h
```

**完整範例 4：從兩個獨立的假設構造交集**

```lean
theorem example_inter_construct (A B x : ZFSet) : (x ∈ A) → (x ∈ B) → x ∈ A ∩ B := by
  intro hxA hxB  -- hxA : x ∈ A, hxB : x ∈ B
  -- 步驟 1：構造合取 x ∈ A ∧ x ∈ B
  have h_pair : x ∈ A ∧ x ∈ B := ⟨hxA, hxB⟩
  -- 步驟 2：轉換為交集成員關係
  exact ZFSet.mem_inter.mpr h_pair
  -- 或者直接寫成：
  -- exact ZFSet.mem_inter.mpr ⟨hxA, hxB⟩
```

**常見模式：**

```lean
-- 模式 1：從交集分解出左邊
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
exact h_pair.left  -- 得到 x ∈ A

-- 模式 2：從交集分解出右邊
have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
exact h_pair.right  -- 得到 x ∈ B

-- 模式 3：從兩個成員關係構造交集
exact ZFSet.mem_inter.mpr ⟨hxA, hxB⟩  -- hxA : x ∈ A, hxB : x ∈ B

-- 模式 4：在證明中使用
have h_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨hxA, hxB⟩
```

**實際應用範例（交集交換律）：**

```lean
theorem thm_2_2_1_j (A B x : ZFSet) : x ∈ A ∩ B → x ∈ B ∩ A := by
  intro h  -- h : x ∈ A ∩ B
  -- 步驟 1：將 x ∈ A ∩ B 轉換為 x ∈ A ∧ x ∈ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  -- 步驟 2：交換順序，構造 x ∈ B ∧ x ∈ A
  have h_pair_swap : x ∈ B ∧ x ∈ A := ⟨h_pair.right, h_pair.left⟩
  -- 步驟 3：轉換為 x ∈ B ∩ A
  exact ZFSet.mem_inter.mpr h_pair_swap
  -- 或者更簡潔地寫成：
  -- exact ZFSet.mem_inter.mpr ⟨(ZFSet.mem_inter.mp h).right, (ZFSet.mem_inter.mp h).left⟩
```

**關鍵理解：**

1. **`.mp` 用於"分解"**：當我們有交集成員關係（`x ∈ A ∩ B`）時，用 `.mp` 轉換為合取（`x ∈ A ∧ x ∈ B`），然後可以使用 `.left` 或 `.right` 提取單個成員關係

2. **`.mpr` 用於"構造"**：當我們有合取（`x ∈ A ∧ x ∈ B`）時，用 `.mpr` 轉換為交集成員關係（`x ∈ A ∩ B`）

3. **配合合取構造使用**：
   - 構造合取：`⟨hxA, hxB⟩`（其中 `hxA : x ∈ A`，`hxB : x ∈ B`）
   - 轉換為交集：`ZFSet.mem_inter.mpr ⟨hxA, hxB⟩`

4. **與聯集的對比**：
   - 聯集使用析取（`∨`）和 `Or.inl`/`Or.inr`
   - 交集使用合取（`∧`）和 `⟨...⟩` 構造

**總結：**

- `ZFSet.mem_inter.mp` 用於分解交集成員關係，提取單個集合的成員關係
- `ZFSet.mem_inter.mpr` 用於構造交集成員關係，需要同時證明元素屬於兩個集合
- 記住：交集需要兩個條件都成立（合取），而聯集只需要一個條件成立（析取）

### 2. `.left` 和 `.right`

从合取命題中提取左右部分：
```lean
h.left   -- 如果 h : P ∧ Q，則 h.left : P
h.right  -- 如果 h : P ∧ Q，則 h.right : Q
```

### 3. `.symm`

等式的对称形式：
```lean
h.symm  -- 如果 h : A = B，則 h.symm : B = A
```

### 4. `False.elim`

从矛盾推出任何结论：
```lean
False.elim 矛盾  -- 从 False 推出任何類型
```

### 5. `rfl` / `rfl`

自反性，用于證明 `x = x`：
```lean
rfl  -- 證明任何 x = x
```

---

## 練習建議

1. **從簡單開始**：先理解 `intro`、`exact`、`have` 等基础策略
2. **逐步增加複雜度**：學習 `rcases`、`constructor`、`apply` 等
3. **理解邏輯連接詞**：掌握 `∧`、`∨`、`→`、`↔`、`¬` 的處理方法
4. **熟悉集合運算**：理解子集合、聯集、交集、差集合的定義和使用
5. **練習常見模式**：傳遞性、外延性、反證法等

---

## 參考資料

- [Lean 4 官方檔案](https://leanprover-community.github.io/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib 檔案](https://leanprover-community.github.io/mathlib4_docs/)

---

**祝學習愉快！** 🎓

