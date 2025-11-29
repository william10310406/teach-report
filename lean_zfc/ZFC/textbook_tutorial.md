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
7. [有序對與笛卡爾積](#有序對與笛卡爾積)
8. [集合族的聯集與交集](#集合族的聯集與交集)
9. [常用技巧總結](#常用技巧總結)

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

**作用：** `exact` 是 Lean 中最直接的證明策略。當你已經有一個表達式，它的類型正好等於當前的證明目標時，可以使用 `exact` 直接完成證明。

**核心概念：**
- `exact` 要求提供的表達式**完全匹配**目標的類型
- 如果表達式的類型與目標類型完全一致，證明就完成了
- 這是最簡單、最直接的證明方式

**語法：**
```lean
exact 表達式
```

**什麼時候使用 `exact`？**

1. **當假設正好是目標時**：
   ```lean
   theorem example1 (A B : ZFSet) : (A ⊆ B) → (A ⊆ B) := by
     intro h  -- 引入前提 A ⊆ B 作為假設 h
     exact h   -- h 的類型正好是目標 A ⊆ B，直接使用
   ```

2. **當目標是某個假設的一部分時**：
   ```lean
   theorem example2 (A : ZFSet) : A ⊆ A := by
     intro x hx  -- 目標變成：證明 x ∈ A
     exact hx     -- hx : x ∈ A 正好是目標，直接使用
   ```

3. **當目標是通過構造函數得到的合取或析取時**：
   ```lean
   theorem example3 (A B : ZFSet) (hA : A ⊆ B) (hB : B ⊆ A) : A = B := by
     apply ZFSet.ext
     intro x
     constructor
     · exact hA  -- hA : A ⊆ B，可以應用到 x ∈ A 得到 x ∈ B
     · exact hB  -- hB : B ⊆ A，可以應用到 x ∈ B 得到 x ∈ A
   ```

4. **當目標是通過 `have` 建立的中間結果時**：
   ```lean
   theorem example4 (A B C : ZFSet) : A ⊆ B → A ⊆ C := by
     intro hAB
     have hBC : B ⊆ C := sorry  -- 假設我們已經證明了 B ⊆ C
     intro x hx_A
     have hx_B : x ∈ B := hAB hx_A  -- 因為 A ⊆ B 且 x ∈ A，所以 x ∈ B
     exact hBC hx_B  -- hBC hx_B 的類型是 x ∈ C，正好是目標
   ```

**`exact` vs `apply` 的區別：**

- **`exact`**：表達式的類型必須**完全匹配**目標類型
  ```lean
  -- 目標：x ∈ B
  -- h : x ∈ B
  exact h  -- ✅ 完全匹配，直接完成
  ```

- **`apply`**：表達式的類型是目標類型的**函數**，需要應用後才能匹配
  ```lean
  -- 目標：x ∈ B
  -- h : A ⊆ B
  apply h  -- ✅ h 是函數類型，應用後得到 x ∈ B
  -- 現在需要證明：x ∈ A
  ```

**常見錯誤：**

1. **類型不匹配**：
   ```lean
   -- 目標：x ∈ B
   -- h : x ∈ A
   exact h  -- ❌ 錯誤：類型不匹配，x ∈ A ≠ x ∈ B
   ```

2. **缺少參數**：
   ```lean
   -- 目標：x ∈ B
   -- h : A ⊆ B
   exact h  -- ❌ 錯誤：h 是函數類型，需要參數
   -- 應該使用：exact h hx_A（其中 hx_A : x ∈ A）
   ```

**實際範例：**

```lean
theorem example5 (A B : ZFSet) : A ⊆ A := by
  intro x hx  -- 引入任意元素 x 和假設 x ∈ A
  -- 目標：證明 x ∈ A
  exact hx    -- hx 的類型正好是 x ∈ A，直接完成證明
```

**詳細說明：**
- 開始時目標是 `A ⊆ A`，即 `∀ x, x ∈ A → x ∈ A`
- `intro x hx` 引入 `x` 和 `hx : x ∈ A`，目標變成 `x ∈ A`
- `exact hx` 直接使用假設 `hx`，因為它的類型正好是目標 `x ∈ A`

**記憶要點：**
- `exact` 用於當表達式的類型**完全匹配**目標時
- 如果類型不匹配，需要使用 `apply`、`rw` 或其他策略
- `exact` 是最簡單的證明方式，但要求類型完全一致
- 當目標是假設本身或假設的直接應用結果時，通常可以使用 `exact`

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

### 範例 11：聯集與補集合的關係

**定理：** `A ∪ Aᶜ = U`，即 `A ∪ compl U A = U`

這個定理說明了一個集合和它的補集合的聯集等於全域集合。這是一個重要的補集合性質，展示了補集合的「完整性」：任何元素要麼在 `A` 中，要麼在 `Aᶜ` 中（相對於全域集合 `U`）。

這個證明展示了：
- 如何使用 `cases` 處理析取（`∨`）
- 如何使用 `by_cases` 進行分情況討論
- 如何使用管道操作符 `|>` 簡化表達式
- 如何結合補集合的定義和子集合關係

**完整證明：**

```lean
theorem theorem_2_2_2_b (U A : ZFSet) (hA_subset_U : A ⊆ U) : A ∪ compl U A = U := by
  apply ZFSet.ext -- 根據外延性公設，將 A ∪ compl U A = U 轉換為 ∀ x, x ∈ A ∪ compl U A ↔ x ∈ U
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_union -- hx_union : x ∈ A ∪ compl U A
    -- x ∈ A ∪ compl U A → x ∈ U
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ A ∪ compl U A 拆成 x ∈ A ∨ x ∈ compl U A
    cases hx_union with
    | inl hx_A => exact hA_subset_U hx_A -- 情況1：x ∈ A，因為 A ⊆ U，所以 x ∈ U
    | inr hx_compl => exact (mem_compl U A x).mp hx_compl |>.left -- 情況2：x ∈ compl U A，根據 mem_compl 得到 x ∈ U ∧ x ∉ A，提取 x ∈ U
  · intro hx_U -- hx_U : x ∈ U
    -- x ∈ U → x ∈ A ∪ compl U A
    by_cases hx_A : x ∈ A -- 分情況：x ∈ A 或 x ∉ A
    · exact ZFSet.mem_union.mpr (Or.inl hx_A) -- 情況1：x ∈ A，所以 x ∈ A ∪ compl U A（用 Or.inl 選擇左分支）
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_compl U A x).mpr ⟨hx_U, hx_A⟩)) -- 情況2：x ∉ A，因為 x ∈ U ∧ x ∉ A，所以 x ∈ compl U A，因此 x ∈ A ∪ compl U A
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ A ∪ compl U A → x ∈ U`

**目標：** 證明如果 `x ∈ A ∪ compl U A`，則 `x ∈ U`

**步驟 1：分解聯集成員關係**
- `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ A ∪ compl U A` 轉換為 `x ∈ A ∨ x ∈ compl U A`
- 現在我們需要處理這個析取（`∨`）

**步驟 2：使用 `cases` 處理析取**
- `cases hx_union with`：將析取分成兩個情況
- `| inl hx_A`：情況 1，`x ∈ A`
- `| inr hx_compl`：情況 2，`x ∈ compl U A`

**步驟 3：處理情況 1（`x ∈ A`）**
- `hx_A : x ∈ A`：我們有 `x ∈ A`
- `hA_subset_U hx_A`：因為 `A ⊆ U` 且 `x ∈ A`，所以 `x ∈ U`
- 這完成了情況 1 的證明

**步驟 4：處理情況 2（`x ∈ compl U A`）**
- `hx_compl : x ∈ compl U A`：我們有 `x ∈ compl U A`
- `(mem_compl U A x).mp hx_compl`：根據補集合的定義，將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
- `|>.left`：使用管道操作符提取合取（`∧`）的左側部分，即 `x ∈ U`
- 這完成了情況 2 的證明

**關鍵理解：**
- 如果 `x ∈ A`，因為 `A ⊆ U`，所以 `x ∈ U`
- 如果 `x ∈ compl U A`，根據補集合的定義，`x ∈ U ∧ x ∉ A`，所以 `x ∈ U`
- 無論哪種情況，都有 `x ∈ U`

#### 第二個方向：`x ∈ U → x ∈ A ∪ compl U A`

**目標：** 證明如果 `x ∈ U`，則 `x ∈ A ∪ compl U A`

**步驟 1：分情況討論**
- `by_cases hx_A : x ∈ A`：將問題分成兩個情況：`x ∈ A` 或 `x ∉ A`
- 這是經典的「要麼在集合中，要麼不在集合中」的邏輯

**步驟 2：處理情況 1（`x ∈ A`）**
- `hx_A : x ∈ A`：我們有 `x ∈ A`
- `Or.inl hx_A`：構造析取 `x ∈ A ∨ x ∈ compl U A` 的左分支
- `ZFSet.mem_union.mpr (Or.inl hx_A)`：將析取轉換為聯集成員關係 `x ∈ A ∪ compl U A`
- 這完成了情況 1 的證明

**步驟 3：處理情況 2（`x ∉ A`）**
- `hx_A : x ∉ A`：我們有 `x ∉ A`（注意這裡 `hx_A` 是 `¬(x ∈ A)`）
- `hx_U : x ∈ U`：我們有 `x ∈ U`
- `⟨hx_U, hx_A⟩`：構造合取 `x ∈ U ∧ x ∉ A`
- `(mem_compl U A x).mpr ⟨hx_U, hx_A⟩`：根據補集合的定義，將 `x ∈ U ∧ x ∉ A` 轉換為 `x ∈ compl U A`
- `Or.inr ...`：構造析取 `x ∈ A ∨ x ∈ compl U A` 的右分支
- `ZFSet.mem_union.mpr (Or.inr ...)`：將析取轉換為聯集成員關係 `x ∈ A ∪ compl U A`
- 這完成了情況 2 的證明

**關鍵理解：**
- 如果 `x ∈ A`，則 `x ∈ A ∪ compl U A`（因為 `x` 在聯集的左側）
- 如果 `x ∉ A` 且 `x ∈ U`，則 `x ∈ compl U A`，所以 `x ∈ A ∪ compl U A`（因為 `x` 在聯集的右側）
- 無論哪種情況，都有 `x ∈ A ∪ compl U A`

**為什麼這個定理很重要？**

1. **展示補集合的完整性**：
   - 它告訴我們，任何元素（相對於全域集合 `U`）要麼在 `A` 中，要麼在 `Aᶜ` 中
   - 這類似於邏輯中的排中律：`P ∨ ¬P`

2. **實際應用**：
   - 當我們需要證明某個元素屬於全域集合時，可以證明它屬於 `A` 或 `Aᶜ`
   - 這在處理補集合相關的證明時很有用

3. **直觀理解**：
   - 補集合是「反面」，一個集合和它的反面合起來就是全部
   - 如果 `A` 是「滿足某性質的集合」，那麼 `Aᶜ` 是「不滿足該性質的集合」，兩者的聯集就是所有可能的元素

**關鍵技巧總結：**

1. **`cases` 的使用**：
   - 當我們有析取（`∨`）時，使用 `cases` 分成兩個情況
   - `inl` 表示左分支，`inr` 表示右分支

2. **`by_cases` 的使用**：
   - 當我們需要分情況討論時，使用 `by_cases`
   - 這會自動處理兩種情況：命題成立和命題不成立

3. **管道操作符 `|>` 的使用**：
   - `|>` 是 Lean 4 的管道操作符，類似於函數式編程中的管道
   - `expr |> f` 等價於 `f expr`
   - `expr |> f |> g` 等價於 `g (f expr)`
   - 在這個證明中，`(mem_compl U A x).mp hx_compl |>.left` 等價於 `((mem_compl U A x).mp hx_compl).left`
   - 這讓代碼更易讀，因為我們可以「從左到右」閱讀：先應用 `.mp`，然後提取 `.left`

4. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

5. **子集合關係的應用**：
   - `hA_subset_U : A ⊆ U` 可以應用到 `x ∈ A` 得到 `x ∈ U`
   - 這是證明第一個方向的關鍵

**關於 `|>.left` 語法的詳細解釋：**

`|>` 是 Lean 4 的**管道操作符**（pipe operator），它允許我們以更直觀的方式鏈式調用函數。

**基本語法：**
```lean
expr |> f        -- 等價於 f expr
expr |> f |> g   -- 等價於 g (f expr)
```

**在我們的證明中：**
```lean
(mem_compl U A x).mp hx_compl |>.left
```

**等價寫法：**
```lean
((mem_compl U A x).mp hx_compl).left
```

**逐步分解：**
1. `mem_compl U A x`：補集合的定義，類型為 `x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
2. `(mem_compl U A x).mp`：提取左到右的方向，類型為 `x ∈ compl U A → x ∈ U ∧ x ∉ A`
3. `(mem_compl U A x).mp hx_compl`：應用函數，得到 `x ∈ U ∧ x ∉ A`（類型為合取）
4. `|>.left`：提取合取的左側部分，得到 `x ∈ U`

**為什麼使用 `|>`？**

1. **可讀性**：`expr |> f |> g` 比 `g (f expr)` 更容易閱讀，因為我們可以「從左到右」閱讀
2. **鏈式調用**：當有多個函數調用時，`|>` 讓代碼更清晰
3. **函數式風格**：這是函數式編程的常見模式

**更多範例：**
```lean
-- 範例 1：簡單的管道
hx |>.left  -- 等價於 hx.left

-- 範例 2：鏈式管道
hx |> f |>.left |>.right  -- 等價於 (f hx).left.right

-- 範例 3：在我們的證明中
(mem_compl U A x).mp hx_compl |>.left
-- 等價於
((mem_compl U A x).mp hx_compl).left
```

**記憶要點：**
- `A ∪ Aᶜ = U` 展示了補集合的完整性
- 證明時需要使用外延性公理、`cases` 和 `by_cases`
- 第一個方向：如果 `x ∈ A ∪ compl U A`，則 `x ∈ U`（兩種情況）
- 第二個方向：如果 `x ∈ U`，則 `x ∈ A ∪ compl U A`（兩種情況）
- 需要假設 `A ⊆ U` 來確保 `x ∈ A` 時有 `x ∈ U`
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- `|>` 是管道操作符，`expr |> f` 等價於 `f expr`
- `|>.left` 提取合取的左側部分

---

### 範例 12：交集與補集合的關係

**定理：** `A ∩ Aᶜ = ∅`，即 `A ∩ compl U A = ∅`

這個定理說明了一個集合和它的補集合的交集是空集合。這是一個重要的補集合性質，展示了補集合的「互斥性」：任何元素不能同時在 `A` 中和 `Aᶜ` 中。

這個證明展示了：
- 如何使用反證法推出矛盾
- 如何結合交集的定義和補集合的定義
- 如何使用 `False.elim` 從矛盾推出任何命題
- 如何處理空真命題（從 `x ∈ ∅` 推出任何命題）

**完整證明：**

```lean
theorem theorem_2_2_2_c (U A : ZFSet) : A ∩ compl U A = ∅ := by
  apply ZFSet.ext -- 根據外延性公設，將 A ∩ compl U A = ∅ 轉換為 ∀ x, x ∈ A ∩ compl U A ↔ x ∈ ∅
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_inter -- hx_inter : x ∈ A ∩ compl U A
    -- x ∈ A ∩ compl U A → x ∈ ∅
    have hx_pair : x ∈ A ∧ x ∈ compl U A := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ compl U A 拆成 x ∈ A ∧ x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_pair.right -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    have h_contra : False := h_temp.right hx_pair.left -- 矛盾：x ∉ A（從 h_temp.right）和 x ∈ A（從 hx_pair.left)
    exact False.elim (ZFSet.notMem_empty x (False.elim h_contra)) -- 從 False 推出 x ∈ ∅，然後用 notMem_empty 推出矛盾
  · intro hx_empty -- hx_empty : x ∈ ∅
    -- x ∈ ∅ → x ∈ A ∩ compl U A（空真命題）
    exact False.elim (ZFSet.notMem_empty x hx_empty)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ A ∩ compl U A → x ∈ ∅`

**目標：** 證明如果 `x ∈ A ∩ compl U A`，則 `x ∈ ∅`

**步驟 1：分解交集成員關係**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ A ∩ compl U A` 轉換為 `x ∈ A ∧ x ∈ compl U A`
- 現在我們有：`x ∈ A` 和 `x ∈ compl U A`

**步驟 2：分解補集合成員關係**
- `(mem_compl U A x).mp hx_pair.right`：將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
- 現在我們有：`x ∈ U` 和 `x ∉ A`

**步驟 3：推出矛盾**
- `h_temp.right : x ∉ A`：我們有 `x ∉ A`
- `hx_pair.left : x ∈ A`：我們有 `x ∈ A`
- `h_temp.right hx_pair.left`：將 `x ∉ A` 應用到 `x ∈ A`，得到 `False`
- 這兩個命題矛盾

**步驟 4：從矛盾推出目標**
- `False.elim h_contra`：從 `False` 可以推出任何命題，包括 `x ∈ ∅`
- `ZFSet.notMem_empty x (False.elim h_contra)`：但 `x ∈ ∅` 是不可能的（空集合沒有元素），所以又推出 `False`
- 這完成了第一個方向的證明

**關鍵理解：**
- 如果 `x ∈ A ∩ compl U A`，則 `x ∈ A` 且 `x ∈ compl U A`
- 從 `x ∈ compl U A` 得到 `x ∉ A`
- 這與 `x ∈ A` 矛盾
- 因此 `x ∈ A ∩ compl U A` 是不可能的，所以 `A ∩ compl U A = ∅`

#### 第二個方向：`x ∈ ∅ → x ∈ A ∩ compl U A`

**目標：** 證明如果 `x ∈ ∅`，則 `x ∈ A ∩ compl U A`

**步驟：使用空真命題**
- `hx_empty : x ∈ ∅`：我們有 `x ∈ ∅`
- `ZFSet.notMem_empty x hx_empty`：但空集合沒有元素，所以 `x ∈ ∅` 是不可能的，推出 `False`
- `False.elim ...`：從 `False` 可以推出任何命題，包括 `x ∈ A ∩ compl U A`
- 這完成了第二個方向的證明

**關鍵理解：**
- 這是一個**空真命題**（vacuous truth）
- 因為 `x ∈ ∅` 永遠為假，所以從它推出任何命題都是真的
- 這是邏輯中的一個重要概念：從假命題可以推出任何命題

**為什麼這個定理很重要？**

1. **展示補集合的互斥性**：
   - 它告訴我們，任何元素不能同時在 `A` 中和 `Aᶜ` 中
   - 這類似於邏輯中的矛盾律：`P ∧ ¬P` 永遠為假

2. **實際應用**：
   - 當我們需要證明某個交集是空集合時，可以證明它的元素會導致矛盾
   - 這在處理補集合相關的證明時很有用

3. **直觀理解**：
   - 補集合是「反面」，一個集合和它的反面沒有共同元素
   - 如果 `A` 是「滿足某性質的集合」，那麼 `Aᶜ` 是「不滿足該性質的集合」，兩者沒有交集

**關鍵技巧總結：**

1. **交集的分解**：
   - 使用 `ZFSet.mem_inter.mp` 分解交集成員關係
   - 將 `x ∈ A ∩ B` 轉換為 `x ∈ A ∧ x ∈ B`

2. **補集合的分解**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`

3. **矛盾的構造**：
   - 當我們有 `x ∈ A` 和 `x ∉ A` 時，可以構造矛盾
   - 使用 `h_temp.right hx_pair.left` 將 `x ∉ A` 應用到 `x ∈ A`，得到 `False`

4. **`False.elim` 的使用**：
   - 從 `False` 可以推出任何命題
   - `False.elim h_contra : P` 表示從 `False` 推出命題 `P`
   - 這是邏輯中的「爆炸原理」（principle of explosion）

5. **空真命題**：
   - 從假命題可以推出任何命題
   - `x ∈ ∅` 永遠為假，所以從它推出任何命題都是真的
   - 這是證明第二個方向的關鍵

**關於 `False.elim` 的詳細解釋：**

`False.elim` 是 Lean 中的一個重要工具，它允許我們從矛盾推出任何命題。

**基本語法：**
```lean
False.elim h : P  -- 如果 h : False，則可以推出任何命題 P
```

**在我們的證明中：**
```lean
have h_contra : False := h_temp.right hx_pair.left  -- 構造矛盾
exact False.elim (ZFSet.notMem_empty x (False.elim h_contra))  -- 從 False 推出 x ∈ ∅，然後用 notMem_empty 推出 False
```

**逐步分解：**
1. `h_contra : False`：我們有矛盾
2. `False.elim h_contra : x ∈ ∅`：從 `False` 推出 `x ∈ ∅`（任何命題）
3. `ZFSet.notMem_empty x (False.elim h_contra)`：但 `x ∈ ∅` 是不可能的，所以又推出 `False`
4. `False.elim ...`：從這個 `False` 可以推出目標 `x ∈ A ∩ compl U A`

**為什麼需要兩次 `False.elim`？**

1. **第一次 `False.elim`**：從矛盾 `h_contra : False` 推出 `x ∈ ∅`
   - 這是為了構造 `ZFSet.notMem_empty` 需要的參數類型

2. **第二次 `False.elim`**：從 `ZFSet.notMem_empty` 返回的 `False` 推出目標
   - 這是為了完成證明

**更多範例：**
```lean
-- 範例 1：從矛盾推出任何命題
have h : False := ...
exact False.elim h  -- 可以推出任何命題

-- 範例 2：在我們的證明中
have h_contra : False := h_temp.right hx_pair.left
exact False.elim (ZFSet.notMem_empty x (False.elim h_contra))

-- 範例 3：空真命題
intro hx_empty : x ∈ ∅
exact False.elim (ZFSet.notMem_empty x hx_empty)  -- 從 x ∈ ∅ 推出任何命題
```

**記憶要點：**
- `A ∩ Aᶜ = ∅` 展示了補集合的互斥性
- 證明時需要使用外延性公理和反證法
- 第一個方向：如果 `x ∈ A ∩ compl U A`，則推出矛盾，因此 `x ∈ ∅`
- 第二個方向：從 `x ∈ ∅`（空真命題）推出 `x ∈ A ∩ compl U A`
- 不需要假設 `A ⊆ U`，因為我們直接從 `x ∈ compl U A` 得到所需信息
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- `False.elim` 允許從矛盾推出任何命題
- 空真命題：從假命題可以推出任何命題

---

### 範例 13：差集合與補集合的關係

**定理：** `A - B = A ∩ Bᶜ`，即 `set_diff A B = A ∩ compl U B`

這個定理說明了一個集合與另一個集合的差集合等於該集合與另一個集合的補集合的交集。這是一個重要的集合運算性質，展示了差集合和補集合之間的關係。

這個證明展示了：
- 如何結合差集合、交集和補集合的定義
- 如何使用子集合關係從 `x ∈ A` 推導出 `x ∈ U`
- 如何在不同集合運算之間轉換

**完整證明：**

```lean
theorem theorem_2_2_2_d (U A B : ZFSet) (hA_subset_U : A ⊆ U) : set_diff A B = A ∩ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 set_diff A B = A ∩ compl U B 轉換為 ∀ x, x ∈ set_diff A B ↔ x ∈ A ∩ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_diff -- hx_diff : x ∈ set_diff A B
    -- x ∈ set_diff A B → x ∈ A ∩ compl U B
    have hx_pair : x ∈ A ∧ x ∉ B := (mem_diff A B x).mp hx_diff -- 將 x ∈ set_diff A B 拆成 x ∈ A ∧ x ∉ B
    have hx_in_U : x ∈ U := hA_subset_U hx_pair.left -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
    have hx_compl : x ∈ compl U B := (mem_compl U B x).mpr ⟨hx_in_U, hx_pair.right⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    exact ZFSet.mem_inter.mpr ⟨hx_pair.left, hx_compl⟩ -- 將 x ∈ A ∧ x ∈ compl U B 轉換為 x ∈ A ∩ compl U B
  · intro hx_inter -- hx_inter : x ∈ A ∩ compl U B
    -- x ∈ A ∩ compl U B → x ∈ set_diff A B
    have hx_pair : x ∈ A ∧ x ∈ compl U B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ compl U B 拆成 x ∈ A ∧ x ∈ compl U B
    have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.right -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_B : x ∉ B := h_temp.right -- 從 x ∈ U ∧ x ∉ B 提取 x ∉ B
    exact (mem_diff A B x).mpr ⟨hx_pair.left, hx_not_in_B⟩ -- 將 x ∈ A ∧ x ∉ B 轉換為 x ∈ set_diff A B
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ set_diff A B → x ∈ A ∩ compl U B`

**目標：** 證明如果 `x ∈ set_diff A B`，則 `x ∈ A ∩ compl U B`

**步驟 1：分解差集合成員關係**
- `(mem_diff A B x).mp hx_diff`：將 `x ∈ set_diff A B` 轉換為 `x ∈ A ∧ x ∉ B`
- 現在我們有：`x ∈ A` 和 `x ∉ B`

**步驟 2：應用子集合關係**
- `hA_subset_U hx_pair.left`：因為 `A ⊆ U` 且 `x ∈ A`，所以 `x ∈ U`
- 現在我們有：`x ∈ U` 和 `x ∉ B`

**步驟 3：構造補集合成員關係**
- `(mem_compl U B x).mpr ⟨hx_in_U, hx_pair.right⟩`：將 `x ∈ U ∧ x ∉ B` 轉換為 `x ∈ compl U B`
- 現在我們有：`x ∈ A` 和 `x ∈ compl U B`

**步驟 4：構造交集成員關係**
- `ZFSet.mem_inter.mpr ⟨hx_pair.left, hx_compl⟩`：將 `x ∈ A ∧ x ∈ compl U B` 轉換為 `x ∈ A ∩ compl U B`
- 這完成了第一個方向的證明

**關鍵理解：**
- 如果 `x ∈ set_diff A B`，則 `x ∈ A` 且 `x ∉ B`
- 因為 `A ⊆ U`，所以 `x ∈ U`
- 因此 `x ∈ U ∧ x ∉ B`，即 `x ∈ compl U B`
- 所以 `x ∈ A` 且 `x ∈ compl U B`，即 `x ∈ A ∩ compl U B`

#### 第二個方向：`x ∈ A ∩ compl U B → x ∈ set_diff A B`

**目標：** 證明如果 `x ∈ A ∩ compl U B`，則 `x ∈ set_diff A B`

**步驟 1：分解交集成員關係**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ A ∩ compl U B` 轉換為 `x ∈ A ∧ x ∈ compl U B`
- 現在我們有：`x ∈ A` 和 `x ∈ compl U B`

**步驟 2：分解補集合成員關係**
- `(mem_compl U B x).mp hx_pair.right`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
- 現在我們有：`x ∈ U` 和 `x ∉ B`

**步驟 3：提取 `x ∉ B`**
- `h_temp.right`：從 `x ∈ U ∧ x ∉ B` 提取 `x ∉ B`
- 現在我們有：`x ∈ A` 和 `x ∉ B`

**步驟 4：構造差集合成員關係**
- `(mem_diff A B x).mpr ⟨hx_pair.left, hx_not_in_B⟩`：將 `x ∈ A ∧ x ∉ B` 轉換為 `x ∈ set_diff A B`
- 這完成了第二個方向的證明

**關鍵理解：**
- 如果 `x ∈ A ∩ compl U B`，則 `x ∈ A` 且 `x ∈ compl U B`
- 從 `x ∈ compl U B` 得到 `x ∈ U ∧ x ∉ B`
- 因此 `x ∈ A` 且 `x ∉ B`，即 `x ∈ set_diff A B`

**為什麼這個定理很重要？**

1. **展示差集合和補集合的關係**：
   - 它告訴我們，差集合可以用交集和補集合來表示
   - `A - B = A ∩ Bᶜ` 是一個重要的集合運算恆等式

2. **實際應用**：
   - 當我們需要處理差集合時，可以將其轉換為交集和補集合
   - 這在處理複雜的集合運算時很有用

3. **直觀理解**：
   - `A - B` 是「在 `A` 中但不在 `B` 中的元素」
   - `A ∩ Bᶜ` 是「在 `A` 中且在 `B` 的補集合中的元素」
   - 這兩個描述是等價的

**關鍵技巧總結：**

1. **差集合的分解和構造**：
   - 使用 `mem_diff.mp` 分解差集合成員關係
   - 使用 `mem_diff.mpr` 構造差集合成員關係
   - `x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B`

2. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係
   - `x ∈ compl U B ↔ x ∈ U ∧ x ∉ B`

3. **交集的分解和構造**：
   - 使用 `ZFSet.mem_inter.mp` 分解交集成員關係
   - 使用 `ZFSet.mem_inter.mpr` 構造交集成員關係
   - `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`

4. **子集合關係的應用**：
   - `hA_subset_U : A ⊆ U` 可以應用到 `x ∈ A` 得到 `x ∈ U`
   - 這是證明第一個方向的關鍵

5. **從合取中提取部分**：
   - 使用 `.left` 提取合取的左側部分
   - 使用 `.right` 提取合取的右側部分
   - 例如：`h_temp.right` 從 `x ∈ U ∧ x ∉ B` 提取 `x ∉ B`

**關於差集合和補集合關係的詳細解釋：**

**差集合的定義：**
```lean
x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B
```

**補集合的定義：**
```lean
x ∈ compl U B ↔ x ∈ U ∧ x ∉ B
```

**關係的建立：**
- 如果 `x ∈ set_diff A B`，則 `x ∈ A` 且 `x ∉ B`
- 如果 `A ⊆ U`，則 `x ∈ A` 意味著 `x ∈ U`
- 因此 `x ∈ U ∧ x ∉ B`，即 `x ∈ compl U B`
- 所以 `x ∈ A` 且 `x ∈ compl U B`，即 `x ∈ A ∩ compl U B`

**反過來：**
- 如果 `x ∈ A ∩ compl U B`，則 `x ∈ A` 且 `x ∈ compl U B`
- 從 `x ∈ compl U B` 得到 `x ∈ U ∧ x ∉ B`
- 因此 `x ∈ A` 且 `x ∉ B`，即 `x ∈ set_diff A B`

**記憶要點：**
- `A - B = A ∩ Bᶜ` 展示了差集合和補集合的關係
- 證明時需要使用外延性公理
- 第一個方向：從 `x ∈ set_diff A B` 推導出 `x ∈ A ∩ compl U B`
- 第二個方向：從 `x ∈ A ∩ compl U B` 推導出 `x ∈ set_diff A B`
- 需要假設 `A ⊆ U` 來確保 `x ∈ A` 時有 `x ∈ U`
- 差集合的定義：`x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B`
- 補集合的定義：`x ∈ compl U B ↔ x ∈ U ∧ x ∉ B`
- 交集的定義：`x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`

---

### 範例 14：子集合關係與補集合的對偶性

**定理：** `A ⊆ B ↔ Bᶜ ⊆ Aᶜ`，即 `A ⊆ B ↔ compl U B ⊆ compl U A`

這個定理說明了一個重要的對偶性質：如果 `A` 是 `B` 的子集合，則 `B` 的補集合是 `A` 的補集合的子集合。這是補集合運算的一個基本性質，展示了子集合關係在補集合運算下的「反向」特性。

這個證明展示了：
- 如何使用反證法證明否定命題
- 如何結合子集合關係和補集合的定義
- 如何處理雙向等價關係的證明

**完整證明：**

```lean
theorem theorem_2_2_2_e (U A B : ZFSet) (hA_subset_U : A ⊆ U) (_hB_subset_U : B ⊆ U) : A ⊆ B ↔ compl U B ⊆ compl U A := by
  constructor -- 將 ↔ 分成兩個方向
  · intro hA_B x hx_compl_B -- hA_B : A ⊆ B, x : any arbitrary element, hx_compl_B : x ∈ compl U B
    -- x ∈ compl U B → x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_A : x ∉ A := by -- 證明 x ∉ A
      by_contra hx_in_A -- 假設 x ∈ A（要證明 x ∉ A，所以假設其否定）
      have hx_in_B : x ∈ B := hA_B hx_in_A -- 因為 A ⊆ B 且 x ∈ A，所以 x ∈ B
      exact h_temp.right hx_in_B -- 矛盾：x ∉ B（從 h_temp.right）和 x ∈ B（從 hx_in_B）
    exact (mem_compl U A x).mpr ⟨h_temp.left, hx_not_in_A⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
  · intro h_compl_B_compl_A x hx_A -- h_compl_B_compl_A : compl U B ⊆ compl U A, x : any arbitrary element, hx_A : x ∈ A
    -- x ∈ A → x ∈ B
    have hx_in_U : x ∈ U := hA_subset_U hx_A -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
    by_contra hx_not_in_B -- 假設 x ∉ B（要證明 x ∈ B，所以假設其否定）
    have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    have hx_compl_A : x ∈ compl U A := h_compl_B_compl_A hx_compl_B -- 因為 compl U B ⊆ compl U A 且 x ∈ compl U B，所以 x ∈ compl U A
    have h_temp : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_compl_A -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    exact h_temp.right hx_A -- 矛盾：x ∉ A（從 h_temp.right）和 x ∈ A（從 hx_A）
```

**詳細步驟解析：**

#### 第一個方向：`A ⊆ B → compl U B ⊆ compl U A`

**目標：** 證明如果 `A ⊆ B`，則 `compl U B ⊆ compl U A`

**步驟 1：引入假設**
- `hA_B : A ⊆ B`：我們有 `A ⊆ B`
- `x : any arbitrary element`：任意元素 `x`
- `hx_compl_B : x ∈ compl U B`：假設 `x ∈ compl U B`
- 目標：證明 `x ∈ compl U A`

**步驟 2：分解補集合成員關係**
- `(mem_compl U B x).mp hx_compl_B`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
- 現在我們有：`x ∈ U` 和 `x ∉ B`

**步驟 3：證明 `x ∉ A`（使用反證法）**
- `by_contra hx_in_A`：假設 `x ∈ A`（要證明 `x ∉ A`，所以假設其否定）
- `hA_B hx_in_A`：因為 `A ⊆ B` 且 `x ∈ A`，所以 `x ∈ B`
- `h_temp.right hx_in_B`：矛盾！我們有 `x ∉ B`（從 `h_temp.right`）和 `x ∈ B`（從 `hA_B hx_in_A`）
- 因此 `x ∉ A` 成立

**步驟 4：構造補集合成員關係**
- `(mem_compl U A x).mpr ⟨h_temp.left, hx_not_in_A⟩`：將 `x ∈ U ∧ x ∉ A` 轉換為 `x ∈ compl U A`
- 這完成了第一個方向的證明

**關鍵理解：**
- 如果 `A ⊆ B` 且 `x ∈ compl U B`，則 `x ∉ B`
- 如果 `x ∈ A`，則因為 `A ⊆ B`，所以 `x ∈ B`，但 `x ∉ B`，矛盾
- 因此 `x ∉ A`，所以 `x ∈ compl U A`

#### 第二個方向：`compl U B ⊆ compl U A → A ⊆ B`

**目標：** 證明如果 `compl U B ⊆ compl U A`，則 `A ⊆ B`

**步驟 1：引入假設**
- `h_compl_B_compl_A : compl U B ⊆ compl U A`：我們有 `compl U B ⊆ compl U A`
- `x : any arbitrary element`：任意元素 `x`
- `hx_A : x ∈ A`：假設 `x ∈ A`
- 目標：證明 `x ∈ B`

**步驟 2：應用子集合關係**
- `hA_subset_U hx_A`：因為 `A ⊆ U` 且 `x ∈ A`，所以 `x ∈ U`
- 現在我們有：`x ∈ U` 和 `x ∈ A`

**步驟 3：使用反證法證明 `x ∈ B`**
- `by_contra hx_not_in_B`：假設 `x ∉ B`（要證明 `x ∈ B`，所以假設其否定）
- `(mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩`：將 `x ∈ U ∧ x ∉ B` 轉換為 `x ∈ compl U B`
- `h_compl_B_compl_A hx_compl_B`：因為 `compl U B ⊆ compl U A` 且 `x ∈ compl U B`，所以 `x ∈ compl U A`
- `(mem_compl U A x).mp hx_compl_A`：將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
- `h_temp.right hx_A`：矛盾！我們有 `x ∉ A`（從 `h_temp.right`）和 `x ∈ A`（從 `hx_A`）
- 因此 `x ∈ B` 成立

**關鍵理解：**
- 如果 `compl U B ⊆ compl U A` 且 `x ∈ A`，要證明 `x ∈ B`
- 假設 `x ∉ B`，則 `x ∈ compl U B`
- 因為 `compl U B ⊆ compl U A`，所以 `x ∈ compl U A`，即 `x ∉ A`
- 但 `x ∈ A`，矛盾
- 因此 `x ∈ B`

**為什麼這個定理很重要？**

1. **展示補集合的對偶性質**：
   - 它告訴我們，子集合關係在補集合運算下是「反向」的
   - 如果 `A` 是 `B` 的子集合，則 `B` 的補集合是 `A` 的補集合的子集合
   - 這類似於邏輯中的對偶性：`P → Q` 等價於 `¬Q → ¬P`

2. **實際應用**：
   - 當我們需要證明補集合之間的子集合關係時，可以轉換為證明原集合之間的子集合關係
   - 這在處理補集合相關的證明時很有用

3. **直觀理解**：
   - 如果 `A` 是 `B` 的子集合，則 `A` 中的元素都在 `B` 中
   - 因此不在 `B` 中的元素（`B` 的補集合）也不在 `A` 中（`A` 的補集合）
   - 所以 `B` 的補集合是 `A` 的補集合的子集合

**關鍵技巧總結：**

1. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

2. **反證法的使用**：
   - 兩個方向都使用反證法
   - 第一個方向：假設 `x ∈ A`，推出 `x ∈ B`，與 `x ∉ B` 矛盾
   - 第二個方向：假設 `x ∉ B`，推出 `x ∉ A`，與 `x ∈ A` 矛盾

3. **子集合關係的應用**：
   - `hA_B : A ⊆ B` 可以應用到 `x ∈ A` 得到 `x ∈ B`
   - `h_compl_B_compl_A : compl U B ⊆ compl U A` 可以應用到 `x ∈ compl U B` 得到 `x ∈ compl U A`

4. **邏輯推理鏈**：
   - 第一個方向：`x ∈ compl U B` → `x ∉ B` → `x ∉ A`（因為如果 `x ∈ A` 則 `x ∈ B`，矛盾）→ `x ∈ compl U A`
   - 第二個方向：`x ∈ A` → 假設 `x ∉ B` → `x ∈ compl U B` → `x ∈ compl U A` → `x ∉ A`（矛盾）→ `x ∈ B`

**記憶要點：**
- `A ⊆ B ↔ Bᶜ ⊆ Aᶜ` 展示了補集合的對偶性質
- 證明時需要使用反證法
- 第一個方向：如果 `A ⊆ B` 且 `x ∈ compl U B`，則 `x ∈ compl U A`
- 第二個方向：如果 `compl U B ⊆ compl U A` 且 `x ∈ A`，則 `x ∈ B`
- 需要假設 `A ⊆ U` 和 `B ⊆ U` 來確保補集合的定義有效
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 子集合關係：`A ⊆ B` 意味著如果 `x ∈ A`，則 `x ∈ B`

---

### 範例 15：交集為空與補集合的等價性

**定理：** `A ∩ B = ∅ ↔ A = Bᶜ`（需要額外假設 `A ∪ B = U`），即 `A ∩ B = ∅ ↔ A = compl U B`

這個定理說明了一個重要的性質：如果 `A` 和 `B` 的交集為空，且它們的聯集等於全域集合 `U`，則 `A` 等於 `B` 的補集合。這展示了交集為空和補集合之間的等價關係。

**重要假設：**
- `A ⊆ U`：`A` 是全集合 `U` 的子集合
- `B ⊆ U`：`B` 是全集合 `U` 的子集合
- `A ∪ B = U`：`A` 和 `B` 的聯集等於全域集合 `U`

這個額外的假設 `A ∪ B = U` 是必要的，因為如果沒有這個假設，`A ∩ B = ∅` 並不能推出 `A = compl U B`。例如，如果 `A` 是 `compl U B` 的真子集合，則 `A ∩ B = ∅` 也成立，但 `A ≠ compl U B`。

這個證明展示了：
- 如何使用外延性公理證明集合相等
- 如何結合交集、聯集和補集合的定義
- 如何使用情況分析處理聯集成員關係
- 如何處理空集合的證明

**完整證明：**

```lean
theorem theorem_2_2_2_f (U A B : ZFSet) (hA_subset_U : A ⊆ U) (_hB_subset_U : B ⊆ U) (h_union : A ∪ B = U) : A ∩ B = ∅ ↔ A = compl U B := by
  constructor -- 將 ↔ 分成兩個方向
  · intro h_inter_empty -- h_inter_empty : A ∩ B = ∅
    apply ZFSet.ext -- 根據外延性公設，將 A = compl U B 轉換為 ∀ x, x ∈ A ↔ x ∈ compl U B
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_A -- hx_A : x ∈ A
      have hx_in_U : x ∈ U := hA_subset_U hx_A -- 因為 A ⊆ U 且 x ∈ A，所以 x ∈ U
      have hx_not_in_B : x ∉ B := by -- 證明 x ∉ B
        by_contra hx_in_B -- 假設 x ∈ B（要證明 x ∉ B，所以假設其否定）
        have hx_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr ⟨hx_A, hx_in_B⟩ -- x ∈ A ∧ x ∈ B, so x ∈ A ∩ B
        rw [h_inter_empty] at hx_inter -- 因為 A ∩ B = ∅，將 hx_inter 中的 A ∩ B 重寫為 ∅，得到 x ∈ ∅
        exact ZFSet.notMem_empty x hx_inter -- 矛盾：x ∈ ∅ 是不可能的
      exact (mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    · intro hx_compl_B -- hx_compl_B : x ∈ compl U B
      have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
      have hx_in_union : x ∈ A ∪ B := by -- 證明 x ∈ A ∪ B
        rw [h_union] -- 因為 A ∪ B = U，將 A ∪ B 重寫為 U
        exact h_temp.left -- x ∈ U
      rw [ZFSet.mem_union] at hx_in_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx_in_union with
      | inl hx_A => exact hx_A -- 情況1：x ∈ A，直接成立
      | inr hx_B => exact False.elim (h_temp.right hx_B) -- 情況2：x ∈ B，但 x ∉ B（從 h_temp.right），矛盾
  · intro h_compl_B -- h_compl_B : A = compl U B
    apply ZFSet.ext -- 根據外延性公設，將 A ∩ B = ∅ 轉換為 ∀ x, x ∈ A ∩ B ↔ x ∈ ∅
    intro x -- x : any arbitrary element
    constructor -- 將 ↔ 分成兩個部分
    · intro hx_inter -- hx_inter : x ∈ A ∩ B
      have hx_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      rw [h_compl_B] at hx_pair -- 因為 A = compl U B，將 hx_pair.left 中的 A 重寫為 compl U B
      have h_temp : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.left -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
      have h_contra : False := h_temp.right hx_pair.right -- 矛盾：x ∉ B（從 h_temp.right）和 x ∈ B（從 hx_pair.right）
      exact False.elim (ZFSet.notMem_empty x (False.elim h_contra)) -- 從 False 推出 x ∈ ∅
    · intro hx_empty -- hx_empty : x ∈ ∅
      exact False.elim (ZFSet.notMem_empty x hx_empty) -- x ∈ ∅ → x ∈ A ∩ B（空真命題）
```

**詳細步驟解析：**

#### 第一個方向：`A ∩ B = ∅ → A = compl U B`

**目標：** 證明如果 `A ∩ B = ∅` 且 `A ∪ B = U`，則 `A = compl U B`

**步驟 1：使用外延性公理**
- `apply ZFSet.ext`：將 `A = compl U B` 轉換為 `∀ x, x ∈ A ↔ x ∈ compl U B`
- `intro x`：引入任意元素 `x`
- `constructor`：將 `↔` 分成兩個部分

**步驟 2：第一部分 - 從 `x ∈ A` 推導出 `x ∈ compl U B`**
- `hx_A : x ∈ A`：假設 `x ∈ A`
- `hx_in_U : x ∈ U`：因為 `A ⊆ U` 且 `x ∈ A`，所以 `x ∈ U`
- `hx_not_in_B : x ∉ B`：使用反證法證明 `x ∉ B`
  - `by_contra hx_in_B`：假設 `x ∈ B`
  - `ZFSet.mem_inter.mpr ⟨hx_A, hx_in_B⟩`：如果 `x ∈ A` 且 `x ∈ B`，則 `x ∈ A ∩ B`
  - `rw [h_inter_empty] at hx_inter`：因為 `A ∩ B = ∅`，所以 `x ∈ ∅`
  - `ZFSet.notMem_empty x hx_inter`：矛盾！`x ∈ ∅` 是不可能的
- `(mem_compl U B x).mpr ⟨hx_in_U, hx_not_in_B⟩`：將 `x ∈ U ∧ x ∉ B` 轉換為 `x ∈ compl U B`

**步驟 3：第二部分 - 從 `x ∈ compl U B` 推導出 `x ∈ A`**
- `hx_compl_B : x ∈ compl U B`：假設 `x ∈ compl U B`
- `(mem_compl U B x).mp hx_compl_B`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
- `hx_in_union : x ∈ A ∪ B`：因為 `A ∪ B = U` 且 `x ∈ U`，所以 `x ∈ A ∪ B`
- `rw [ZFSet.mem_union] at hx_in_union`：將 `x ∈ A ∪ B` 轉換為 `x ∈ A ∨ x ∈ B`
- `cases hx_in_union`：分情況討論
  - `inl hx_A`：情況 1：`x ∈ A`，直接成立
  - `inr hx_B`：情況 2：`x ∈ B`，但 `x ∉ B`（從 `h_temp.right`），矛盾

**關鍵理解：**
- 如果 `A ∩ B = ∅` 且 `A ∪ B = U`，則 `A` 和 `B` 互補
- 如果 `x ∈ A`，則 `x ∉ B`（因為 `A ∩ B = ∅`），所以 `x ∈ compl U B`
- 如果 `x ∈ compl U B`，則 `x ∈ U` 且 `x ∉ B`
- 因為 `A ∪ B = U`，所以 `x ∈ A` 或 `x ∈ B`
- 但 `x ∉ B`，所以 `x ∈ A`

#### 第二個方向：`A = compl U B → A ∩ B = ∅`

**目標：** 證明如果 `A = compl U B`，則 `A ∩ B = ∅`

**步驟 1：使用外延性公理**
- `apply ZFSet.ext`：將 `A ∩ B = ∅` 轉換為 `∀ x, x ∈ A ∩ B ↔ x ∈ ∅`
- `intro x`：引入任意元素 `x`
- `constructor`：將 `↔` 分成兩個部分

**步驟 2：第一部分 - 從 `x ∈ A ∩ B` 推導出 `x ∈ ∅`**
- `hx_inter : x ∈ A ∩ B`：假設 `x ∈ A ∩ B`
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ A ∩ B` 轉換為 `x ∈ A ∧ x ∈ B`
- `rw [h_compl_B] at hx_pair`：因為 `A = compl U B`，將 `hx_pair.left` 中的 `A` 重寫為 `compl U B`
- `(mem_compl U B x).mp hx_pair.left`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
- `h_temp.right hx_pair.right`：矛盾！我們有 `x ∉ B`（從 `h_temp.right`）和 `x ∈ B`（從 `hx_pair.right`）
- `False.elim (ZFSet.notMem_empty x (False.elim h_contra))`：從 `False` 推出 `x ∈ ∅`

**步驟 3：第二部分 - 從 `x ∈ ∅` 推導出 `x ∈ A ∩ B`（空真命題）**
- `hx_empty : x ∈ ∅`：假設 `x ∈ ∅`
- `ZFSet.notMem_empty x hx_empty`：矛盾！`x ∈ ∅` 是不可能的
- 這是空真命題：從 `False` 可以推出任何命題

**關鍵理解：**
- 如果 `A = compl U B`，則 `A` 中的所有元素都不在 `B` 中
- 因此 `A ∩ B` 中沒有元素，即 `A ∩ B = ∅`
- 如果 `x ∈ A ∩ B`，則 `x ∈ A` 且 `x ∈ B`
- 但 `x ∈ A = compl U B` 意味著 `x ∉ B`，與 `x ∈ B` 矛盾
- 因此 `A ∩ B = ∅`

**為什麼這個定理很重要？**

1. **展示交集為空和補集合的關係**：
   - 它告訴我們，如果兩個集合的交集為空且它們的聯集等於全域集合，則它們互補
   - 這在處理互補集合時很有用

2. **實際應用**：
   - 當我們需要證明兩個集合互補時，可以證明它們的交集為空且聯集等於全域集合
   - 這在處理集合的分割和分類時很有用

3. **直觀理解**：
   - 如果 `A` 和 `B` 的交集為空，則它們沒有共同元素
   - 如果它們的聯集等於全域集合，則全域集合中的每個元素都在 `A` 或 `B` 中
   - 因此 `A` 和 `B` 互補，即 `A = compl U B`

**關鍵技巧總結：**

1. **外延性公理的使用**：
   - 使用 `apply ZFSet.ext` 將集合相等轉換為成員關係的等價
   - 這是證明集合相等的基本方法

2. **情況分析的使用**：
   - 使用 `cases` 處理聯集成員關係 `x ∈ A ∪ B`
   - 這允許我們分別處理 `x ∈ A` 和 `x ∈ B` 兩種情況

3. **反證法的使用**：
   - 第一個方向的第一部分使用反證法證明 `x ∉ B`
   - 第二個方向的第一部分使用反證法證明 `A ∩ B = ∅`

4. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

5. **空集合的處理**：
   - 使用 `ZFSet.notMem_empty` 處理空集合的成員關係
   - 空真命題：從 `False` 可以推出任何命題

**記憶要點：**
- `A ∩ B = ∅ ↔ A = compl U B` 展示了交集為空和補集合的等價關係
- 需要額外假設 `A ∪ B = U` 來確保定理成立
- 證明時需要使用外延性公理
- 第一個方向：如果 `A ∩ B = ∅` 且 `A ∪ B = U`，則 `A = compl U B`
- 第二個方向：如果 `A = compl U B`，則 `A ∩ B = ∅`
- 需要假設 `A ⊆ U` 和 `B ⊆ U` 來確保補集合的定義有效
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 交集的定義：`x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`
- 聯集的定義：`x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`
- 空集合的性質：`x ∈ ∅` 永遠為假

---

### 範例 16：德摩根定律 - 聯集的補集合等於補集合的交集

**定理：** `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`，即 `compl U (A ∪ B) = compl U A ∩ compl U B`

這是德摩根定律（De Morgan's Law）在集合論中的應用。德摩根定律是邏輯和集合論中的基本定律，它描述了補集合運算與聯集、交集運算之間的關係。

這個定理說明：兩個集合的聯集的補集合，等於它們各自補集合的交集。這在處理補集合相關的證明時非常有用。

這個證明展示了：
- 如何使用外延性公理證明集合相等
- 如何處理補集合和聯集的組合
- 如何使用反證法證明否定命題
- 如何使用情況分析處理聯集成員關係

**完整證明：**

```lean
theorem theorem_2_2_2_g (U A B : ZFSet): compl U (A ∪ B) = compl U A ∩ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 compl U (A ∪ B) = compl U A ∩ compl U B 轉換為 ∀ x, x ∈ compl U (A ∪ B) ↔ x ∈ compl U A ∩ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_compl_union -- hx_compl_union : x ∈ compl U (A ∪ B)
    -- x ∈ compl U (A ∪ B) → x ∈ compl U A ∩ compl U B
    have h_temp : x ∈ U ∧ x ∉ (A ∪ B) := (mem_compl U (A ∪ B) x).mp hx_compl_union -- 將 x ∈ compl U (A ∪ B) 拆成 x ∈ U ∧ x ∉ (A ∪ B)
    have hx_not_in_union : x ∉ (A ∪ B) := h_temp.right -- 從 x ∈ U ∧ x ∉ (A ∪ B) 提取 x ∉ (A ∪ B)
    have hx_not_A_and_not_B : x ∉ A ∧ x ∉ B := by -- 證明 x ∉ A ∧ x ∉ B
      constructor -- 將合取分成兩個部分
      · intro hx_A -- 假設 x ∈ A
        have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inl hx_A) -- x ∈ A，所以 x ∈ A ∪ B
        exact hx_not_in_union hx_in_union -- 矛盾：x ∉ (A ∪ B) 和 x ∈ A ∪ B
      · intro hx_B -- 假設 x ∈ B
        have hx_in_union : x ∈ A ∪ B := ZFSet.mem_union.mpr (Or.inr hx_B) -- x ∈ B，所以 x ∈ A ∪ B
        exact hx_not_in_union hx_in_union -- 矛盾：x ∉ (A ∪ B) 和 x ∈ A ∪ B
    have hx_compl_A : x ∈ compl U A := (mem_compl U A x).mpr ⟨h_temp.left, hx_not_A_and_not_B.left⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
    have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨h_temp.left, hx_not_A_and_not_B.right⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
    exact ZFSet.mem_inter.mpr ⟨hx_compl_A, hx_compl_B⟩ -- 將 x ∈ compl U A ∧ x ∈ compl U B 轉換為 x ∈ compl U A ∩ compl U B
  · intro hx_inter -- hx_inter : x ∈ compl U A ∩ compl U B
    -- x ∈ compl U A ∩ compl U B → x ∈ compl U (A ∪ B)
    have hx_pair : x ∈ compl U A ∧ x ∈ compl U B := ZFSet.mem_inter.mp hx_inter -- 將 x ∈ compl U A ∩ compl U B 拆成 x ∈ compl U A ∧ x ∈ compl U B
    have h_temp_A : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_pair.left -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
    have h_temp_B : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_pair.right -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
    have hx_not_in_union : x ∉ (A ∪ B) := by -- 證明 x ∉ (A ∪ B)
      intro hx_in_union -- 假設 x ∈ A ∪ B
      rw [ZFSet.mem_union] at hx_in_union -- 將 x ∈ A ∪ B 拆成 x ∈ A ∨ x ∈ B
      cases hx_in_union with
      | inl hx_A => exact h_temp_A.right hx_A -- 情況1：x ∈ A，但 x ∉ A（從 h_temp_A.right），矛盾
      | inr hx_B => exact h_temp_B.right hx_B -- 情況2：x ∈ B，但 x ∉ B（從 h_temp_B.right），矛盾
    exact (mem_compl U (A ∪ B) x).mpr ⟨h_temp_A.left, hx_not_in_union⟩ -- 將 x ∈ U ∧ x ∉ (A ∪ B) 轉換為 x ∈ compl U (A ∪ B)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ compl U (A ∪ B) → x ∈ compl U A ∩ compl U B`

**目標：** 證明如果 `x ∈ compl U (A ∪ B)`，則 `x ∈ compl U A ∩ compl U B`

**步驟 1：分解補集合成員關係**
- `(mem_compl U (A ∪ B) x).mp hx_compl_union`：將 `x ∈ compl U (A ∪ B)` 轉換為 `x ∈ U ∧ x ∉ (A ∪ B)`
- 現在我們有：`x ∈ U` 和 `x ∉ (A ∪ B)`

**步驟 2：證明 `x ∉ A ∧ x ∉ B`（使用反證法）**
- `constructor`：將合取分成兩個部分
- **第一部分 - 證明 `x ∉ A`**：
  - `intro hx_A`：假設 `x ∈ A`
  - `ZFSet.mem_union.mpr (Or.inl hx_A)`：如果 `x ∈ A`，則 `x ∈ A ∪ B`
  - `hx_not_in_union hx_in_union`：矛盾！我們有 `x ∉ (A ∪ B)` 和 `x ∈ A ∪ B`
  - 因此 `x ∉ A` 成立
- **第二部分 - 證明 `x ∉ B`**：
  - `intro hx_B`：假設 `x ∈ B`
  - `ZFSet.mem_union.mpr (Or.inr hx_B)`：如果 `x ∈ B`，則 `x ∈ A ∪ B`
  - `hx_not_in_union hx_in_union`：矛盾！我們有 `x ∉ (A ∪ B)` 和 `x ∈ A ∪ B`
  - 因此 `x ∉ B` 成立

**步驟 3：構造補集合成員關係**
- `(mem_compl U A x).mpr ⟨h_temp.left, hx_not_A_and_not_B.left⟩`：將 `x ∈ U ∧ x ∉ A` 轉換為 `x ∈ compl U A`
- `(mem_compl U B x).mpr ⟨h_temp.left, hx_not_A_and_not_B.right⟩`：將 `x ∈ U ∧ x ∉ B` 轉換為 `x ∈ compl U B`

**步驟 4：構造交集成員關係**
- `ZFSet.mem_inter.mpr ⟨hx_compl_A, hx_compl_B⟩`：將 `x ∈ compl U A ∧ x ∈ compl U B` 轉換為 `x ∈ compl U A ∩ compl U B`

**關鍵理解：**
- 如果 `x ∈ compl U (A ∪ B)`，則 `x ∉ (A ∪ B)`
- 如果 `x ∉ (A ∪ B)`，則 `x ∉ A` 且 `x ∉ B`（因為如果 `x ∈ A` 或 `x ∈ B`，則 `x ∈ A ∪ B`）
- 因此 `x ∈ compl U A` 且 `x ∈ compl U B`，所以 `x ∈ compl U A ∩ compl U B`

#### 第二個方向：`x ∈ compl U A ∩ compl U B → x ∈ compl U (A ∪ B)`

**目標：** 證明如果 `x ∈ compl U A ∩ compl U B`，則 `x ∈ compl U (A ∪ B)`

**步驟 1：分解交集成員關係**
- `ZFSet.mem_inter.mp hx_inter`：將 `x ∈ compl U A ∩ compl U B` 轉換為 `x ∈ compl U A ∧ x ∈ compl U B`
- 現在我們有：`x ∈ compl U A` 和 `x ∈ compl U B`

**步驟 2：分解補集合成員關係**
- `(mem_compl U A x).mp hx_pair.left`：將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
- `(mem_compl U B x).mp hx_pair.right`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
- 現在我們有：`x ∈ U`、`x ∉ A` 和 `x ∉ B`

**步驟 3：證明 `x ∉ (A ∪ B)`（使用反證法）**
- `intro hx_in_union`：假設 `x ∈ A ∪ B`
- `rw [ZFSet.mem_union] at hx_in_union`：將 `x ∈ A ∪ B` 轉換為 `x ∈ A ∨ x ∈ B`
- `cases hx_in_union`：分情況討論
  - `inl hx_A`：情況 1：`x ∈ A`，但 `x ∉ A`（從 `h_temp_A.right`），矛盾
  - `inr hx_B`：情況 2：`x ∈ B`，但 `x ∉ B`（從 `h_temp_B.right`），矛盾
- 因此 `x ∉ (A ∪ B)` 成立

**步驟 4：構造補集合成員關係**
- `(mem_compl U (A ∪ B) x).mpr ⟨h_temp_A.left, hx_not_in_union⟩`：將 `x ∈ U ∧ x ∉ (A ∪ B)` 轉換為 `x ∈ compl U (A ∪ B)`

**關鍵理解：**
- 如果 `x ∈ compl U A` 且 `x ∈ compl U B`，則 `x ∉ A` 且 `x ∉ B`
- 如果 `x ∉ A` 且 `x ∉ B`，則 `x ∉ (A ∪ B)`（因為如果 `x ∈ A ∪ B`，則 `x ∈ A` 或 `x ∈ B`，矛盾）
- 因此 `x ∈ compl U (A ∪ B)`

**為什麼這個定理很重要？**

1. **德摩根定律的應用**：
   - 這是邏輯和集合論中的基本定律
   - 它展示了補集合運算與聯集、交集運算之間的關係
   - 類似的定律也適用於交集：`(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`

2. **實際應用**：
   - 當我們需要證明補集合相關的性質時，可以轉換為證明原集合的性質
   - 這在處理複雜的補集合表達式時很有用
   - 可以用來簡化補集合的表達式

3. **直觀理解**：
   - 不在 `A` 或 `B` 中的元素（`(A ∪ B)ᶜ`），就是既不在 `A` 中也不在 `B` 中的元素（`Aᶜ ∩ Bᶜ`）
   - 這符合我們對「不在 A 或 B 中」的直觀理解

**關鍵技巧總結：**

1. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

2. **聯集的處理**：
   - 使用 `ZFSet.mem_union.mpr` 構造聯集成員關係
   - 使用 `ZFSet.mem_union.mp` 或 `rw [ZFSet.mem_union]` 分解聯集成員關係
   - 使用 `cases` 處理析取（`x ∈ A ∨ x ∈ B`）

3. **交集的處理**：
   - 使用 `ZFSet.mem_inter.mpr` 構造交集成員關係
   - 使用 `ZFSet.mem_inter.mp` 分解交集成員關係

4. **反證法的使用**：
   - 第一個方向：使用反證法證明 `x ∉ A` 和 `x ∉ B`
   - 第二個方向：使用反證法證明 `x ∉ (A ∪ B)`

5. **邏輯推理鏈**：
   - 第一個方向：`x ∈ compl U (A ∪ B)` → `x ∉ (A ∪ B)` → `x ∉ A ∧ x ∉ B` → `x ∈ compl U A ∧ x ∈ compl U B` → `x ∈ compl U A ∩ compl U B`
   - 第二個方向：`x ∈ compl U A ∩ compl U B` → `x ∉ A ∧ x ∉ B` → `x ∉ (A ∪ B)` → `x ∈ compl U (A ∪ B)`

**記憶要點：**
- `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` 是德摩根定律在集合論中的應用
- 證明時需要使用外延性公理
- 第一個方向：如果 `x ∈ compl U (A ∪ B)`，則 `x ∈ compl U A ∩ compl U B`
- 第二個方向：如果 `x ∈ compl U A ∩ compl U B`，則 `x ∈ compl U (A ∪ B)`
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 聯集的定義：`x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`
- 交集的定義：`x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`
- 使用反證法證明否定命題：假設命題成立，推出矛盾
- 使用情況分析處理析取：`cases` 可以分別處理 `x ∈ A` 和 `x ∈ B` 兩種情況

---

### 範例 17：德摩根定律 - 交集的補集合等於補集合的聯集

**定理：** `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`，即 `compl U (A ∩ B) = compl U A ∪ compl U B`

這是德摩根定律的另一個方向，與範例 16 相對應。它說明：兩個集合的交集的補集合，等於它們各自補集合的聯集。

這個定理與範例 16 一起構成了完整的德摩根定律：
- `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`（範例 16）
- `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`（範例 17）

這個證明展示了：
- 如何使用外延性公理證明集合相等
- 如何處理補集合和交集的組合
- 如何使用反證法證明析取命題
- 如何使用情況分析處理聯集成員關係

**完整證明：**

```lean
theorem theorem_2_2_2_h (U A B : ZFSet) : compl U (A ∩ B) = compl U A ∪ compl U B := by
  apply ZFSet.ext -- 根據外延性公設，將 compl U (A ∩ B) = compl U A ∪ compl U B 轉換為 ∀ x, x ∈ compl U (A ∩ B) ↔ x ∈ compl U A ∪ compl U B
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_compl_inter -- hx_compl_inter : x ∈ compl U (A ∩ B)
    -- x ∈ compl U (A ∩ B) → x ∈ compl U A ∪ compl U B
    have h_temp : x ∈ U ∧ x ∉ (A ∩ B) := (mem_compl U (A ∩ B) x).mp hx_compl_inter -- 將 x ∈ compl U (A ∩ B) 拆成 x ∈ U ∧ x ∉ (A ∩ B)
    have hx_not_in_inter : x ∉ (A ∩ B) := h_temp.right -- 從 x ∈ U ∧ x ∉ (A ∩ B) 提取 x ∉ (A ∩ B)
    have hx_not_A_or_not_B : x ∉ A ∨ x ∉ B := by -- 證明 x ∉ A ∨ x ∉ B
      by_contra h -- 假設 ¬(x ∉ A ∨ x ∉ B)，即 x ∈ A ∧ x ∈ B
      have hx_in_A_and_B : x ∈ A ∧ x ∈ B := by -- 證明 x ∈ A ∧ x ∈ B
        constructor -- 將合取分成兩個部分
        · by_contra hx_not_A -- 假設 x ∉ A
          exact h (Or.inl hx_not_A) -- 矛盾：¬(x ∉ A ∨ x ∉ B) 和 x ∉ A
        · by_contra hx_not_B -- 假設 x ∉ B
          exact h (Or.inr hx_not_B) -- 矛盾：¬(x ∉ A ∨ x ∉ B) 和 x ∉ B
      have hx_in_inter : x ∈ A ∩ B := ZFSet.mem_inter.mpr hx_in_A_and_B -- 將 x ∈ A ∧ x ∈ B 轉換為 x ∈ A ∩ B
      exact hx_not_in_inter hx_in_inter -- 矛盾：x ∉ (A ∩ B) 和 x ∈ A ∩ B
    cases hx_not_A_or_not_B with
    | inl hx_not_A => -- 情況1：x ∉ A
      have hx_compl_A : x ∈ compl U A := (mem_compl U A x).mpr ⟨h_temp.left, hx_not_A⟩ -- 將 x ∈ U ∧ x ∉ A 轉換為 x ∈ compl U A
      exact ZFSet.mem_union.mpr (Or.inl hx_compl_A) -- x ∈ compl U A，所以 x ∈ compl U A ∪ compl U B
    | inr hx_not_B => -- 情況2：x ∉ B
      have hx_compl_B : x ∈ compl U B := (mem_compl U B x).mpr ⟨h_temp.left, hx_not_B⟩ -- 將 x ∈ U ∧ x ∉ B 轉換為 x ∈ compl U B
      exact ZFSet.mem_union.mpr (Or.inr hx_compl_B) -- x ∈ compl U B，所以 x ∈ compl U A ∪ compl U B
  · intro hx_union -- hx_union : x ∈ compl U A ∪ compl U B
    -- x ∈ compl U A ∪ compl U B → x ∈ compl U (A ∩ B)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ compl U A ∪ compl U B 拆成 x ∈ compl U A ∨ x ∈ compl U B
    have hx_in_U : x ∈ U := by -- 證明 x ∈ U
      cases hx_union with
      | inl hx_compl_A => exact ((mem_compl U A x).mp hx_compl_A).left -- 情況1：x ∈ compl U A，所以 x ∈ U
      | inr hx_compl_B => exact ((mem_compl U B x).mp hx_compl_B).left -- 情況2：x ∈ compl U B，所以 x ∈ U
    have hx_not_in_inter : x ∉ (A ∩ B) := by -- 證明 x ∉ (A ∩ B)
      intro hx_in_inter -- 假設 x ∈ A ∩ B
      have hx_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp hx_in_inter -- 將 x ∈ A ∩ B 拆成 x ∈ A ∧ x ∈ B
      cases hx_union with
      | inl hx_compl_A => -- 情況1：x ∈ compl U A
        have h_temp_A : x ∈ U ∧ x ∉ A := (mem_compl U A x).mp hx_compl_A -- 將 x ∈ compl U A 拆成 x ∈ U ∧ x ∉ A
        exact h_temp_A.right hx_pair.left -- 矛盾：x ∉ A（從 h_temp_A.right）和 x ∈ A（從 hx_pair.left）
      | inr hx_compl_B => -- 情況2：x ∈ compl U B
        have h_temp_B : x ∈ U ∧ x ∉ B := (mem_compl U B x).mp hx_compl_B -- 將 x ∈ compl U B 拆成 x ∈ U ∧ x ∉ B
        exact h_temp_B.right hx_pair.right -- 矛盾：x ∉ B（從 h_temp_B.right）和 x ∈ B（從 hx_pair.right）
    exact (mem_compl U (A ∩ B) x).mpr ⟨hx_in_U, hx_not_in_inter⟩ -- 將 x ∈ U ∧ x ∉ (A ∩ B) 轉換為 x ∈ compl U (A ∩ B)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ compl U (A ∩ B) → x ∈ compl U A ∪ compl U B`

**目標：** 證明如果 `x ∈ compl U (A ∩ B)`，則 `x ∈ compl U A ∪ compl U B`

**步驟 1：分解補集合成員關係**
- `(mem_compl U (A ∩ B) x).mp hx_compl_inter`：將 `x ∈ compl U (A ∩ B)` 轉換為 `x ∈ U ∧ x ∉ (A ∩ B)`
- 現在我們有：`x ∈ U` 和 `x ∉ (A ∩ B)`

**步驟 2：證明 `x ∉ A ∨ x ∉ B`（使用反證法）**
- `by_contra h`：假設 `¬(x ∉ A ∨ x ∉ B)`，即 `x ∈ A ∧ x ∈ B`
- **證明 `x ∈ A ∧ x ∈ B`**：
  - `constructor`：將合取分成兩個部分
  - **第一部分 - 證明 `x ∈ A`**：
    - `by_contra hx_not_A`：假設 `x ∉ A`
    - `h (Or.inl hx_not_A)`：矛盾！我們有 `¬(x ∉ A ∨ x ∉ B)` 和 `x ∉ A`
    - 因此 `x ∈ A` 成立
  - **第二部分 - 證明 `x ∈ B`**：
    - `by_contra hx_not_B`：假設 `x ∉ B`
    - `h (Or.inr hx_not_B)`：矛盾！我們有 `¬(x ∉ A ∨ x ∉ B)` 和 `x ∉ B`
    - 因此 `x ∈ B` 成立
- `ZFSet.mem_inter.mpr hx_in_A_and_B`：將 `x ∈ A ∧ x ∈ B` 轉換為 `x ∈ A ∩ B`
- `hx_not_in_inter hx_in_inter`：矛盾！我們有 `x ∉ (A ∩ B)` 和 `x ∈ A ∩ B`
- 因此 `x ∉ A ∨ x ∉ B` 成立

**步驟 3：分情況構造聯集成員關係**
- `cases hx_not_A_or_not_B`：分情況討論
  - `inl hx_not_A`：情況 1：`x ∉ A`
    - `(mem_compl U A x).mpr ⟨h_temp.left, hx_not_A⟩`：將 `x ∈ U ∧ x ∉ A` 轉換為 `x ∈ compl U A`
    - `ZFSet.mem_union.mpr (Or.inl hx_compl_A)`：`x ∈ compl U A`，所以 `x ∈ compl U A ∪ compl U B`
  - `inr hx_not_B`：情況 2：`x ∉ B`
    - `(mem_compl U B x).mpr ⟨h_temp.left, hx_not_B⟩`：將 `x ∈ U ∧ x ∉ B` 轉換為 `x ∈ compl U B`
    - `ZFSet.mem_union.mpr (Or.inr hx_compl_B)`：`x ∈ compl U B`，所以 `x ∈ compl U A ∪ compl U B`

**關鍵理解：**
- 如果 `x ∈ compl U (A ∩ B)`，則 `x ∉ (A ∩ B)`
- 如果 `x ∉ (A ∩ B)`，則 `x ∉ A` 或 `x ∉ B`（因為如果 `x ∈ A` 且 `x ∈ B`，則 `x ∈ A ∩ B`，矛盾）
- 因此 `x ∈ compl U A` 或 `x ∈ compl U B`，所以 `x ∈ compl U A ∪ compl U B`

#### 第二個方向：`x ∈ compl U A ∪ compl U B → x ∈ compl U (A ∩ B)`

**目標：** 證明如果 `x ∈ compl U A ∪ compl U B`，則 `x ∈ compl U (A ∩ B)`

**步驟 1：分解聯集成員關係**
- `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ compl U A ∪ compl U B` 轉換為 `x ∈ compl U A ∨ x ∈ compl U B`
- 現在我們有：`x ∈ compl U A` 或 `x ∈ compl U B`

**步驟 2：證明 `x ∈ U`**
- `cases hx_union`：分情況討論
  - `inl hx_compl_A`：情況 1：`x ∈ compl U A`
    - `((mem_compl U A x).mp hx_compl_A).left`：從 `x ∈ compl U A` 提取 `x ∈ U`
  - `inr hx_compl_B`：情況 2：`x ∈ compl U B`
    - `((mem_compl U B x).mp hx_compl_B).left`：從 `x ∈ compl U B` 提取 `x ∈ U`

**步驟 3：證明 `x ∉ (A ∩ B)`（使用反證法）**
- `intro hx_in_inter`：假設 `x ∈ A ∩ B`
- `ZFSet.mem_inter.mp hx_in_inter`：將 `x ∈ A ∩ B` 轉換為 `x ∈ A ∧ x ∈ B`
- `cases hx_union`：分情況討論
  - `inl hx_compl_A`：情況 1：`x ∈ compl U A`
    - `(mem_compl U A x).mp hx_compl_A`：將 `x ∈ compl U A` 轉換為 `x ∈ U ∧ x ∉ A`
    - `h_temp_A.right hx_pair.left`：矛盾！我們有 `x ∉ A`（從 `h_temp_A.right`）和 `x ∈ A`（從 `hx_pair.left`）
  - `inr hx_compl_B`：情況 2：`x ∈ compl U B`
    - `(mem_compl U B x).mp hx_compl_B`：將 `x ∈ compl U B` 轉換為 `x ∈ U ∧ x ∉ B`
    - `h_temp_B.right hx_pair.right`：矛盾！我們有 `x ∉ B`（從 `h_temp_B.right`）和 `x ∈ B`（從 `hx_pair.right`）
- 因此 `x ∉ (A ∩ B)` 成立

**步驟 4：構造補集合成員關係**
- `(mem_compl U (A ∩ B) x).mpr ⟨hx_in_U, hx_not_in_inter⟩`：將 `x ∈ U ∧ x ∉ (A ∩ B)` 轉換為 `x ∈ compl U (A ∩ B)`

**關鍵理解：**
- 如果 `x ∈ compl U A` 或 `x ∈ compl U B`，則 `x ∉ A` 或 `x ∉ B`
- 如果 `x ∉ A` 或 `x ∉ B`，則 `x ∉ (A ∩ B)`（因為如果 `x ∈ A ∩ B`，則 `x ∈ A` 且 `x ∈ B`，矛盾）
- 因此 `x ∈ compl U (A ∩ B)`

**為什麼這個定理很重要？**

1. **完成德摩根定律**：
   - 與範例 16 一起，構成了完整的德摩根定律
   - 展示了補集合運算與聯集、交集運算之間的完整關係

2. **實際應用**：
   - 當我們需要證明補集合相關的性質時，可以轉換為證明原集合的性質
   - 這在處理複雜的補集合表達式時很有用
   - 可以用來簡化補集合的表達式

3. **直觀理解**：
   - 不在 `A` 和 `B` 的交集中的元素（`(A ∩ B)ᶜ`），就是不在 `A` 中或不在 `B` 中的元素（`Aᶜ ∪ Bᶜ`）
   - 這符合我們對「不在 A 和 B 的交集中」的直觀理解

**關鍵技巧總結：**

1. **補集合的分解和構造**：
   - 使用 `mem_compl.mp` 分解補集合成員關係
   - 使用 `mem_compl.mpr` 構造補集合成員關係

2. **聯集的處理**：
   - 使用 `ZFSet.mem_union.mpr` 構造聯集成員關係
   - 使用 `rw [ZFSet.mem_union]` 分解聯集成員關係
   - 使用 `cases` 處理析取（`x ∈ A ∨ x ∈ B`）

3. **交集的處理**：
   - 使用 `ZFSet.mem_inter.mpr` 構造交集成員關係
   - 使用 `ZFSet.mem_inter.mp` 分解交集成員關係

4. **反證法的使用**：
   - 第一個方向：使用反證法證明 `x ∉ A ∨ x ∉ B`
   - 第二個方向：使用反證法證明 `x ∉ (A ∩ B)`

5. **邏輯推理鏈**：
   - 第一個方向：`x ∈ compl U (A ∩ B)` → `x ∉ (A ∩ B)` → `x ∉ A ∨ x ∉ B` → `x ∈ compl U A ∨ x ∈ compl U B` → `x ∈ compl U A ∪ compl U B`
   - 第二個方向：`x ∈ compl U A ∪ compl U B` → `x ∉ A ∨ x ∉ B` → `x ∉ (A ∩ B)` → `x ∈ compl U (A ∩ B)`

**記憶要點：**
- `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ` 是德摩根定律的另一個方向
- 與 `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` 一起構成完整的德摩根定律
- 證明時需要使用外延性公理
- 第一個方向：如果 `x ∈ compl U (A ∩ B)`，則 `x ∈ compl U A ∪ compl U B`
- 第二個方向：如果 `x ∈ compl U A ∪ compl U B`，則 `x ∈ compl U (A ∩ B)`
- 補集合的定義：`x ∈ compl U A ↔ x ∈ U ∧ x ∉ A`
- 聯集的定義：`x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`
- 交集的定義：`x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`
- 使用反證法證明析取命題：假設命題的否定成立，推出矛盾
- 使用情況分析處理析取：`cases` 可以分別處理 `x ∉ A` 和 `x ∉ B` 兩種情況

---

## 有序對與笛卡爾積

### 有序對（Ordered Pair）的定義

在集合論中，我們需要一種方法來表示有序的元素對 `(a, b)`，其中順序很重要（即 `(a, b) ≠ (b, a)` 當 `a ≠ b` 時）。

**Kuratowski 定義：**

在 ZFC 中，有序對 `(a, b)` 定義為：
```
(a, b) = {{a}, {a, b}}
```

這個定義確保了：
- `(a, b) = (c, d)` 當且僅當 `a = c` 且 `b = d`
- 只使用集合（符合 ZFC 的要求）
- 可以區分順序：`(a, b) ≠ (b, a)`（當 `a ≠ b` 時）

**為什麼這樣定義？**

1. **只使用集合**：`{{a}, {a, b}}` 完全由集合構成，符合 ZFC 的要求
2. **可以區分順序**：當 `a ≠ b` 時，`{{a}, {a, b}} ≠ {{b}, {a, b}}`
3. **可以判斷相等**：`(a, b) = (c, d)` 當且僅當 `a = c` 且 `b = d`

**注意：**
- 當 `a = b` 時，`{{a}, {a, a}} = {{a}}`（只有一個元素）
- 當 `a ≠ b` 時，`{{a}, {a, b}}` 有兩個元素：`{a}` 和 `{a, b}`

**完整定義：**

```lean
def ordered_pair (a b : ZFSet) : ZFSet := {{a}, {a, b}}
```

**語法解析：**
- `def ordered_pair`：定義函數 `ordered_pair`
- `(a b : ZFSet)`：參數 `a` 和 `b` 都是 `ZFSet` 類型
- `: ZFSet`：返回類型是 `ZFSet`（一個集合）
- `:= {{a}, {a, b}}`：使用配對公設構造集合 `{{a}, {a, b}}`

**含義：**
- `ordered_pair a b = {{a}, {a, b}}`
- 即有序對 `(a, b)` 定義為包含 `{a}` 和 `{a, b}` 的集合

---

### 笛卡爾積（Cartesian Product）的定義

**數學定義：**

對於兩個集合 `A` 和 `B`，它們的笛卡爾積定義為：
```
A × B = {(a, b) | a ∈ A, b ∈ B}
```

即所有有序對 `(a, b)` 的集合，其中 `a ∈ A` 且 `b ∈ B`。

**在 ZFC 中的定義：**

在 ZFC 中，我們需要使用分離公設來構造笛卡爾積。關鍵觀察是：
- 有序對 `(a, b) = {{a}, {a, b}}` 是 `A ∪ B` 的冪集的冪集的元素
- 因為 `{a}` 和 `{a, b}` 都是 `A ∪ B` 的子集合
- 所以 `{{a}, {a, b}}` 是 `powerset (A ∪ B)` 的子集合

**完整定義：**

```lean
def product (A B : ZFSet) : ZFSet := 
  ZFSet.sep 
    (fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b) 
    (ZFSet.powerset (ZFSet.powerset (A ∪ B)))
```

**語法解析：**
- `def product`：定義函數 `product`
- `(A B : ZFSet)`：參數 `A` 和 `B` 都是 `ZFSet` 類型
- `: ZFSet`：返回類型是 `ZFSet`（一個集合）
- `:= ZFSet.sep`：使用分離公設
- `(fun x => ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b)`：性質：`x` 是 `A × B` 中的有序對
- `(ZFSet.powerset (ZFSet.powerset (A ∪ B)))`：源集合：`A ∪ B` 的冪集的冪集

**含義：**
- `product A B = {x | ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b}`
- 即從 `A ∪ B` 的冪集的冪集中選出所有形如 `(a, b)` 的有序對，其中 `a ∈ A` 且 `b ∈ B`

**注意：**
- 這個定義使用分離公設從一個足夠大的集合中分離出所有有序對
- 因為有序對 `(a, b) = {{a}, {a, b}}` 是 `A ∪ B` 的冪集的冪集的元素

---

### 笛卡爾積的成員關係

**定理：** `x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`

這個定理說明了笛卡爾積的成員關係：`x` 屬於 `A × B` 當且僅當 `x` 是某個有序對 `(a, b)`，其中 `a ∈ A` 且 `b ∈ B`。

**完整證明：**

```lean
theorem mem_product (A B x : ZFSet) : x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b := by
  rw [product] -- 展開 product 的定義
  rw [ZFSet.mem_sep] -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
  constructor -- 將 ↔ 分成兩個方向
  · intro ⟨hx_in_powerset, h_exists⟩ -- hx_in_powerset : x ∈ powerset (powerset (A ∪ B)), h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    exact h_exists -- 直接使用 h_exists
  · intro h_exists -- h_exists : ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    constructor -- 將合取分成兩個部分
    · -- 證明 x ∈ powerset (powerset (A ∪ B))
      -- 這需要證明有序對 ordered_pair a b = {{a}, {a, b}} 是 powerset (powerset (A ∪ B)) 的元素
      -- 即證明 {{a}, {a, b}} ⊆ powerset (A ∪ B)
      rcases h_exists with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, x = ordered_pair a b
      rw [ordered_pair] -- 展開 ordered_pair 的定義：x = {{a}, {a, b}}
      apply ZFSet.mem_powerset.mpr -- 使用冪集的成員關係：x ∈ powerset A ↔ x ⊆ A，目標變成 {{a}, {a, b}} ⊆ powerset (A ∪ B)
      intro z hz -- z : any arbitrary element, hz : z ∈ {{a}, {a, b}}
      rw [ZFSet.mem_pair] at hz -- 將 z ∈ {{a}, {a, b}} 拆成 z = {a} ∨ z = {a, b}
      cases hz with
      | inl hz_eq => -- 情況1：z = {a}
        rw [hz_eq] -- 將 z 重寫為 {a}
        apply ZFSet.mem_powerset.mpr -- 證明 {a} ∈ powerset (A ∪ B)，即 {a} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a}
        rw [ZFSet.mem_singleton] at hw -- 將 w ∈ {a} 轉換為 w = a
        rw [hw] -- 將 w 重寫為 a
        rw [ZFSet.mem_union] -- 將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
        left
        exact ha -- a ∈ A，所以 a ∈ A ∪ B
      | inr hz_eq => -- 情況2：z = {a, b}
        rw [hz_eq] -- 將 z 重寫為 {a, b}
        apply ZFSet.mem_powerset.mpr -- 證明 {a, b} ∈ powerset (A ∪ B)，即 {a, b} ⊆ A ∪ B
        intro w hw -- w : any arbitrary element, hw : w ∈ {a, b}
        rw [ZFSet.mem_pair] at hw -- 將 w ∈ {a, b} 拆成 w = a ∨ w = b
        cases hw with
        | inl hw_eq => -- w = a
          rw [hw_eq] -- 將 w 重寫為 a
          rw [ZFSet.mem_union] -- 將 a ∈ A ∪ B 拆成 a ∈ A ∨ a ∈ B
          left
          exact ha -- a ∈ A，所以 a ∈ A ∪ B
        | inr hw_eq => -- w = b
          rw [hw_eq] -- 將 w 重寫為 b
          rw [ZFSet.mem_union] -- 將 b ∈ A ∪ B 拆成 a ∈ A ∨ b ∈ B
          right
          exact hb -- b ∈ B，所以 b ∈ A ∪ B
    · exact h_exists -- 直接使用 h_exists
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ product A B → ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`

**目標：** 證明如果 `x ∈ product A B`，則存在 `a ∈ A` 和 `b ∈ B`，使得 `x = ordered_pair a b`

**步驟：**
- `rw [product]`：展開 `product` 的定義
- `rw [ZFSet.mem_sep]`：使用分離公設的成員關係，得到 `x ∈ powerset (powerset (A ∪ B)) ∧ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
- `exact h_exists`：直接使用存在量詞部分

#### 第二個方向：`∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b → x ∈ product A B`

**目標：** 證明如果存在 `a ∈ A` 和 `b ∈ B`，使得 `x = ordered_pair a b`，則 `x ∈ product A B`

**步驟 1：分解存在量詞**
- `rcases h_exists with ⟨a, ha, b, hb, rfl⟩`：分解存在量詞，得到 `a ∈ A`、`b ∈ B` 和 `x = ordered_pair a b`
- `rw [ordered_pair]`：展開 `ordered_pair` 的定義，得到 `x = {{a}, {a, b}}`

**步驟 2：證明 `x ∈ powerset (powerset (A ∪ B))`**
- `apply ZFSet.mem_powerset.mpr`：目標變成 `{{a}, {a, b}} ⊆ powerset (A ∪ B)`
- `intro z hz`：引入任意元素 `z`，假設 `z ∈ {{a}, {a, b}}`
- `rw [ZFSet.mem_pair] at hz`：將 `z ∈ {{a}, {a, b}}` 拆成 `z = {a} ∨ z = {a, b}`
- `cases hz`：分情況討論

**情況 1：`z = {a}`**
- `rw [hz_eq]`：將 `z` 重寫為 `{a}`
- `apply ZFSet.mem_powerset.mpr`：目標變成 `{a} ⊆ A ∪ B`
- `intro w hw`：引入任意元素 `w`，假設 `w ∈ {a}`
- `rw [ZFSet.mem_singleton] at hw`：將 `w ∈ {a}` 轉換為 `w = a`
- `rw [hw]`：將 `w` 重寫為 `a`
- `rw [ZFSet.mem_union]`：將 `a ∈ A ∪ B` 拆成 `a ∈ A ∨ a ∈ B`
- `left` 和 `exact ha`：因為 `a ∈ A`，所以 `a ∈ A ∪ B`

**情況 2：`z = {a, b}`**
- `rw [hz_eq]`：將 `z` 重寫為 `{a, b}`
- `apply ZFSet.mem_powerset.mpr`：目標變成 `{a, b} ⊆ A ∪ B`
- `intro w hw`：引入任意元素 `w`，假設 `w ∈ {a, b}`
- `rw [ZFSet.mem_pair] at hw`：將 `w ∈ {a, b}` 拆成 `w = a ∨ w = b`
- `cases hw`：分情況討論
  - `inl hw_eq`：`w = a`，使用 `ha` 證明 `a ∈ A ∪ B`
  - `inr hw_eq`：`w = b`，使用 `hb` 證明 `b ∈ A ∪ B`

**關鍵理解：**
- 有序對 `(a, b) = {{a}, {a, b}}` 是 `powerset (powerset (A ∪ B))` 的元素
- 因為 `{a}` 和 `{a, b}` 都是 `A ∪ B` 的子集合
- 所以 `{{a}, {a, b}}` 是 `powerset (A ∪ B)` 的子集合

**為什麼這個定義很重要？**

1. **構造有序對**：
   - 在 ZFC 中，所有東西都必須是集合
   - Kuratowski 定義提供了一種只用集合來表示有序對的方法

2. **構造笛卡爾積**：
   - 笛卡爾積是關係和函數的基礎
   - 在 ZFC 中，關係和函數都定義為有序對的集合

3. **實際應用**：
   - 笛卡爾積用於定義二元關係
   - 函數定義為特殊的關係（滿足單值性）
   - 這是數學中許多概念的基礎

**關鍵技巧總結：**

1. **有序對的構造**：
   - 使用配對公設構造 `{{a}, {a, b}}`
   - 這確保了有序對的順序性

2. **笛卡爾積的構造**：
   - 使用分離公設從足夠大的集合中分離出所有有序對
   - 使用 `powerset (powerset (A ∪ B))` 作為源集合

3. **成員關係的證明**：
   - 使用 `ZFSet.mem_sep` 分解分離公設的成員關係
   - 使用 `ZFSet.mem_powerset.mpr` 證明子集合關係
   - 使用 `ZFSet.mem_singleton` 處理單元素集合
   - 使用 `ZFSet.mem_pair` 處理雙元素集合

4. **情況分析**：
   - 使用 `cases` 處理析取（`z = {a} ∨ z = {a, b}`）
   - 使用 `cases` 處理析取（`w = a ∨ w = b`）

**記憶要點：**
- 有序對的定義：`ordered_pair a b = {{a}, {a, b}}`（Kuratowski 定義）
- 有序對的性質：`(a, b) = (c, d)` 當且僅當 `a = c` 且 `b = d`
- 笛卡爾積的定義：`product A B = {x | ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b}`
- 笛卡爾積的成員關係：`x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
- 單元素集合的成員關係：`w ∈ {a} ↔ w = a`（使用 `ZFSet.mem_singleton`）
- 雙元素集合的成員關係：`w ∈ {a, b} ↔ w = a ∨ w = b`（使用 `ZFSet.mem_pair`）
- 冪集的成員關係：`x ∈ powerset A ↔ x ⊆ A`（使用 `ZFSet.mem_powerset`）
- 分離公設的成員關係：`x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x`（使用 `ZFSet.mem_sep`）

---

### 有序對的單射性質

**定理：** 如果 `ordered_pair a b = ordered_pair a' b'`，則 `a = a'` 且 `b = b'`

這個定理說明了有序對的單射性質：不同的有序對對應不同的集合表示。這是 Kuratowski 定義的核心性質，確保了有序對的唯一性。

**完整證明：**

```lean
theorem ordered_pair_inj (a b a' b' : ZFSet) : ordered_pair a b = ordered_pair a' b' → a = a' ∧ b = b' := by
  intro h_eq -- h_eq : ordered_pair a b = ordered_pair a' b'
  -- 因為 {{a}, {a, b}} = {{a'}, {a', b'}}，所以 {a} ∈ {{a}, {a, b}} 當且僅當 {a} ∈ {{a'}, {a', b'}}
  have h_a_in : {a} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inl rfl) -- {a} = {a}，所以 {a} ∈ {{a}, {a, b}}
  rw [h_eq] at h_a_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a} ∈ {{a'}, {a', b'}}
  rw [ordered_pair] at h_a_in -- 展開 ordered_pair a' b' 的定義，得到 {a} ∈ {{a'}, {a', b'}}
  rw [ZFSet.mem_pair] at h_a_in -- 將 {a} ∈ {{a'}, {a', b'}} 拆成 {a} = {a'} ∨ {a} = {a', b'}
  cases h_a_in with
  | inl h_eq_singleton => -- 情況1：{a} = {a'}
    have ha_eq : a = a' := by -- 證明 a = a'
      have ha_in : a ∈ {a} := ZFSet.mem_singleton.mpr rfl -- a = a，所以 a ∈ {a}
      rw [h_eq_singleton] at ha_in -- 將 {a} 重寫為 {a'}，得到 a ∈ {a'}
      rw [ZFSet.mem_singleton] at ha_in -- 將 a ∈ {a'} 轉換為 a = a'
      exact ha_in -- a = a'
    -- 現在我們有 a = a'，需要證明 b = b'
    -- 因為 ordered_pair a b = ordered_pair a' b' 且 a = a'，所以 {{a}, {a, b}} = {{a'}, {a', b'}} = {{a}, {a, b'}}
    have h_ab_in : {a, b} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b} = {a, b}，所以 {a, b} ∈ {{a}, {a, b}}
    rw [h_eq] at h_ab_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a, b} ∈ ordered_pair a' b'
    rw [ordered_pair] at h_ab_in -- 展開 ordered_pair a' b' 的定義，得到 {a, b} ∈ {{a'}, {a', b'}}
    rw [ha_eq] at h_ab_in -- 將 a' 重寫為 a，得到 {a, b} ∈ {{a}, {a, b'}}
    rw [ZFSet.mem_pair] at h_ab_in -- 將 {a, b} ∈ {{a}, {a, b'}} 拆成 {a, b} = {a} ∨ {a, b} = {a, b'}
    cases h_ab_in with
    | inl h_eq_pair_singleton => -- 情況1.1：{a, b} = {a} 或 {a', b} = {a'}（需要重寫）
      -- 先將 h_eq_pair_singleton 中的 a' 重寫為 a
      rw [ha_eq.symm] at h_eq_pair_singleton -- 將 a' 重寫為 a，得到 {a, b} = {a}（因為 ha_eq : a = a'，所以 ha_eq.symm : a' = a）
      -- 這意味著 {a, b} 只有一個元素 a，所以 b = a
      have hb_eq_a : b = a := by -- 證明 b = a
        -- 因為 {a, b} = {a}，所以 b ∈ {a, b} 當且僅當 b ∈ {a}
        have hb_in_pair : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        -- 使用 h_eq_pair_singleton 將 {a, b} 替換為 {a}
        -- 因為 {a, b} = {a}，所以 b ∈ {a, b} 意味著 b ∈ {a}
        rw [h_eq_pair_singleton] at hb_in_pair -- 將 {a, b} 重寫為 {a}，得到 b ∈ {a}
        rw [ZFSet.mem_singleton] at hb_in_pair -- 將 b ∈ {a} 轉換為 b = a
        exact hb_in_pair -- b = a
      -- 類似地，{a, b'} = {a}，所以 b' = a
      have hb'_eq_a : b' = a := by -- 證明 b' = a
        -- 因為 ordered_pair a b = ordered_pair a' b' 且 a = a'，所以 ordered_pair a b = ordered_pair a b'
        have h_eq_ab' : ordered_pair a b = ordered_pair a b' := by -- 證明 ordered_pair a b = ordered_pair a b'
          -- 從 h_eq : ordered_pair a b = ordered_pair a' b' 和 ha_eq : a = a'，我們可以得到 ordered_pair a b = ordered_pair a b'
          -- 因為 a = a'，所以 ordered_pair a' b' = ordered_pair a b'
          have h_eq_right : ordered_pair a' b' = ordered_pair a b' := by -- 證明 ordered_pair a' b' = ordered_pair a b'
            rw [ha_eq] -- 將 a' 重寫為 a
          -- 使用等式的傳遞性：ordered_pair a b = ordered_pair a' b' = ordered_pair a b'
          exact Eq.trans h_eq h_eq_right -- ordered_pair a b = ordered_pair a b'
        have h_ab'_in : {a, b'} ∈ ordered_pair a b' := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b'} = {a, b'}，所以 {a, b'} ∈ {{a}, {a, b'}}
        rw [← h_eq_ab', ordered_pair] at h_ab'_in -- 因為 ordered_pair a b = ordered_pair a b'，展開定義得到 {a, b'} ∈ {{a}, {a, b}}
        rw [ZFSet.mem_pair] at h_ab'_in -- 將 {a, b'} ∈ {{a}, {a, b}} 拆成 {a, b'} = {a} ∨ {a, b'} = {a, b}
        cases h_ab'_in with
        | inl h => -- {a, b'} = {a}
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [h] at hb'_in -- 將 {a, b'} 重寫為 {a}，得到 b' ∈ {a}
          rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
          exact hb'_in -- b' = a
        | inr h => -- {a, b'} = {a, b}
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [h] at hb'_in -- 將 {a, b'} 重寫為 {a, b}，得到 b' ∈ {a, b}
          -- 因為 h_eq_pair_singleton : {a, b} = {a}，所以 b' ∈ {a, b} 意味著 b' ∈ {a}
          rw [h_eq_pair_singleton] at hb'_in -- 將 {a, b} 重寫為 {a}，得到 b' ∈ {a}
          rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
          exact hb'_in -- b' = a
      rw [hb_eq_a, hb'_eq_a] -- 將 b 和 b' 都重寫為 a
      exact ⟨ha_eq, rfl⟩ -- a = a' 且 a = a
    | inr h_eq_pair => -- 情況1.2：{a, b} = {a', b'}（注意：這裡的 {a', b'} 需要重寫為 {a, b'}）
      -- 這意味著 {a, b} 和 {a, b'} 有相同的元素
      have hb_eq_b' : b = b' := by -- 證明 b = b'
        -- 因為 {a, b} = {a', b'}，所以 b ∈ {a, b} 當且僅當 b ∈ {a', b'}
        have hb_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        -- h_eq_pair 是 {a, b} = {a', b'}，需要將 a' 重寫為 a
        rw [ha_eq.symm] at h_eq_pair -- 將 a' 重寫為 a，得到 {a, b} = {a, b'}
        rw [h_eq_pair] at hb_in -- 將 {a, b} 重寫為 {a, b'}，得到 b ∈ {a, b'}
        rw [ZFSet.mem_pair] at hb_in -- 將 b ∈ {a, b'} 拆成 b = a ∨ b = b'
        cases hb_in with
        | inl hb_eq_a => -- 情況1.2.1：b = a
          -- 類似地，b' ∈ {a, b'}，所以 b' = a 或 b' = b'
          have hb'_in : b' ∈ {a, b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a, b'}
          rw [← h_eq_pair] at hb'_in -- 將 {a, b'} 重寫為 {a, b}，得到 b' ∈ {a, b}
          rw [ZFSet.mem_pair] at hb'_in -- 將 b' ∈ {a, b} 拆成 b' = a ∨ b' = b
          cases hb'_in with
          | inl hb'_eq_a => rw [hb_eq_a, hb'_eq_a] -- b = a 且 b' = a，所以 b = b'
          | inr hb'_eq_b => -- b' = b
            rw [hb_eq_a] at hb'_eq_b -- 將 b 重寫為 a，得到 b' = a
            rw [hb'_eq_b] -- 將 b' 重寫為 a，目標變成 b = a
            exact hb_eq_a -- b = a
        | inr hb_eq_b' => exact hb_eq_b' -- b = b'，直接成立
      exact ⟨ha_eq, hb_eq_b'⟩ -- a = a' 且 b = b'
  | inr h_eq_singleton_pair => -- 情況2：{a} = {a', b'}
    -- 這意味著 {a} 有兩個元素 a' 和 b'，但 {a} 只有一個元素 a，所以 a' = b' = a
    have ha'_in : a' ∈ {a', b'} := ZFSet.mem_pair.mpr (Or.inl rfl) -- a' = a'，所以 a' ∈ {a', b'}
    rw [← h_eq_singleton_pair] at ha'_in -- 將 {a', b'} 重寫為 {a}，得到 a' ∈ {a}
    rw [ZFSet.mem_singleton] at ha'_in -- 將 a' ∈ {a} 轉換為 a' = a
    have hb'_in : b' ∈ {a', b'} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b' = b'，所以 b' ∈ {a', b'}
    rw [← h_eq_singleton_pair] at hb'_in -- 將 {a', b'} 重寫為 {a}，得到 b' ∈ {a}
    rw [ZFSet.mem_singleton] at hb'_in -- 將 b' ∈ {a} 轉換為 b' = a
    -- 現在我們有 a' = a 且 b' = a，所以 ordered_pair a' b' = {{a}, {a, a}} = {{a}}
    -- 類似地，我們需要證明 a = a' 且 b = a
    have h_ab_in : {a, b} ∈ ordered_pair a b := ZFSet.mem_pair.mpr (Or.inr rfl) -- {a, b} = {a, b}，所以 {a, b} ∈ {{a}, {a, b}}
    rw [h_eq] at h_ab_in -- 因為 ordered_pair a b = ordered_pair a' b'，所以 {a, b} ∈ ordered_pair a' b'
    rw [ordered_pair] at h_ab_in -- 展開 ordered_pair a' b' 的定義，得到 {a, b} ∈ {{a'}, {a', b'}}
    rw [ha'_in, hb'_in] at h_ab_in -- 將 a' 和 b' 都重寫為 a，得到 {a, b} ∈ {{a}, {a, a}}
    -- 注意：{a, a} = {a}，所以 {{a}, {a, a}} = {{a}}
    have h_pair_eq : ({a, a} : ZFSet) = ({a} : ZFSet) := by -- 證明 {a, a} = {a}，明確類型為 ZFSet
      apply ZFSet.ext -- 使用外延性公設
      intro x -- x : any arbitrary element
      constructor -- 將 ↔ 分成兩個部分
      · intro hx_aa -- hx_aa : x ∈ {a, a}
        rw [ZFSet.mem_pair] at hx_aa -- 將 x ∈ {a, a} 拆成 x = a ∨ x = a
        cases hx_aa with
        | inl hx_eq => -- x = a
          rw [ZFSet.mem_singleton] -- 將目標 x ∈ {a} 轉換為 x = a
          exact hx_eq -- x = a
        | inr hx_eq => -- x = a
          rw [ZFSet.mem_singleton] -- 將目標 x ∈ {a} 轉換為 x = a
          exact hx_eq -- x = a
      · intro hx_a -- hx_a : x ∈ {a}
        rw [ZFSet.mem_singleton] at hx_a -- 將 x ∈ {a} 轉換為 x = a
        rw [hx_a] -- 將 x 重寫為 a
        rw [ZFSet.mem_pair] -- 將 a ∈ {a, a} 拆成 a = a ∨ a = a
        left
        rfl -- a = a
    rw [h_pair_eq] at h_ab_in -- 將 {a, a} 重寫為 {a}，得到 {a, b} ∈ {{a}}
    rw [ZFSet.mem_pair] at h_ab_in -- 將 {a, b} ∈ {{a}} 拆成 {a, b} = {a} ∨ {a, b} = {a}
    cases h_ab_in with
    | inl h => -- {a, b} = {a}
      have hb_eq_a : b = a := by -- 證明 b = a
        have hb_in : b ∈ {a, b} := ZFSet.mem_pair.mpr (Or.inr rfl) -- b = b，所以 b ∈ {a, b}
        rw [h] at hb_in -- 將 {a, b} 重寫為 {a}，得到 b ∈ {a}
        rw [ZFSet.mem_singleton] at hb_in -- 將 b ∈ {a} 轉換為 b = a
        exact hb_in -- b = a
      rw [ha'_in, hb'_in, hb_eq_a] -- 將 a', b', b 都重寫為 a
      exact ⟨rfl, rfl⟩ -- a = a 且 a = a
```

**詳細步驟解析：**

#### 第一步：證明 `a = a'`

**目標：** 從 `ordered_pair a b = ordered_pair a' b'` 推導出 `a = a'`

**策略：** 利用 `{a}` 是 `ordered_pair a b` 的元素，所以它也是 `ordered_pair a' b'` 的元素。

**步驟：**
1. `have h_a_in : {a} ∈ ordered_pair a b`：因為 `{a} = {a}`，所以 `{a} ∈ {{a}, {a, b}}`
2. `rw [h_eq] at h_a_in`：因為 `ordered_pair a b = ordered_pair a' b'`，所以 `{a} ∈ ordered_pair a' b'`
3. `rw [ordered_pair] at h_a_in`：展開定義，得到 `{a} ∈ {{a'}, {a', b'}}`
4. `rw [ZFSet.mem_pair] at h_a_in`：將成員關係拆成 `{a} = {a'} ∨ {a} = {a', b'}`
5. `cases h_a_in`：分情況討論

**情況 1：`{a} = {a'}`**
- 使用外延性公設：`a ∈ {a}` 當且僅當 `a ∈ {a'}`
- 因為 `a ∈ {a}`，所以 `a ∈ {a'}`，即 `a = a'`

**情況 2：`{a} = {a', b'}`**
- 這意味著 `{a}` 有兩個元素 `a'` 和 `b'`
- 但 `{a}` 只有一個元素 `a`，所以 `a' = b' = a`
- 因此 `a = a'`（因為 `a' = a`）

#### 第二步：證明 `b = b'`

**目標：** 在已知 `a = a'` 的情況下，證明 `b = b'`

**策略：** 利用 `{a, b}` 是 `ordered_pair a b` 的元素，所以它也是 `ordered_pair a' b'` 的元素。

**步驟：**
1. `have h_ab_in : {a, b} ∈ ordered_pair a b`：因為 `{a, b} = {a, b}`，所以 `{a, b} ∈ {{a}, {a, b}}`
2. `rw [h_eq] at h_ab_in`：因為 `ordered_pair a b = ordered_pair a' b'`，所以 `{a, b} ∈ ordered_pair a' b'`
3. `rw [ordered_pair] at h_ab_in`：展開定義，得到 `{a, b} ∈ {{a'}, {a', b'}}`
4. `rw [ha_eq] at h_ab_in`：將 `a'` 重寫為 `a`，得到 `{a, b} ∈ {{a}, {a, b'}}`
5. `rw [ZFSet.mem_pair] at h_ab_in`：將成員關係拆成 `{a, b} = {a} ∨ {a, b} = {a, b'}`
6. `cases h_ab_in`：分情況討論

**情況 1.1：`{a, b} = {a}`**
- 這意味著 `{a, b}` 只有一個元素 `a`，所以 `b = a`
- 類似地，我們可以證明 `b' = a`
- 因此 `b = b'`（因為 `b = a = b'`）

**情況 1.2：`{a, b} = {a, b'}`**
- 這意味著 `{a, b}` 和 `{a, b'}` 有相同的元素
- 因為 `b ∈ {a, b}`，所以 `b ∈ {a, b'}`，即 `b = a` 或 `b = b'`
- 如果 `b = a`，則類似地可以證明 `b' = a`，所以 `b = b'`
- 如果 `b = b'`，則直接成立

**關鍵技巧：**

1. **使用成員關係**：
   - `{a} ∈ ordered_pair a b` 和 `{a, b} ∈ ordered_pair a b` 是關鍵觀察
   - 利用等式的傳遞性：如果 `ordered_pair a b = ordered_pair a' b'`，則它們的元素相同

2. **重寫變數**：
   - 使用 `rw [ha_eq]` 將 `a'` 重寫為 `a`
   - 使用 `rw [ha_eq.symm]` 將 `a'` 重寫為 `a`（當需要反向重寫時）

3. **情況分析**：
   - 使用 `cases` 處理析取（`{a} = {a'} ∨ {a} = {a', b'}`）
   - 使用 `cases` 處理析取（`{a, b} = {a} ∨ {a, b} = {a, b'}`）

4. **處理特殊情況**：
   - 當 `{a, b} = {a}` 時，需要證明 `b = a`
   - 當 `{a} = {a', b'}` 時，需要證明 `a' = b' = a`
   - 當 `{a, a} = {a}` 時，需要使用外延性公設證明

5. **等式的傳遞性**：
   - 使用 `Eq.trans` 證明 `ordered_pair a b = ordered_pair a' b' = ordered_pair a b'`

**為什麼這個證明很重要？**

1. **確保有序對的唯一性**：
   - 不同的有序對對應不同的集合表示
   - 這是 Kuratowski 定義的核心性質

2. **支持笛卡爾積的構造**：
   - 有序對的單射性質確保了笛卡爾積中沒有重複的元素
   - 這對於後續定義關係和函數非常重要

3. **證明技巧的綜合應用**：
   - 這個證明綜合運用了成員關係、外延性公設、情況分析等多種技巧
   - 是學習集合論證明的優秀範例

**記憶要點：**
- 有序對的單射性質：`ordered_pair a b = ordered_pair a' b' → a = a' ∧ b = b'`
- 關鍵觀察：`{a} ∈ ordered_pair a b` 和 `{a, b} ∈ ordered_pair a b`
- 重寫技巧：使用 `ha_eq.symm` 將 `a'` 重寫為 `a`
- 情況分析：處理 `{a} = {a'} ∨ {a} = {a', b'}` 和 `{a, b} = {a} ∨ {a, b} = {a, b'}`
- 特殊情況：`{a, a} = {a}` 需要使用外延性公設證明

---

### 範例 17：笛卡爾積對聯集的分配律

**定理：** `A × (B ∪ C) = (A × B) ∪ (A × C)`，即 `product A (B ∪ C) = product A B ∪ product A C`

這是笛卡爾積對聯集的分配律。它說明：集合 `A` 與 `B` 和 `C` 的聯集的笛卡爾積，等於 `A` 與 `B` 的笛卡爾積和 `A` 與 `C` 的笛卡爾積的聯集。

這個定理展示了：
- 笛卡爾積運算與聯集運算之間的關係
- 如何使用笛卡爾積的成員關係進行證明
- 如何使用情況分析處理聯集成員關係
- 如何使用 `rcases` 處理嵌套的存在量詞

**完整證明：**

```lean
theorem theorem_2_2_3_a (A B C : ZFSet) : product A (B ∪ C) = product A B ∪ product A C := by
  apply ZFSet.ext -- 根據外延性公設，將 product A (B ∪ C) = product A B ∪ product A C 轉換為 ∀ x, x ∈ product A (B ∪ C) ↔ x ∈ product A B ∪ product A C
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個部分
  · intro hx_product -- hx_product : x ∈ product A (B ∪ C)
    -- x ∈ product A (B ∪ C) → x ∈ product A B ∪ product A C
    rw [product] at hx_product -- 展開 product 的定義
    rw [ZFSet.mem_sep] at hx_product -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
    rcases hx_product with ⟨hx_in_powerset, h_exists⟩ -- 分解分離公設的成員關係，h_exists : ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b
    rcases h_exists with ⟨a, ha, b, hb, hx_eq⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B ∪ C, hx_eq : x = ordered_pair a b
    -- 現在我們有：a ∈ A, b ∈ B ∪ C, x = ordered_pair a b
    rw [ZFSet.mem_union] at hb -- 將 b ∈ B ∪ C 拆成 b ∈ B ∨ b ∈ C
    cases hb with
    | inl hb_B => -- 情況1：b ∈ B
      have hx_in_product_B : x ∈ product A B := by -- 證明 x ∈ product A B
        rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
        exact ⟨a, ha, b, hb_B, rfl⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
      exact ZFSet.mem_union.mpr (Or.inl hx_in_product_B) -- x ∈ product A B，所以 x ∈ product A B ∪ product A C
    | inr hb_C => -- 情況2：b ∈ C
      have hx_in_product_C : x ∈ product A C := by -- 證明 x ∈ product A C
        rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
        exact ⟨a, ha, b, hb_C, rfl⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ C
      exact ZFSet.mem_union.mpr (Or.inr hx_in_product_C) -- x ∈ product A C，所以 x ∈ product A B ∪ product A C
  · intro hx_union -- hx_union : x ∈ product A B ∪ product A C
    -- x ∈ product A B ∪ product A C → x ∈ product A (B ∪ C)
    rw [ZFSet.mem_union] at hx_union -- 將 x ∈ product A B ∪ product A C 拆成 x ∈ product A B ∨ x ∈ product A C
    cases hx_union with
    | inl hx_product_B => -- 情況1：x ∈ product A B
      rw [mem_product] at hx_product_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
      rcases hx_product_B with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, x = ordered_pair a b
      have hb_union : b ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inl hb) -- b ∈ B，所以 b ∈ B ∪ C
      rw [mem_product] -- 使用笛卡爾積的成員關係
      exact ⟨a, ha, b, hb_union, rfl⟩ -- x = ordered_pair a b, a ∈ A, b ∈ B ∪ C
    | inr hx_product_C => -- 情況2：x ∈ product A C
      rw [mem_product] at hx_product_C -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ C, x = ordered_pair a b
      rcases hx_product_C with ⟨a, ha, b, hb, rfl⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ C, x = ordered_pair a b
      have hb_union : b ∈ B ∪ C := ZFSet.mem_union.mpr (Or.inr hb) -- b ∈ C，所以 b ∈ B ∪ C
      rw [mem_product] -- 使用笛卡爾積的成員關係
      exact ⟨a, ha, b, hb_union, rfl⟩ -- x = ordered_pair a b, a ∈ A, b ∈ B ∪ C
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ product A (B ∪ C) → x ∈ product A B ∪ product A C`

**目標：** 證明如果 `x ∈ product A (B ∪ C)`，則 `x ∈ product A B ∪ product A C`

**步驟 1：展開定義並分解成員關係**
- `rw [product] at hx_product`：展開 `product` 的定義，得到 `x ∈ ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b) (powerset (powerset (A ∪ B ∪ C)))`
- `rw [ZFSet.mem_sep] at hx_product`：使用分離公設的成員關係，得到 `x ∈ powerset (powerset (A ∪ B ∪ C)) ∧ ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b`
- `rcases hx_product with ⟨hx_in_powerset, h_exists⟩`：分解合取，得到 `h_exists : ∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b`

**步驟 2：分解嵌套的存在量詞**
- `rcases h_exists with ⟨a, ha, b, hb, hx_eq⟩`：使用 `rcases` 一次性分解嵌套的存在量詞
  - `a : ZFSet`：存在的元素 `a`
  - `ha : a ∈ A`：`a` 屬於 `A` 的證明
  - `b : ZFSet`：存在的元素 `b`
  - `hb : b ∈ B ∪ C`：`b` 屬於 `B ∪ C` 的證明
  - `hx_eq : x = ordered_pair a b`：`x` 等於 `ordered_pair a b` 的證明

**為什麼使用 `rcases` 而不是嵌套的 `cases`？**

- `∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b` 是嵌套的存在量詞
- `∃ a ∈ A` 實際上是 `∃ a, a ∈ A ∧ ...` 的簡寫
- `cases` 一次只能處理一個存在量詞，需要嵌套使用
- `rcases` 可以一次性處理多個嵌套的存在量詞，更簡潔

**步驟 3：分解聯集成員關係**
- `rw [ZFSet.mem_union] at hb`：將 `b ∈ B ∪ C` 轉換為 `b ∈ B ∨ b ∈ C`
- `cases hb`：分情況討論

**情況 1：`b ∈ B`**
- `inl hb_B`：`hb_B : b ∈ B`
- `have hx_in_product_B : x ∈ product A B`：證明 `x ∈ product A B`
  - `rw [mem_product, hx_eq]`：
    - `mem_product`：展開 `mem_product` 定理，目標變成 `∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
    - `hx_eq`：將 `x` 重寫為 `ordered_pair a b`，目標變成 `∃ a ∈ A, ∃ b ∈ B, ordered_pair a b = ordered_pair a b`
  - `exact ⟨a, ha, b, hb_B, rfl⟩`：構造存在量詞
    - `a`：存在的元素 `a`
    - `ha`：`a ∈ A` 的證明
    - `b`：存在的元素 `b`
    - `hb_B`：`b ∈ B` 的證明
    - `rfl`：`ordered_pair a b = ordered_pair a b` 的證明（自反性）
- `exact ZFSet.mem_union.mpr (Or.inl hx_in_product_B)`：因為 `x ∈ product A B`，所以 `x ∈ product A B ∪ product A C`（使用 `Or.inl` 選擇左分支）

**情況 2：`b ∈ C`**
- `inr hb_C`：`hb_C : b ∈ C`
- `have hx_in_product_C : x ∈ product A C`：證明 `x ∈ product A C`
  - 類似情況 1，但使用 `hb_C : b ∈ C`
- `exact ZFSet.mem_union.mpr (Or.inr hx_in_product_C)`：因為 `x ∈ product A C`，所以 `x ∈ product A B ∪ product A C`（使用 `Or.inr` 選擇右分支）

**關鍵理解：**
- 如果 `x ∈ product A (B ∪ C)`，則存在 `a ∈ A` 和 `b ∈ B ∪ C`，使得 `x = (a, b)`
- 因為 `b ∈ B ∪ C`，所以 `b ∈ B` 或 `b ∈ C`
- 如果 `b ∈ B`，則 `x ∈ product A B`
- 如果 `b ∈ C`，則 `x ∈ product A C`
- 因此 `x ∈ product A B ∪ product A C`

#### 第二個方向：`x ∈ product A B ∪ product A C → x ∈ product A (B ∪ C)`

**目標：** 證明如果 `x ∈ product A B ∪ product A C`，則 `x ∈ product A (B ∪ C)`

**步驟 1：分解聯集成員關係**
- `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ product A B ∪ product A C` 轉換為 `x ∈ product A B ∨ x ∈ product A C`
- `cases hx_union`：分情況討論

**情況 1：`x ∈ product A B`**
- `inl hx_product_B`：`hx_product_B : x ∈ product A B`
- `rw [mem_product] at hx_product_B`：使用笛卡爾積的成員關係，得到 `∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
- `rcases hx_product_B with ⟨a, ha, b, hb, rfl⟩`：分解存在量詞
  - `a : ZFSet`：存在的元素 `a`
  - `ha : a ∈ A`：`a` 屬於 `A` 的證明
  - `b : ZFSet`：存在的元素 `b`
  - `hb : b ∈ B`：`b` 屬於 `B` 的證明
  - `rfl`：`x = ordered_pair a b` 的證明（這裡使用 `rfl` 會自動將 `x` 重寫為 `ordered_pair a b`）
- `have hb_union : b ∈ B ∪ C`：證明 `b ∈ B ∪ C`
  - `ZFSet.mem_union.mpr (Or.inl hb)`：因為 `b ∈ B`，所以 `b ∈ B ∪ C`（使用 `Or.inl` 選擇左分支）
- `rw [mem_product]`：使用笛卡爾積的成員關係，目標變成 `∃ a ∈ A, ∃ b ∈ B ∪ C, x = ordered_pair a b`
- `exact ⟨a, ha, b, hb_union, rfl⟩`：構造存在量詞
  - `a`：存在的元素 `a`
  - `ha`：`a ∈ A` 的證明
  - `b`：存在的元素 `b`
  - `hb_union`：`b ∈ B ∪ C` 的證明
  - `rfl`：`x = ordered_pair a b` 的證明

**情況 2：`x ∈ product A C`**
- `inr hx_product_C`：`hx_product_C : x ∈ product A C`
- 類似情況 1，但使用 `hb : b ∈ C` 和 `Or.inr` 來證明 `b ∈ B ∪ C`

**關鍵理解：**
- 如果 `x ∈ product A B ∪ product A C`，則 `x ∈ product A B` 或 `x ∈ product A C`
- 如果 `x ∈ product A B`，則存在 `a ∈ A` 和 `b ∈ B`，使得 `x = (a, b)`
- 因為 `b ∈ B`，所以 `b ∈ B ∪ C`
- 因此 `x ∈ product A (B ∪ C)`
- 類似地，如果 `x ∈ product A C`，也可以證明 `x ∈ product A (B ∪ C)`

**為什麼這個定理很重要？**

1. **展示分配律**：
   - 這是笛卡爾積運算的一個基本性質
   - 類似於數的乘法對加法的分配律：`a × (b + c) = a × b + a × c`

2. **實際應用**：
   - 在處理關係和函數時，經常需要處理笛卡爾積的運算
   - 這個定理允許我們將複雜的笛卡爾積表達式分解為更簡單的形式

3. **直觀理解**：
   - `A × (B ∪ C)` 包含所有形如 `(a, b)` 的有序對，其中 `a ∈ A` 且 `b ∈ B` 或 `b ∈ C`
   - `(A × B) ∪ (A × C)` 包含所有形如 `(a, b)` 的有序對，其中 `a ∈ A` 且 `b ∈ B`，或者 `a ∈ A` 且 `b ∈ C`
   - 這兩個集合包含相同的元素

**關鍵技巧總結：**

1. **使用 `rcases` 處理嵌套的存在量詞**：
   - `rcases h_exists with ⟨a, ha, b, hb, hx_eq⟩` 可以一次性分解多個嵌套的存在量詞
   - 比嵌套的 `cases` 更簡潔和易讀

2. **使用 `rfl` 進行等式重寫**：
   - 在 `rcases` 中使用 `rfl` 可以自動將變數重寫為等式的右邊
   - 例如：`rcases h with ⟨a, ha, rfl⟩` 會將目標中的變數重寫為 `a`

3. **情況分析的使用**：
   - 使用 `cases` 處理析取（`b ∈ B ∨ b ∈ C`）
   - 使用 `cases` 處理析取（`x ∈ product A B ∨ x ∈ product A C`）

4. **構造存在量詞**：
   - 使用 `⟨a, ha, b, hb, rfl⟩` 構造存在量詞
   - 需要提供存在的元素和它們滿足條件的證明

5. **使用 `have` 建立中間結果**：
   - 使用 `have` 來建立中間步驟，使證明更清晰
   - 例如：`have hx_in_product_B : x ∈ product A B := by ...`

**記憶要點：**
- `A × (B ∪ C) = (A × B) ∪ (A × C)` 是笛卡爾積對聯集的分配律
- 證明時需要使用外延性公理
- 第一個方向：如果 `x ∈ product A (B ∪ C)`，則 `x ∈ product A B ∪ product A C`
- 第二個方向：如果 `x ∈ product A B ∪ product A C`，則 `x ∈ product A (B ∪ C)`
- 使用 `rcases` 處理嵌套的存在量詞：`rcases h with ⟨a, ha, b, hb, hx_eq⟩`
- 使用 `cases` 處理析取：`cases hb with | inl hb_B => ... | inr hb_C => ...`
- 使用 `rfl` 進行等式重寫：在 `rcases` 中使用 `rfl` 可以自動重寫變數
- 使用 `have` 建立中間結果：使證明更清晰和易讀
- 笛卡爾積的成員關係：`x ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
- 聯集的成員關係：`x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`

---

### 範例 18：笛卡爾積與空集合

**定理：** `A × ∅ = ∅`，即 `product A ∅ = ∅`

這個定理說明：任何集合 `A` 與空集合的笛卡爾積等於空集合。這是因為笛卡爾積 `A × ∅` 中的元素都是有序對 `(a, b)`，其中 `a ∈ A` 且 `b ∈ ∅`。但空集合沒有元素，所以不存在這樣的 `b`，因此 `A × ∅` 是空集合。

**完整證明：**

```lean
theorem theorem_2_2_3_c (A : ZFSet) : product A ∅ = ∅ := by
  apply ZFSet.ext -- 根據外延性公設，將 product A ∅ = ∅ 轉換為 ∀ x, x ∈ product A ∅ ↔ x ∈ ∅
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_product -- hx_product : x ∈ product A ∅
    -- x ∈ product A ∅ → x ∈ ∅
    rw [product] at hx_product -- 展開 product 的定義：product A ∅ = ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ ∅)))
    rw [ZFSet.mem_sep] at hx_product -- 使用分離公設的成員關係：x ∈ ZFSet.sep P A ↔ x ∈ A ∧ P x
    rcases hx_product with ⟨ hx_in_powerset, h_exists ⟩ -- 分解分離公設的成員關係，h_exists : ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b
    rcases h_exists with ⟨ a, ha, b, hb, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ ∅, x = ordered_pair a b
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ ∅
    -- 但空集合沒有元素，所以矛盾
    exact False.elim (ZFSet.notMem_empty b hb)  -- b ∈ ∅，但空集合沒有元素，所以矛盾
  · intro hx_empty -- hx_empty : x ∈ ∅
    -- x ∈ ∅ → x ∈ product A ∅（空真命題：如果 x ∈ ∅，則可以推出任何命題）
    exact False.elim (ZFSet.notMem_empty x hx_empty) -- x ∈ ∅，但空集合沒有元素，所以矛盾
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ product A ∅ → x ∈ ∅`

**目標：** 證明如果 `x ∈ product A ∅`，則 `x ∈ ∅`

**策略：** 使用反證法。假設 `x ∈ product A ∅`，則存在 `a ∈ A` 和 `b ∈ ∅`，使得 `x = ordered_pair a b`。但空集合沒有元素，所以 `b ∈ ∅` 是不可能的，產生矛盾。

**步驟：**
1. `rw [product] at hx_product`：展開 `product` 的定義，得到 `x ∈ ZFSet.sep (fun x => ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b) (ZFSet.powerset (ZFSet.powerset (A ∪ ∅)))`
2. `rw [ZFSet.mem_sep] at hx_product`：使用分離公設的成員關係，得到 `x ∈ powerset (powerset (A ∪ ∅)) ∧ ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b`
3. `rcases hx_product with ⟨ hx_in_powerset, h_exists ⟩`：分解合取，得到存在量詞 `h_exists : ∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b`
4. `rcases h_exists with ⟨ a, ha, b, hb, hx_eq ⟩`：分解存在量詞，得到 `a ∈ A`、`b ∈ ∅` 和 `x = ordered_pair a b`
5. `exact False.elim (ZFSet.notMem_empty b hb)`：因為 `b ∈ ∅` 是不可能的（空集合沒有元素），所以產生矛盾

**關鍵理解：**
- `ZFSet.notMem_empty b hb` 的簽名是 `(b : ZFSet) → (hb : b ∈ ∅) → False`
- 第一個參數是屬於空集合的元素（`b`），第二個參數是該元素屬於空集合的證明（`hb`）
- 這會產生 `False`，然後使用 `False.elim` 推出目標

#### 第二個方向：`x ∈ ∅ → x ∈ product A ∅`

**目標：** 證明如果 `x ∈ ∅`，則 `x ∈ product A ∅`

**策略：** 這是空真命題（vacuous truth）。如果 `x ∈ ∅`，則可以推出任何命題，包括 `x ∈ product A ∅`。但 `x ∈ ∅` 是不可能的（空集合沒有元素），所以直接使用矛盾。

**步驟：**
1. `intro hx_empty`：引入假設 `hx_empty : x ∈ ∅`
2. `exact False.elim (ZFSet.notMem_empty x hx_empty)`：因為 `x ∈ ∅` 是不可能的（空集合沒有元素），所以產生矛盾

**關鍵理解：**
- 空真命題：如果前提是假的，則蘊含式自動為真
- 但這裡我們直接使用矛盾來完成證明，因為 `x ∈ ∅` 是不可能的

**為什麼這個定理很重要？**

1. **展示笛卡爾積的性質**：
   - 笛卡爾積 `A × B` 中的元素都是有序對 `(a, b)`，其中 `a ∈ A` 且 `b ∈ B`
   - 如果 `B = ∅`，則不存在 `b ∈ B`，所以 `A × ∅ = ∅`

2. **反證法的應用**：
   - 這個證明展示了如何使用反證法
   - 通過假設存在性，然後推導出矛盾

3. **空真命題的處理**：
   - 第二個方向展示了如何處理空真命題
   - 雖然前提是假的，但我們仍然可以完成證明

**關鍵技巧總結：**

1. **使用外延性公設**：
   - `apply ZFSet.ext`：將集合等式轉換為雙向蘊含

2. **展開定義**：
   - `rw [product]`：展開 `product` 的定義
   - `rw [ZFSet.mem_sep]`：使用分離公設的成員關係

3. **分解存在量詞**：
   - `rcases`：分解嵌套的存在量詞 `∃ a ∈ A, ∃ b ∈ ∅, x = ordered_pair a b`

4. **使用矛盾**：
   - `ZFSet.notMem_empty b hb`：從 `b ∈ ∅` 推出矛盾
   - `False.elim`：從矛盾推出任何命題

**記憶要點：**
- 笛卡爾積與空集合：`A × ∅ = ∅` 和 `∅ × A = ∅`
- 關鍵觀察：笛卡爾積中的元素都是有序對 `(a, b)`，其中 `a ∈ A` 且 `b ∈ B`
- 如果 `B = ∅`，則不存在 `b ∈ B`，所以 `A × ∅ = ∅`
- 使用 `ZFSet.notMem_empty` 處理空集合的成員關係
- 第一個參數是屬於空集合的元素，第二個參數是該元素屬於空集合的證明

---

### 範例 19：笛卡爾積與交集的關係

**定理：** `(A × B) ∩ (C × D) = (A ∩ C) × (B ∩ D)`，即 `product A B ∩ product C D = product (A ∩ C) (B ∩ D)`

這個定理說明：兩個笛卡爾積的交集等於對應集合的交集的笛卡爾積。這是笛卡爾積與交集運算之間的重要關係。

**完整證明：**

```lean
theorem theorem_2_2_3_d (A B C D : ZFSet) : product A B ∩ product C D = product (A ∩ C) (B ∩ D) := by
  apply ZFSet.ext -- 根據外延性公設，將 (A ⨯ B) ∩ (C ⨯ D) = (A ∩ C) ⨯ (B ∩ D) 轉換為 ∀ x, x ∈ (A ⨯ B) ∩ (C ⨯ D) ↔ x ∈ (A ∩ C) ⨯ (B ∩ D)
  intro x -- x : any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ (A ⨯ B) ∩ (C ⨯ D)
    -- x ∈ (A ⨯ B) ∩ (C ⨯ D) → x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ (A ⨯ B) ∩ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rcases hx_inter with ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- 分解交集成員關係，得到 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B
    rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
    rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq2 ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq2 : x = ordered_pair c d
    -- 現在我們有：x = ordered_pair c d, c ∈ C, d ∈ D
    -- 因為 x = ordered_pair a b ∧ x = ordered_pair c d，所以 ordered_pair a b = ordered_pair c d
    have h_eq_pair : ordered_pair a b = ordered_pair c d := by
      rw [← hx_eq] -- 將 ordered_pair a b 重寫為 x
      exact hx_eq2 -- x = ordered_pair c d
    -- 使用有序對單射性質，得到 a = c ∧ b = d
    have h_eq_components : a = c ∧ b = d := ordered_pair_inj a b c d h_eq_pair
    rcases h_eq_components with ⟨ ha_eq_c, hb_eq_d ⟩ -- 分解等式，得到 a = c ∧ b = d
    have ha_in_C : a ∈ C := by
      rw [ha_eq_c] -- 將 a 重寫為 c
      exact hc -- c ∈ C
    have hb_in_D : b ∈ D := by
      rw [hb_eq_d] -- 將 b 重寫為 d
      exact hd_D -- d ∈ D
    have ha_in_inter_A_C : a ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨ ha, ha_in_C ⟩ -- a ∈ A ∧ a ∈ C
    have hb_in_inter_B_D : b ∈ B ∩ D := ZFSet.mem_inter.mpr ⟨ hb_B, hb_in_D ⟩ -- b ∈ B ∧ b ∈ D
    rw [mem_product] -- 展開目標為 ∃ a' ∈ A ∩ C, ∃ b' ∈ B ∩ D, x = ordered_pair a' b'
    rw [hx_eq] -- 將 x 重寫為 ordered_pair a b
    exact ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, rfl ⟩
  · intro hx_product -- hx_product : x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [mem_product] at hx_product -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A ∩ C, ∃ b ∈ B ∩ D, x = ordered_pair a b
    rcases hx_product with ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A ∩ C, b ∈ B ∩ D, hx_eq : x = ordered_pair a b
    rw [ZFSet.mem_inter] at ha_in_inter_A_C -- 將 a ∈ A ∩ C 拆成 a ∈ A ∧ a ∈ C
    rcases ha_in_inter_A_C with ⟨ ha_in_A, ha_in_C ⟩ -- 分解交集成員關係，得到 a ∈ A ∧ a ∈ C
    rw [ZFSet.mem_inter] at hb_in_inter_B_D -- 將 b ∈ B ∩ D 拆成 b ∈ B ∧ b ∈ D
    rcases hb_in_inter_B_D with ⟨ hb_in_B, hb_in_D ⟩ -- 分解交集成員關係，得到 b ∈ B ∧ b ∈ D
    have hx_in_product_A_B : x ∈ product A B := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_A, b, hb_in_B, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    have hx_in_product_C_D : x ∈ product C D := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_C, b, hb_in_D, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ C, b ∈ D
    exact ZFSet.mem_inter.mpr ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- x ∈ (A ⨯ B) ∩ (C ⨯ D)
```

**詳細步驟解析：**

#### 第一個方向：`x ∈ (A × B) ∩ (C × D) → x ∈ (A ∩ C) × (B ∩ D)`

**目標：** 證明如果 `x` 同時屬於 `A × B` 和 `C × D`，則 `x` 屬於 `(A ∩ C) × (B ∩ D)`

**策略：** 
1. 從 `x ∈ A × B` 得到 `x = (a, b)`，其中 `a ∈ A, b ∈ B`
2. 從 `x ∈ C × D` 得到 `x = (c, d)`，其中 `c ∈ C, d ∈ D`
3. 因為 `(a, b) = (c, d)`，使用有序對的單射性質得到 `a = c` 且 `b = d`
4. 因此 `a ∈ A ∩ C` 且 `b ∈ B ∩ D`，所以 `x ∈ (A ∩ C) × (B ∩ D)`

**步驟：**
1. `rw [ZFSet.mem_inter] at hx_inter`：將 `x ∈ (A × B) ∩ (C × D)` 拆成 `x ∈ A × B ∧ x ∈ C × D`
2. `rcases hx_inter with ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩`：分解合取
3. `rw [mem_product] at hx_in_product_A_B`：展開 `x ∈ A × B` 為 `∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
4. `rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩`：分解存在量詞，得到 `a ∈ A, b ∈ B, x = ordered_pair a b`
5. 類似地，從 `x ∈ C × D` 得到 `c ∈ C, d ∈ D, x = ordered_pair c d`
6. `have h_eq_pair : ordered_pair a b = ordered_pair c d`：因為 `x = ordered_pair a b` 且 `x = ordered_pair c d`
7. `have h_eq_components : a = c ∧ b = d := ordered_pair_inj a b c d h_eq_pair`：使用有序對的單射性質
8. `have ha_in_C : a ∈ C`：因為 `a = c` 且 `c ∈ C`
9. `have hb_in_D : b ∈ D`：因為 `b = d` 且 `d ∈ D`
10. `have ha_in_inter_A_C : a ∈ A ∩ C`：因為 `a ∈ A` 且 `a ∈ C`
11. `have hb_in_inter_B_D : b ∈ B ∩ D`：因為 `b ∈ B` 且 `b ∈ D`
12. `rw [mem_product]` 和 `exact ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, rfl ⟩`：證明 `x ∈ (A ∩ C) × (B ∩ D)`

**關鍵理解：**
- 因為 `x` 同時屬於兩個笛卡爾積，所以 `x` 可以表示為兩個不同的有序對
- 但有序對的唯一性（單射性質）確保這兩個有序對必須相等
- 因此它們的分量也必須相等

#### 第二個方向：`x ∈ (A ∩ C) × (B ∩ D) → x ∈ (A × B) ∩ (C × D)`

**目標：** 證明如果 `x` 屬於 `(A ∩ C) × (B ∩ D)`，則 `x` 同時屬於 `A × B` 和 `C × D`

**策略：**
1. 從 `x ∈ (A ∩ C) × (B ∩ D)` 得到 `x = (a, b)`，其中 `a ∈ A ∩ C, b ∈ B ∩ D`
2. 分解交集得到 `a ∈ A, a ∈ C, b ∈ B, b ∈ D`
3. 因此 `x ∈ A × B`（因為 `a ∈ A, b ∈ B`）且 `x ∈ C × D`（因為 `a ∈ C, b ∈ D`）
4. 所以 `x ∈ (A × B) ∩ (C × D)`

**步驟：**
1. `rw [mem_product] at hx_product`：展開 `x ∈ (A ∩ C) × (B ∩ D)` 為 `∃ a ∈ A ∩ C, ∃ b ∈ B ∩ D, x = ordered_pair a b`
2. `rcases hx_product with ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, hx_eq ⟩`：分解存在量詞
3. `rw [ZFSet.mem_inter] at ha_in_inter_A_C`：將 `a ∈ A ∩ C` 拆成 `a ∈ A ∧ a ∈ C`
4. `rcases ha_in_inter_A_C with ⟨ ha_in_A, ha_in_C ⟩`：分解合取
5. 類似地，從 `b ∈ B ∩ D` 得到 `b ∈ B` 且 `b ∈ D`
6. `have hx_in_product_A_B : x ∈ product A B`：因為 `a ∈ A, b ∈ B`
7. `have hx_in_product_C_D : x ∈ product C D`：因為 `a ∈ C, b ∈ D`
8. `exact ZFSet.mem_inter.mpr ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩`：構造交集

**關鍵理解：**
- 如果 `a ∈ A ∩ C`，則 `a` 同時屬於 `A` 和 `C`
- 如果 `b ∈ B ∩ D`，則 `b` 同時屬於 `B` 和 `D`
- 因此 `(a, b)` 同時屬於 `A × B` 和 `C × D`

**為什麼這個定理很重要？**

1. **展示笛卡爾積與交集的關係**：
   - 兩個笛卡爾積的交集等於對應集合的交集的笛卡爾積
   - 這與聯集的分配律形成對比

2. **有序對單射性質的應用**：
   - 這個證明展示了如何使用有序對的單射性質
   - 從有序對的相等推導出分量的相等

3. **交集與笛卡爾積的交互**：
   - 展示了如何處理交集的成員關係
   - 展示了如何構造交集的成員關係

**關鍵技巧總結：**

1. **使用有序對的單射性質**：
   - `ordered_pair_inj`：從 `ordered_pair a b = ordered_pair c d` 得到 `a = c ∧ b = d`

2. **處理變數名衝突**：
   - 使用不同的變數名（如 `hx_eq` 和 `hx_eq2`）避免衝突

3. **分解交集**：
   - `rw [ZFSet.mem_inter]`：將 `x ∈ A ∩ B` 拆成 `x ∈ A ∧ x ∈ B`
   - `rcases`：分解合取

4. **構造交集**：
   - `ZFSet.mem_inter.mpr`：從 `x ∈ A ∧ x ∈ B` 構造 `x ∈ A ∩ B`

5. **重寫等式**：
   - `rw [ha_eq_c]`：將 `a` 重寫為 `c`，用於證明 `a ∈ C`

**記憶要點：**
- 笛卡爾積與交集的關係：`(A × B) ∩ (C × D) = (A ∩ C) × (B ∩ D)`
- 關鍵觀察：如果 `x` 同時屬於兩個笛卡爾積，則 `x` 可以表示為兩個有序對，但有序對的唯一性確保它們相等
- 使用 `ordered_pair_inj` 從有序對的相等推導出分量的相等
- 注意變數名的衝突，使用不同的名稱（如 `hx_eq` 和 `hx_eq2`）
- 分解交集使用 `rw [ZFSet.mem_inter]` 和 `rcases`
- 構造交集使用 `ZFSet.mem_inter.mpr`

---

### 範例 20：笛卡爾積與聯集的子集合關係

**定理：** `(A × B) ∪ (C × D) ⊆ (A ∪ C) × (B ∪ D)`，即 `product A B ∪ product C D ⊆ product (A ∪ C) (B ∪ D)`

這個定理說明：兩個笛卡爾積的聯集是對應集合的聯集的笛卡爾積的子集合。注意這是一個單向的子集合關係，不是等價關係。

**完整證明：**

```lean
theorem theorem_2_2_3_e (A B C D : ZFSet) : product A B ∪ product C D ⊆ product (A ∪ C) (B ∪ D) := by
  rw [ZFSet.subset_def] -- 將 A ⊆ B 轉換為 ∀ x, x ∈ A → x ∈ B
  intro x hx_union -- x : any arbitrary element, hx_union : x ∈ (A ⨯ B) ∪ (C ⨯ D)
  -- 目標：證明 x ∈ (A ∪ C) ⨯ (B ∪ D)
  rw [ZFSet.mem_union] at hx_union -- 將 x ∈ (A ⨯ B) ∪ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∨ x ∈ (C ⨯ D)
  cases hx_union with
    | inl hx_in_product_A_B => -- hx_in_product_A_B : x ∈ (A ⨯ B)
      rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
      rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
      -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B
      -- 因為 a ∈ A 所以 a ∈ A ∪ C
      have ha_in_A_C : a ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inl ha) -- a ∈ A，所以 a ∈ A ∪ C
      -- 因為 b ∈ B 所以 b ∈ B ∪ D
      have hb_in_B_D : b ∈ B ∪ D := ZFSet.mem_union.mpr (Or.inl hb_B) -- b ∈ B，所以 b ∈ B ∪ D
      rw [mem_product] -- 使用笛卡爾積的成員關係，目標變成 ∃ a' ∈ A ∪ C, ∃ b' ∈ B ∪ D, x = ordered_pair a' b'
      rw [hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair a' b'
      exact ⟨ a, ha_in_A_C, b, hb_in_B_D, rfl ⟩ -- x = ordered_pair a b, a ∈ A ∪ C, b ∈ B ∪ D
    | inr hx_in_product_C_D => -- hx_in_product_C_D : x ∈ (C ⨯ D)
      rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
      rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq : x = ordered_pair c d
      -- 現在我們有：x = ordered_pair c d, c ∈ C, d ∈ D
      -- 因為 c ∈ C 所以 c ∈ A ∪ C
      have hc_in_A_C : c ∈ A ∪ C := ZFSet.mem_union.mpr (Or.inr hc) -- c ∈ C，所以 c ∈ A ∪ C
      -- 因為 d ∈ D 所以 d ∈ B ∪ D
      have hd_in_B_D : d ∈ B ∪ D := ZFSet.mem_union.mpr (Or.inr hd_D) -- d ∈ D，所以 d ∈ B ∪ D
      rw [mem_product] -- 使用笛卡爾積的成員關係，目標變成 ∃ a' ∈ A ∪ C, ∃ b' ∈ B ∪ D, x = ordered_pair a' b'
      rw [hx_eq] -- 將 x = ordered_pair c d 重寫為 x = ordered_pair a' b'
      exact ⟨ c, hc_in_A_C, d, hd_in_B_D, rfl ⟩ -- x = ordered_pair c d, c ∈ A ∪ C, d ∈ B ∪ D
```

**詳細步驟解析：**

#### 第一步：轉換子集合關係

**目標：** 將 `(A × B) ∪ (C × D) ⊆ (A ∪ C) × (B ∪ D)` 轉換為單向蘊含

**策略：** 使用 `ZFSet.subset_def` 將子集合關係轉換為全稱量化的單向蘊含。

**步驟：**
1. `rw [ZFSet.subset_def]`：將 `A ⊆ B` 轉換為 `∀ x, x ∈ A → x ∈ B`
2. `intro x hx_union`：引入任意元素 `x` 和假設 `hx_union : x ∈ (A × B) ∪ (C × D)`
3. 目標變成：證明 `x ∈ (A ∪ C) × (B ∪ D)`

**關鍵理解：**
- 子集合關係 `A ⊆ B` 只需要證明單向：如果 `x ∈ A`，則 `x ∈ B`
- 不需要證明反向（如果 `x ∈ B`，則 `x ∈ A`）
- 這與集合等式 `A = B` 不同，後者需要雙向證明

#### 第二步：分解聯集成員關係

**目標：** 從 `x ∈ (A × B) ∪ (C × D)` 得到 `x ∈ A × B` 或 `x ∈ C × D`

**步驟：**
1. `rw [ZFSet.mem_union] at hx_union`：將 `x ∈ (A × B) ∪ (C × D)` 轉換為 `x ∈ A × B ∨ x ∈ C × D`
2. `cases hx_union`：分情況討論

**情況 1：`x ∈ A × B`**
- `inl hx_in_product_A_B`：`hx_in_product_A_B : x ∈ A × B`
- `rw [mem_product] at hx_in_product_A_B`：展開為 `∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b`
- `rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩`：分解存在量詞，得到 `a ∈ A, b ∈ B, x = ordered_pair a b`

**情況 2：`x ∈ C × D`**
- `inr hx_in_product_C_D`：`hx_in_product_C_D : x ∈ C × D`
- 類似地處理

#### 第三步：證明聯集成員關係

**目標：** 證明 `a ∈ A ∪ C` 和 `b ∈ B ∪ D`（情況 1），或 `c ∈ A ∪ C` 和 `d ∈ B ∪ D`（情況 2）

**情況 1：`x ∈ A × B`**
- `have ha_in_A_C : a ∈ A ∪ C`：因為 `a ∈ A`，所以 `a ∈ A ∪ C`
  - `ZFSet.mem_union.mpr (Or.inl ha)`：使用 `Or.inl` 選擇左分支
- `have hb_in_B_D : b ∈ B ∪ D`：因為 `b ∈ B`，所以 `b ∈ B ∪ D`
  - `ZFSet.mem_union.mpr (Or.inl hb_B)`：使用 `Or.inl` 選擇左分支

**情況 2：`x ∈ C × D`**
- `have hc_in_A_C : c ∈ A ∪ C`：因為 `c ∈ C`，所以 `c ∈ A ∪ C`
  - `ZFSet.mem_union.mpr (Or.inr hc)`：使用 `Or.inr` 選擇右分支
- `have hd_in_B_D : d ∈ B ∪ D`：因為 `d ∈ D`，所以 `d ∈ B ∪ D`
  - `ZFSet.mem_union.mpr (Or.inr hd_D)`：使用 `Or.inr` 選擇右分支

**關鍵理解：**
- `Or.inl` 用於選擇左分支：如果 `a ∈ A`，則 `a ∈ A ∪ C`
- `Or.inr` 用於選擇右分支：如果 `c ∈ C`，則 `c ∈ A ∪ C`

#### 第四步：證明目標

**目標：** 證明 `x ∈ (A ∪ C) × (B ∪ D)`

**步驟：**
1. `rw [mem_product]`：展開目標為 `∃ a' ∈ A ∪ C, ∃ b' ∈ B ∪ D, x = ordered_pair a' b'`
2. `rw [hx_eq]`：將 `x` 重寫為 `ordered_pair a b`（情況 1）或 `ordered_pair c d`（情況 2）
3. `exact ⟨ a, ha_in_A_C, b, hb_in_B_D, rfl ⟩`：構造存在量詞（情況 1）
4. `exact ⟨ c, hc_in_A_C, d, hd_in_B_D, rfl ⟩`：構造存在量詞（情況 2）

**關鍵理解：**
- 使用 `rfl` 證明 `ordered_pair a b = ordered_pair a b`（自反性）
- 構造存在量詞需要提供存在的元素和它們滿足條件的證明

**為什麼這個定理很重要？**

1. **展示子集合關係與等價關係的區別**：
   - 這個定理展示了如何證明子集合關係（單向）
   - 與之前的等價關係（雙向）形成對比

2. **聯集與笛卡爾積的交互**：
   - 展示了聯集運算與笛卡爾積運算之間的關係
   - 兩個笛卡爾積的聯集是對應集合的聯集的笛卡爾積的子集合

3. **情況分析的應用**：
   - 展示了如何使用 `cases` 處理析取
   - 展示了如何使用 `Or.inl` 和 `Or.inr` 構造聯集成員關係

**關鍵技巧總結：**

1. **使用 `ZFSet.subset_def`**：
   - `rw [ZFSet.subset_def]`：將 `A ⊆ B` 轉換為 `∀ x, x ∈ A → x ∈ B`
   - 這與 `ZFSet.ext`（用於集合等式）不同

2. **處理子集合關係**：
   - 子集合關係只需要證明單向蘊含
   - 不需要使用 `constructor` 分成兩個方向

3. **使用 `Or.inl` 和 `Or.inr`**：
   - `Or.inl`：選擇左分支（`a ∈ A` 意味著 `a ∈ A ∪ C`）
   - `Or.inr`：選擇右分支（`c ∈ C` 意味著 `c ∈ A ∪ C`）

4. **情況分析**：
   - 使用 `cases` 處理析取（`x ∈ A × B ∨ x ∈ C × D`）
   - 每個情況都需要單獨處理

**記憶要點：**
- 笛卡爾積與聯集的子集合關係：`(A × B) ∪ (C × D) ⊆ (A ∪ C) × (B ∪ D)`
- 關鍵觀察：這是單向的子集合關係，不是等價關係
- 使用 `ZFSet.subset_def` 將子集合關係轉換為單向蘊含
- 子集合關係只需要證明：如果 `x ∈ A`，則 `x ∈ B`
- 使用 `Or.inl` 選擇左分支，`Or.inr` 選擇右分支
- 使用 `cases` 處理析取，每個情況都需要單獨處理
- 注意：這個關係是單向的，反向不一定成立

---

### 範例 21：笛卡爾積與交集的關係（重複）

**定理：** `(A × B) ∩ (C × D) = (A ∩ C) × (B ∩ D)`，即 `product A B ∩ product C D = product (A ∩ C) (B ∩ D)`

**注意：** 這個定理與範例 19 相同，這裡提供完整的證明代碼供參考。

**完整證明：**

```lean
theorem theorem_2_2_3_f (A B C D : ZFSet) : product A B ∩ product C D = product (A ∩ C) (B ∩ D) := by
  apply ZFSet.ext -- 根據外延性公設，將 (A ⨯ B) ∩ (C ⨯ D) = (A ∩ C) ⨯ (B ∩ D) 轉換為 ∀ x, x ∈ (A ⨯ B) ∩ (C ⨯ D) ↔ x ∈ (A ∩ C) ⨯ (B ∩ D)
  intro x -- x :any arbitrary element
  constructor -- 將 ↔ 分成兩個方向
  · intro hx_inter -- hx_inter : x ∈ (A ⨯ B) ∩ (C ⨯ D)
    -- x ∈ (A ⨯ B) ∩ (C ⨯ D) → x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [ZFSet.mem_inter] at hx_inter -- 將 x ∈ (A ⨯ B) ∩ (C ⨯ D) 拆成 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rcases hx_inter with ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- 分解交集成員關係，得到 x ∈ (A ⨯ B) ∧ x ∈ (C ⨯ D)
    rw [mem_product] at hx_in_product_A_B -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
    rcases hx_in_product_A_B with ⟨ a, ha, b, hb_B, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A, b ∈ B, hx_eq : x = ordered_pair a b
    rw [mem_product] at hx_in_product_C_D -- 使用笛卡爾積的成員關係，得到 ∃ c ∈ C, ∃ d ∈ D, x = ordered_pair c d
    rcases hx_in_product_C_D with ⟨ c, hc, d, hd_D, hx_eq2 ⟩ -- 分解存在量詞，得到 c ∈ C, d ∈ D, hx_eq2 : x = ordered_pair c d
    -- 現在我們有：x = ordered_pair a b, a ∈ A, b ∈ B, x = ordered_pair c d, c ∈ C, d ∈ D
    -- 因為 x = ordered_pair a b ∧ x = ordered_pair c d，所以 ordered_pair a b = ordered_pair c d
    have h_eq_pair : ordered_pair a b = ordered_pair c d := by
      rw [← hx_eq] -- 將 ordered_pair a b 重寫為 x
      exact hx_eq2 -- x = ordered_pair c d
    -- 使用有序對單射性質，得到 a = c ∧ b = d
    have h_eq_components : a = c ∧ b = d := ordered_pair_inj a b c d h_eq_pair
    rcases h_eq_components with ⟨ ha_eq_c, hb_eq_d ⟩ -- 分解等式，得到 a = c ∧ b = d
    have ha_in_C : a ∈ C := by
      rw [ha_eq_c] -- 將 a 重寫為 c
      exact hc -- a = c，所以 a ∈ C
    have hb_in_D : b ∈ D := by
      rw [hb_eq_d] -- 將 b 重寫為 d
      exact hd_D -- d ∈ D
    have ha_in_inter_A_C : a ∈ A ∩ C := ZFSet.mem_inter.mpr ⟨ ha, ha_in_C ⟩ -- a ∈ A ∧ a ∈ C
    have hb_in_inter_B_D : b ∈ B ∩ D := ZFSet.mem_inter.mpr ⟨ hb_B, hb_in_D ⟩ -- b ∈ B ∧ b ∈ D
    rw [mem_product] -- 展開目標為 ∃ a' ∈ A ∩ C, ∃ b' ∈ B ∩ D, x = ordered_pair a' b'
    rw [hx_eq] -- 將 x = ordered_pair a b 重寫為 x = ordered_pair a' b'
    exact ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, rfl ⟩ -- x = ordered_pair a b, a ∈ A ∩ C, b ∈ B ∩ D
  · intro hx_product -- hx_product : x ∈ (A ∩ C) ⨯ (B ∩ D)
    rw [mem_product] at hx_product -- 使用笛卡爾積的成員關係，得到 ∃ a ∈ A ∩ C, ∃ b ∈ B ∩ D, x = ordered_pair a b
    rcases hx_product with ⟨ a, ha_in_inter_A_C, b, hb_in_inter_B_D, hx_eq ⟩ -- 分解存在量詞，得到 a ∈ A ∩ C, b ∈ B ∩ D, hx_eq : x = ordered_pair a b
    rw [ZFSet.mem_inter] at ha_in_inter_A_C -- 將 a ∈ A ∩ C 拆成 a ∈ A ∧ a ∈ C
    rcases ha_in_inter_A_C with ⟨ ha_in_A, ha_in_C ⟩ -- 分解交集成員關係，得到 a ∈ A ∧ a ∈ C
    rw [ZFSet.mem_inter] at hb_in_inter_B_D -- 將 b ∈ B ∩ D 拆成 b ∈ B ∧ b ∈ D
    rcases hb_in_inter_B_D with ⟨ hb_in_B, hb_in_D ⟩ -- 分解交集成員關係，得到 b ∈ B ∧ b ∈ D
    have hx_in_product_A_B : x ∈ product A B := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_A, b, hb_in_B, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ A, b ∈ B
    have hx_in_product_C_D : x ∈ product C D := by
      rw [mem_product, hx_eq] -- 使用笛卡爾積的成員關係，並將 x 重寫為 ordered_pair a b
      exact ⟨ a, ha_in_C, b, hb_in_D, rfl ⟩ -- ordered_pair a b = ordered_pair a b, a ∈ C, b ∈ D
    exact ZFSet.mem_inter.mpr ⟨ hx_in_product_A_B, hx_in_product_C_D ⟩ -- x ∈ (A ⨯ B) ∩ (C ⨯ D)
```

**詳細說明：**

這個證明的結構與範例 19 完全相同，主要步驟包括：

1. **第一個方向**：使用有序對的單射性質，從 `x` 同時屬於兩個笛卡爾積推導出 `x` 屬於對應交集的笛卡爾積
2. **第二個方向**：分解交集的成員關係，分別證明 `x` 屬於兩個笛卡爾積

詳細的步驟解析和關鍵理解請參見範例 19。

---

## 集合族的聯集與交集

### 集合族的聯集（Union of a Family）

**定義：**

集合族 `𝒜` 的聯集（或稱為在 `𝒜` 上的聯集）定義為包含所有屬於 `𝒜` 中某個集合的元素的集合。

```lean
def union_of_family (𝒜 : ZFSet) : ZFSet := ZFSet.sUnion 𝒜
```

**數學符號：** `⋃_{A ∈ 𝒜} A = {x : ∃ A ∈ 𝒜, x ∈ A}`

**成員關係定理：**

```lean
theorem mem_union_of_family (𝒜 x : ZFSet) :
  x ∈ union_of_family 𝒜 ↔ ∃ A ∈ 𝒜, x ∈ A
```

這個定理說明：`x` 屬於集合族 `𝒜` 的聯集，當且僅當存在一個集合 `A` 屬於 `𝒜`，使得 `x` 屬於 `A`。

---

### 集合族的交集（Intersection of a Family）

**定義：**

集合族 `𝒜` 的交集（或稱為在 `𝒜` 上的交集）定義為包含所有同時屬於 `𝒜` 中每個集合的元素的集合。

**注意：** 集合族的交集通常需要集合族非空。如果 `𝒜` 是空集合族，則其交集在 ZFC 中未定義（或者需要全域集合，這在 ZFC 中不存在）。
我們的定義使用分離公理，實際上定義的是 `⋂_{A ∈ 𝒜} A = {x ∈ ⋃_{A ∈ 𝒜} A : ∀ A ∈ 𝒜, x ∈ A}`。

```lean
def intersection_of_family (𝒜 : ZFSet) : ZFSet := 
  ZFSet.sep (fun x => ∀ A ∈ 𝒜, x ∈ A) (union_of_family 𝒜)
```

**數學符號：** `⋂_{A ∈ 𝒜} A = {x : ∀ A ∈ 𝒜, x ∈ A}`

**成員關係定理：**

```lean
theorem mem_intersection_of_family (𝒜 x : ZFSet) :
  x ∈ intersection_of_family 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A)
```

這個定理說明：`x` 屬於集合族 `𝒜` 的交集，當且僅當：
1. `x` 屬於 `𝒜` 的聯集（即存在某個 `B ∈ 𝒜` 使得 `x ∈ B`，這隱含了 `𝒜` 非空且 `x` 至少在一個集合中）
2. 對於所有 `A ∈ 𝒜`，`x` 都屬於 `A`

**證明技巧：**

證明這個定理時，我們使用了 `simp` 策略，因為展開定義後，左右兩邊的邏輯表達式是等價的（alpha-equivalent）。

```lean
theorem mem_intersection_of_family (𝒜 x : ZFSet) :
  x ∈ intersection_of_family 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A) := by
  -- 直接使用 simp 展開所有定義並簡化
  simp [intersection_of_family, ZFSet.mem_sep, mem_union_of_family]
```

### 範例 21：集合族交集的子集合性質

**題目：** 對於集合族 `𝒜` 中的任意集合 `B`，`𝒜` 的交集是 `B` 的子集合。即 `∀ B ∈ 𝒜, ⋂_{A ∈ 𝒜} A ⊆ B`。

**證明思路：**
1. 這是「交集包含於每一個集合」的推廣。
2. 如果 `x` 在交集中，則 `x` 必須在 `𝒜` 的**每一個**集合中。
3. 因為 `B` 是 `𝒜` 的成員，所以 `x` 必須在 `B` 中。

**代碼實現：**

```lean
-- Theorem 2.3.1 : Let 𝒜 be a family of sets.
-- (a) For every set B in the family 𝒜, ⋂_{A ∈ 𝒜} A ⊆ B.
theorem theorem_2_3_1 (𝒜 : ZFSet) : ∀ B ∈ 𝒜, intersection_of_family 𝒜 ⊆ B := by
  intro B hB x hx -- B : 任意集合, hB : B ∈ 𝒜, x : 任意元素, hx : x ∈ ⋂ 𝒜
  -- 目標：證明 x ∈ B
  rw [mem_intersection_of_family] at hx -- 展開交集定義：x ∈ ⋂ 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A)
  have h_forall : ∀ A ∈ 𝒜, x ∈ A := hx.right -- 取出右邊的性質：對於所有 A ∈ 𝒜，x ∈ A
  exact h_forall B hB -- 因為 B ∈ 𝒜，所以 x ∈ B
```

**關鍵技巧：**
- **`rw [mem_intersection_of_family] at hx`**：將抽象的交集定義轉換為具體的邏輯條件。
- **`hx.right`**：從合取中提取全稱量詞部分。
- **`h_forall B hB`**：將全稱量詞應用於特定的集合 `B`（因為我們已知 `B ∈ 𝒜`）。

### 範例 22：集合族聯集的超集合性質

**題目：** 對於集合族 `𝒜` 中的任意集合 `B`，`B` 是 `𝒜` 的聯集的子集合。即 `∀ B ∈ 𝒜, B ⊆ ⋃_{A ∈ 𝒜} A`。

**證明思路：**
1. 這是「聯集包含每一個集合」的推廣。
2. 假設 `x ∈ B`。
3. 要證明 `x ∈ ⋃𝒜`，只要證明存在一個 `A ∈ 𝒜` 使得 `x ∈ A`。
4. 因為 `B` 本身就在 `𝒜` 中，且 `x ∈ B`，所以 `B` 就是我們要找的那個集合。

**代碼實現：**

```lean
-- (b) For every set B in the family 𝒜, B ⊆ ⋃_{A ∈ 𝒜} A
theorem theorem_2_3_1_b (𝒜 : ZFSet) : ∀ B ∈ 𝒜, B ⊆ union_of_family 𝒜 := by
  intro B hB x hx -- B : 任意集合, hB : B ∈ 𝒜, x : 任意元素, hx : x ∈ B
  -- 目標：證明 x ∈ ⋃ 𝒜
  rw [mem_union_of_family] -- 展開目標中的聯集定義：目標變成 ∃ A ∈ 𝒜, x ∈ A
  -- 我們需要提供一個 A，證明 A ∈ 𝒜 且 x ∈ A
  -- 因為已知 B ∈ 𝒜 且 x ∈ B，所以 B 就是我們要找的集合
  exact ⟨ B, hB, hx ⟩ -- 構造存在量詞證明：使用 B 作為存在的集合
```

**關鍵技巧：**
- **構造存在量詞**：當目標是 `∃ A ∈ 𝒜, ...` 時，如果我們手上有一個具體的對象（這裡是 `B`）滿足條件，我們可以用 `exact ⟨B, ...⟩` 來完成證明。

### 範例 23：非空集合族的交集包含於聯集

**題目：** 如果集合族 `𝒜` 非空，則 `𝒜` 的交集包含於 `𝒜` 的聯集。即 `𝒜 ≠ ∅ → ⋂_{A ∈ 𝒜} A ⊆ ⋃_{A ∈ 𝒜} A`。

**證明思路：**
1. 假設 `x` 在交集中。
2. 根據交集的定義，`x` 必須在 `𝒜` 的**每一個**集合中，且至少存在一個 `B ∈ 𝒜` 使得 `x ∈ B`（這來自交集定義中 `x ∈ ⋃𝒜` 的部分）。
3. 既然 `x` 屬於某個 `B ∈ 𝒜`，根據聯集的定義，`x` 自然在聯集中。

**代碼實現：**

```lean
-- (c) If the family 𝒜 is nonempty, then ⋂_{A ∈ 𝒜} A ⊆ ⋃_{A ∈ 𝒜} A
theorem theorem_2_3_1_c (𝒜 : ZFSet) : 𝒜 ≠ ∅ → intersection_of_family 𝒜 ⊆ union_of_family 𝒜 := by
  intro h_nonempty x hx -- 𝒜 : 集合族, h_nonempty : 𝒜 ≠ ∅, x : 任意元素, hx : x ∈ ⋂ 𝒜
  -- 目標：證明 x ∈ ⋃ 𝒜
  rw [mem_intersection_of_family] at hx -- 展開交集定義：x ∈ ⋂ 𝒜 ↔ (∃ B ∈ 𝒜, x ∈ B) ∧ (∀ A ∈ 𝒜, x ∈ A)
  have h_exists : ∃ B ∈ 𝒜, x ∈ B := hx.left -- 存在一個 B ∈ 𝒜 使得 x ∈ B
  rcases h_exists with ⟨ B, hB, hx_B ⟩ -- B : 任意集合, hB : B ∈ 𝒜, hx_B : x ∈ B
  rw [mem_union_of_family] -- 展開目標中的聯集定義：目標變成 ∃ A ∈ 𝒜, x ∈ A
  exact ⟨ B, hB, hx_B ⟩ -- 構造存在量詞證明：使用 B 作為存在的集合
```

### 範例 24：集合族的德摩根定律（聯集形式）

**題目：** 聯集的補集等於補集的交集。對於集合族，這表現為：`(⋃ 𝒜)ᶜ ↔ ∀ A ∈ 𝒜, Aᶜ`。
更精確地說：`x ∈ (⋃ 𝒜)ᶜ ↔ x ∈ U ∧ ∀ A ∈ 𝒜, x ∉ A`。

**證明思路：**
- **方向 1 (→)**：如果 `x` 不在聯集中，則 `x` 不屬於任何一個 `A ∈ 𝒜`。否則，如果 `x ∈ A`，則 `x ∈ ⋃ 𝒜`，矛盾。
- **方向 2 (←)**：如果 `x` 不屬於任何 `A ∈ 𝒜`，則 `x` 不在聯集中。否則，如果 `x ∈ ⋃ 𝒜`，則存在 `A` 使得 `x ∈ A`，與假設矛盾。

**代碼實現：**

```lean
-- (e) De Morgan's Law for families: (⋃ 𝒜)ᶜ ↔ ∀ A ∈ 𝒜, Aᶜ
theorem theorem_2_3_1_d (U 𝒜 : ZFSet) :
  ∀ x, x ∈ compl U (union_of_family 𝒜) ↔ (x ∈ U ∧ ∀ A ∈ 𝒜, x ∉ A) := by
  intro x -- x : 任意元素
  constructor -- 將 ↔ 分成兩個方向
  · intro hx -- hx : x ∈ (⋃ 𝒜)ᶜ
    rw [mem_compl] at hx -- 展開補集定義：x ∈ U ∧ x ∉ ⋃ 𝒜
    rcases hx with ⟨hx_U, hx_not_union⟩ -- hx_U : x ∈ U, hx_not_union : x ∉ ⋃ 𝒜
    constructor
    · exact hx_U -- x ∈ U
    · intro A hA hx_A -- A : 任意集合, hA : A ∈ 𝒜, hx_A : x ∈ A。目標：推出矛盾
      -- 證明 x ∈ ⋃ 𝒜
      have hx_in_union : x ∈ union_of_family 𝒜 := by
        rw [mem_union_of_family] -- 展開聯集定義：∃ B ∈ 𝒜, x ∈ B
        exact ⟨ A, hA, hx_A ⟩ -- 因為 A ∈ 𝒜 且 x ∈ A
      exact hx_not_union hx_in_union -- 矛盾：x ∉ ⋃ 𝒜 但 x ∈ ⋃ 𝒜
  · intro ⟨hx_U, h_forall⟩ -- hx_U : x ∈ U, h_forall : ∀ A ∈ 𝒜, x ∉ A
    rw [mem_compl] -- 展開目標補集定義：x ∈ U ∧ x ∉ ⋃ 𝒜
    constructor
    · exact hx_U -- x ∈ U
    · intro hx_in_union -- 假設 x ∈ ⋃ 𝒜，推出矛盾
      rw [mem_union_of_family] at hx_in_union -- 展開聯集定義：∃ A ∈ 𝒜, x ∈ A
      rcases hx_in_union with ⟨ A, hA, hx_A ⟩ -- 取出存在的集合 A
      -- h_forall A hA 說 x ∉ A，但 hx_A 說 x ∈ A，矛盾
      exact h_forall A hA hx_A
```

### 範例 25：集合族的德摩根定律（交集形式）

**題目：** 交集的補集等於補集的聯集（需要 `𝒜 ≠ ∅`）。即：`(⋂ 𝒜)ᶜ ↔ ∃ A ∈ 𝒜, Aᶜ`。

**證明思路：**
- **方向 1 (→)**：使用反證法。假設對於所有 `A ∈ 𝒜`，`x ∈ A`。則 `x ∈ ⋂ 𝒜`，這與 `x ∈ (⋂ 𝒜)ᶜ` 矛盾。
- **方向 2 (←)**：如果存在 `A ∈ 𝒜` 使得 `x ∉ A`，則 `x` 不可能在交集中（因為交集要求元素在所有集合中）。

**代碼實現：**

```lean
-- (f) De Morgan's Law for families (Intersection): (⋂ 𝒜)ᶜ ↔ ∃ A ∈ 𝒜, Aᶜ
-- Note: Requires 𝒜 ≠ ∅ to ensure the existence of sets.
theorem theorem_2_3_1_e (U 𝒜 : ZFSet) (h_nonempty : 𝒜 ≠ ∅) :
  ∀ x, x ∈ compl U (intersection_of_family 𝒜) ↔ (x ∈ U ∧ ∃ A ∈ 𝒜, x ∉ A) := by
  intro x
  constructor
  · intro hx -- hx : x ∈ (⋂ 𝒜)ᶜ
    rw [mem_compl] at hx
    rcases hx with ⟨hx_U, hx_not_inter⟩ -- x ∈ U, x ∉ ⋂ 𝒜
    constructor
    · exact hx_U
    · -- 我們需要證明 ∃ A ∈ 𝒜, x ∉ A
      -- 使用反證法：假設 ∀ A ∈ 𝒜, x ∈ A
      by_contra h_all_in
      rw [not_exists] at h_all_in -- h_all_in : ∀ x, ¬(x ∈ 𝒜 ∧ x ∉ A)
      -- 這意味著對於所有 A ∈ 𝒜，x ∈ A
      have h_forall : ∀ A ∈ 𝒜, x ∈ A := by
        intro A hA
        by_contra h_not_in
        exact h_all_in A ⟨hA, h_not_in⟩
      -- 因為 𝒜 ≠ ∅，我們可以找到一個 B ∈ 𝒜
      have h_exists_B : ∃ B, B ∈ 𝒜 := by
        by_contra h_empty
        rw [not_exists] at h_empty
        -- 如果不存在 B ∈ 𝒜，則 𝒜 是空集合
        have h_A_empty : 𝒜 = ∅ := by
          apply ZFSet.ext
          intro z
          constructor
          · intro hz
            exact False.elim (h_empty z hz)
          · intro hz
            exact False.elim (ZFSet.notMem_empty z hz)
        exact h_nonempty h_A_empty
      rcases h_exists_B with ⟨B, hB⟩
      -- 因為 x ∈ B (由 h_forall)，所以 x ∈ ⋃ 𝒜
      have hx_in_union : x ∈ union_of_family 𝒜 := by
        rw [mem_union_of_family]
        exact ⟨B, hB, h_forall B hB⟩
      -- 所以 x ∈ ⋂ 𝒜
      have hx_in_inter : x ∈ intersection_of_family 𝒜 := by
        rw [mem_intersection_of_family]
        exact ⟨⟨B, hB, h_forall B hB⟩, h_forall⟩
      -- 這與 x ∉ ⋂ 𝒜 (hx_not_inter) 矛盾
      exact hx_not_inter hx_in_inter
  · intro ⟨hx_U, h_exists⟩ -- x ∈ U, ∃ A ∈ 𝒜, x ∉ A
    rw [mem_compl]
    constructor
    · exact hx_U
    · intro hx_in_inter -- 假設 x ∈ ⋂ 𝒜
      rw [mem_intersection_of_family] at hx_in_inter
      have h_forall := hx_in_inter.right -- ∀ A ∈ 𝒜, x ∈ A
      rcases h_exists with ⟨A, hA, hx_not_in_A⟩
      -- h_forall A hA 說 x ∈ A，但 hx_not_in_A 說 x ∉ A，矛盾
      exact hx_not_in_A (h_forall A hA)
```

### 範例 26：子集合與集合族交集的關係

**題目：** 設 `𝒜` 為非空集合族，`B` 為集合。如果 `B` 是 `𝒜` 中每個集合的子集合，則 `B` 是 `𝒜` 的交集的子集合。即 `(∀ A ∈ 𝒜, B ⊆ A) → B ⊆ ⋂_{A ∈ 𝒜} A`。

**證明思路：**
1. 假設 `B ⊆ A` 對所有 `A ∈ 𝒜` 成立。
2. 取任意 `x ∈ B`，要證明 `x ∈ ⋂_{A ∈ 𝒜} A`。
3. 根據交集定義，需要證明兩點：
   - **存在性**：存在某個 `A₀ ∈ 𝒜` 使得 `x ∈ A₀`（這需要利用 `𝒜 ≠ ∅`）
   - **全稱性**：對所有 `A ∈ 𝒜`，`x ∈ A`
4. 因為 `𝒜` 非空，我們可以取出一個 `A₀ ∈ 𝒜`，由於 `B ⊆ A₀` 且 `x ∈ B`，所以 `x ∈ A₀`。
5. 對於任意 `A ∈ 𝒜`，由於 `B ⊆ A` 且 `x ∈ B`，所以 `x ∈ A`。

**代碼實現：**

```lean
-- Theorem 2.3.2 : Let 𝓐 be a nonempty family of sets and B be a set.
-- (a) If B ⊆ A for all A ∈ 𝓐, then B ⊆ ⋂_{A ∈ 𝓐} A.
theorem theorem_2_3_2_a (𝓐 B : ZFSet) (h_nonempty : 𝓐 ≠ ∅) : 
  (∀ A ∈ 𝓐, B ⊆ A) → B ⊆ intersection_of_family 𝓐 := by
  intro h_forall x hx -- h_forall : ∀ A ∈ 𝓐, B ⊆ A; x : 任意元素; hx : x ∈ B
  -- 目標：證明 x ∈ ⋂ 𝓐
  rw [mem_intersection_of_family] -- 展開交集定義：(∃ A ∈ 𝓐, x ∈ A) ∧ (∀ A ∈ 𝓐, x ∈ A)
  constructor -- 將 ∧ 分成兩個部分
  · -- 證明存在性：∃ A ∈ 𝓐, x ∈ A
    -- 先從 𝓐 ≠ ∅ 推導出存在一個集合 A₀ ∈ 𝓐
    have h_exists_A : ∃ A, A ∈ 𝓐 := by
      by_contra h_all_empty -- 反證法：假設 ¬(∃ A, A ∈ 𝓐)
      rw [not_exists] at h_all_empty -- 轉換為 ∀ A, A ∉ 𝓐
      apply h_nonempty -- 要證明 𝓐 ≠ ∅，即證明 𝓐 = ∅ → False
      apply ZFSet.ext -- 證明 𝓐 = ∅
      intro z
      constructor
      · intro hz; exact False.elim (h_all_empty z hz) -- z ∈ 𝓐 與假設矛盾
      · intro hz; exact False.elim (ZFSet.notMem_empty z hz) -- z ∈ ∅ 不可能
    rcases h_exists_A with ⟨ A₀, hA₀ ⟩ -- 取出存在的 A₀
    use A₀
    constructor
    · exact hA₀
    · apply h_forall A₀ hA₀ -- B ⊆ A₀
      exact hx -- x ∈ B
  · -- 證明全稱性：∀ A ∈ 𝓐, x ∈ A
    intro A hA
    apply h_forall A hA -- B ⊆ A
    exact hx -- x ∈ B
```

**關鍵技巧：**

1. **處理非空條件**：`𝓐 ≠ ∅` 是否定命題，不能直接用 `rcases` 解構。需要先用反證法證明「存在 `A ∈ 𝓐`」。

2. **反證法的標準模式**：
   ```lean
   have h_exists_A : ∃ A, A ∈ 𝓐 := by
     by_contra h_all_empty
     -- 從假設「不存在」推導出矛盾
   ```

3. **交集的雙重性質**：證明 `x ∈ ⋂ 𝓐` 需要同時證明：
   - 存在性：至少在一個集合中（確保 `𝓐` 非空且 `x` 有意義）
   - 全稱性：在每一個集合中

4. **子集合的應用**：`B ⊆ A` 在 Lean 中展開為 `∀ x, x ∈ B → x ∈ A`，所以 `h_forall A hA` 得到的是一個函數，需要應用於 `hx : x ∈ B` 來得到 `x ∈ A`。

### 範例 27：子集合與集合族聯集的關係（對偶定理）

**題目：** 設 `𝒜` 為集合族，`B` 為集合。如果 `𝒜` 中每個集合都是 `B` 的子集合，則 `𝒜` 的聯集也是 `B` 的子集合。即 `(∀ A ∈ 𝒜, A ⊆ B) → ⋃_{A ∈ 𝒜} A ⊆ B`。

**注意：** 這個定理不需要 `𝒜 ≠ ∅` 條件，因為如果 `𝒜 = ∅`，則 `⋃ 𝒜 = ∅`，自然是任何集合的子集合。

**證明思路：**
1. 假設對所有 `A ∈ 𝒜`，`A ⊆ B`。
2. 取任意 `x ∈ ⋃_{A ∈ 𝒜} A`，要證明 `x ∈ B`。
3. 根據聯集定義，存在某個 `A ∈ 𝒜` 使得 `x ∈ A`。
4. 由於 `A ⊆ B` 且 `x ∈ A`，所以 `x ∈ B`。

**代碼實現：**

```lean
-- (b) If A ⊆ B for all A ∈ 𝓐, then ⋃_{A ∈ 𝓐} A ⊆ B.
theorem theorem_2_3_2_b (𝓐 B : ZFSet) : 
  (∀ A ∈ 𝓐, A ⊆ B) → union_of_family 𝓐 ⊆ B := by
  intro h_forall x hx -- h_forall : ∀ A ∈ 𝓐, A ⊆ B; x : 任意元素; hx : x ∈ ⋃ 𝓐
  rw [mem_union_of_family] at hx -- 展開定義：∃ A ∈ 𝓐, x ∈ A
  rcases hx with ⟨A, hA, hxA⟩ -- 得到 A ∈ 𝓐 且 x ∈ A
  -- 利用前提 A ⊆ B (即 h_forall A hA) 推導
  apply h_forall A hA
  exact hxA
```

**關鍵技巧：**

1. **聯集的簡單性**：聯集只需要證明「存在一個集合包含 `x`」，所以用 `rcases` 解構後直接應用子集合關係即可。

2. **與交集的對比**：
   - **交集**（範例 26）：需要證明「所有集合都包含 `x`」，且需要非空條件來確保存在性。
   - **聯集**（範例 27）：只需證明「某個集合包含 `x`」，自然滿足存在性，無需非空條件。

3. **對偶性**：
   - 範例 26：`B ⊆ (所有 A) → B ⊆ ⋂ A`
   - 範例 27：`(所有 A) ⊆ B → ⋃ A ⊆ B`

---

## 9. 索引集合族（Indexed Family of Sets）

### 定義

在集合論中，我們經常需要處理「一族集合」，其中每個集合都有一個對應的「標籤」或「索引」。這就是**索引集合族**的概念。

**定義：** 設 `Δ` 為一個非空集合，對於每個 `α ∈ Δ`，都有一個對應的集合 `Aα`。則集合族 `{Aα : α ∈ Δ}` 稱為一個**索引集合族**（Indexed Family of Sets）。

- **索引集（Indexing Set）**：集合 `Δ` 稱為索引集
- **索引（Index）**：`Δ` 中的每個元素 `α` 稱為一個索引
- **索引族（Indexed Family）**：`{Aα : α ∈ Δ}` 表示所有由索引 `α` 標記的集合 `Aα` 組成的族

### 在 ZFC 中的形式化

在 ZFC 集合論中，索引集合族實際上是一個**函數**的概念：

1. **函數觀點**：索引族 `{Aα : α ∈ Δ}` 可以視為一個函數 `f : Δ → Sets`，其中 `f(α) = Aα`

2. **集合表示**：在 ZFC 中，函數本身也是集合（有序對的集合）。因此索引族可以表示為：
   ```
   f = {(α, Aα) : α ∈ Δ}
   ```
   這是一個由有序對組成的集合。

3. **與普通集合族的關係**：
   - **普通集合族**：`𝒜 = {A₁, A₂, A₃, ...}`，只是一個集合的集合，沒有明確的順序或標籤
   - **索引集合族**：`{Aα : α ∈ Δ}`，每個集合都有一個來自 `Δ` 的明確索引

### Lean 4 中的定義

```lean
-- 索引聯集的定義：⋃_{α ∈ Δ} Aα
-- 給定索引集 Δ 和索引函數 f : ZFSet → ZFSet
def indexed_union (Δ : ZFSet) (f : ZFSet → ZFSet) : ZFSet :=
  union_of_family (ZFSet.sep (fun A => ∃ α ∈ Δ, A = f α) 
    (ZFSet.powerset (ZFSet.sUnion (ZFSet.sep (fun A => ∃ α ∈ Δ, A = f α) 
      (ZFSet.powerset (ZFSet.sUnion Δ))))))
```

**說明：**
- 這個定義比較複雜，因為我們需要在 ZFC 中構造「所有 `f(α)` 的集合」
- 實際使用時，更常用的是通過**成員關係**來刻畫

### 索引聯集與索引交集

對於索引集合族 `{Aα : α ∈ Δ}`，我們可以定義：

#### 1. 索引聯集（Indexed Union）

**定義：** `⋃_{α ∈ Δ} Aα = {x : ∃ α ∈ Δ, x ∈ Aα}`

**成員關係：**
```
x ∈ ⋃_{α ∈ Δ} Aα  ↔  ∃ α ∈ Δ, x ∈ Aα
```

**與普通聯集的關係：**
```
⋃_{α ∈ Δ} Aα = ⋃ {Aα : α ∈ Δ}
```
即索引聯集等於將所有 `Aα` 收集成一個集合族，然後取該族的聯集。

#### 2. 索引交集（Indexed Intersection）

**定義：** `⋂_{α ∈ Δ} Aα = {x : ∀ α ∈ Δ, x ∈ Aα}`

**成員關係：**
```
x ∈ ⋂_{α ∈ Δ} Aα  ↔  (∃ β ∈ Δ, x ∈ Aβ) ∧ (∀ α ∈ Δ, x ∈ Aα)
```

**與普通交集的關係：**
```
⋂_{α ∈ Δ} Aα = ⋂ {Aα : α ∈ Δ}
```
即索引交集等於將所有 `Aα` 收集成一個集合族，然後取該族的交集。

### 常見例子

#### 例子 1：可數索引族

設 `Δ = ℕ`（自然數集），對每個 `n ∈ ℕ`，定義 `Aₙ = {x ∈ ℝ : 0 < x < 1/n}`（開區間）。

則：
- `{Aₙ : n ∈ ℕ}` 是一個可數索引族
- `⋃_{n ∈ ℕ} Aₙ = (0, 1)`（正實數中小於1的部分）
- `⋂_{n ∈ ℕ} Aₙ = ∅`（沒有正數同時小於所有 `1/n`）

#### 例子 2：連續索引族

設 `Δ = [0, 1]`（實數區間），對每個 `t ∈ [0, 1]`，定義 `Aₜ = {(x, y) ∈ ℝ² : x² + y² ≤ t²}`（半徑為 `t` 的圓盤）。

則：
- `{Aₜ : t ∈ [0, 1]}` 是一個連續索引族
- `⋃_{t ∈ [0, 1]} Aₜ = A₁`（單位圓盤）
- `⋂_{t ∈ [0, 1]} Aₜ = A₀ = {(0, 0)}`（原點）

#### 例子 3：任意索引族

設 `Δ` 為任意集合，對每個 `α ∈ Δ`，定義 `Aα = {α}`（單元素集合）。

則：
- `⋃_{α ∈ Δ} Aα = Δ`
- `⋂_{α ∈ Δ} Aα = ∅`（當 `Δ` 有至少兩個不同元素時）

### 與之前概念的關係

索引集合族與我們之前學習的集合族概念本質上是一致的：

1. **`union_of_family 𝒜`** ≈ `⋃_{α ∈ Δ} Aα`
   - 前者：對集合族 `𝒜` 中的所有集合取聯集
   - 後者：對索引族 `{Aα : α ∈ Δ}` 中的所有集合取聯集

2. **`intersection_of_family 𝒜`** ≈ `⋂_{α ∈ Δ} Aα`
   - 前者：對集合族 `𝒜` 中的所有集合取交集
   - 後者：對索引族 `{Aα : α ∈ Δ}` 中的所有集合取交集

**主要區別：**
- 索引族**明確標識**了索引集 `Δ` 和每個索引 `α`
- 索引族強調了集合與索引之間的**對應關係**（函數性質）
- 普通集合族只是「一堆集合」，沒有特定的標籤結構

### 形式化的注意事項

**重要說明：** 完整的索引族形式化需要先定義以下概念：

1. **關係（Relation）**：有序對的集合
2. **函數（Function）**：滿足單值性的關係
3. **定義域（Domain）**：函數的輸入集合
4. **值域（Range）**：函數的輸出集合
5. **像集（Image）**：函數在某個子集上的所有輸出值

這些概念通常在「關係與函數」章節中系統地定義。目前我們給出的是索引族的**概念框架**，為後續形式化做準備。

在實際使用中，我們可以：
- 使用 `union_of_family` 和 `intersection_of_family` 來處理索引族
- 理解索引族作為一種特殊的集合族（帶有明確索引結構）
- 等待後續章節完善函數和關係的完整理論

### 索引族的優勢

使用索引族而非普通集合族的優勢：

1. **清晰的標識**：每個集合都有明確的標籤，便於引用和討論
2. **可數性討論**：可以討論索引集的大小（有限、可數、不可數）
3. **序列化表示**：當 `Δ = ℕ` 時，索引族變成序列 `A₀, A₁, A₂, ...`
4. **參數化**：索引可以攜帶參數信息（如上面例子中的半徑 `t`）

---

## 10. 成對不交（Pairwise Disjoint）

### 定義

**定義：** 索引集合族 `{Aα : α ∈ Δ}` 稱為**成對不交的**（Pairwise Disjoint），如果對於所有 `α, β ∈ Δ`，滿足以下條件之一：
- `Aα = Aβ`（兩個集合相同）
- `Aα ∩ Aβ = ∅`（兩個集合不交）

換句話說，索引族中任意兩個**不同**的集合都是不交的。

### Lean 4 中的定義

```lean
-- 成對不交的定義
def pairwise_disjoint (Δ : ZFSet) (f : ZFSet → ZFSet) : Prop :=
  ∀ α ∈ Δ, ∀ β ∈ Δ, f α = f β ∨ f α ∩ f β = ∅
```

**說明：**
- `f : ZFSet → ZFSet` 表示索引函數，`f α` 是索引 `α` 對應的集合 `Aα`
- 條件 `f α = f β ∨ f α ∩ f β = ∅` 表示：要麼兩個集合相同，要麼它們不交
- 這個定義自動處理了 `α = β` 的情況（此時 `f α = f β` 成立）

### 等價的表述

成對不交可以有多種等價的表述方式：

1. **原始定義**：`∀ α, β ∈ Δ, Aα = Aβ ∨ Aα ∩ Aβ = ∅`

2. **排除相等的版本**：`∀ α, β ∈ Δ, α ≠ β → Aα ∩ Aβ = ∅`
   - 只對**不同**的索引要求集合不交

3. **使用不交的定義**：`∀ α, β ∈ Δ, α ≠ β → (∀ x, x ∈ Aα → x ∉ Aβ)`
   - 任何元素不能同時屬於兩個不同的集合

### 例子

#### 例子 1：成對不交的集合族

設 `Δ = {1, 2, 3}`，定義：
- `A₁ = {a, b}`
- `A₂ = {c, d}`
- `A₃ = {e, f}`

這個索引族是成對不交的，因為：
- `A₁ ∩ A₂ = ∅`
- `A₁ ∩ A₃ = ∅`
- `A₂ ∩ A₃ = ∅`

#### 例子 2：不是成對不交的集合族

設 `Δ = {1, 2, 3}`，定義：
- `A₁ = {a, b, c}`
- `A₂ = {b, c, d}`
- `A₃ = {e, f}`

這個索引族**不是**成對不交的，因為：
- `A₁ ∩ A₂ = {b, c} ≠ ∅`（雖然 `A₁ ∩ A₃ = ∅` 且 `A₂ ∩ A₃ = ∅`）

#### 例子 3：實數區間的分割

設 `Δ = ℤ`（整數集），對每個 `n ∈ ℤ` 定義：
```
Aₙ = [n, n+1) = {x ∈ ℝ : n ≤ x < n+1}
```

這個索引族是成對不交的，因為：
- 對於 `n ≠ m`，區間 `[n, n+1)` 和 `[m, m+1)` 沒有交集
- 這個族構成了整個實數軸 `ℝ` 的一個**分割**（partition）

### 成對不交的重要性

成對不交的概念在集合論中非常重要，主要原因：

1. **分割（Partition）**：
   - 成對不交的集合族可以將一個大集合分割成不重疊的小塊
   - 例如：將實數軸分割成區間，將平面分割成區域

2. **唯一性**：
   - 如果 `{Aα : α ∈ Δ}` 成對不交，則每個元素 `x ∈ ⋃_{α ∈ Δ} Aα` 恰好屬於**一個** `Aα`
   - 這保證了元素到索引的對應是唯一的

3. **計數原理**：
   - 如果集合族成對不交，則聯集的大小等於各個集合大小之和
   - `|⋃_{α ∈ Δ} Aα| = Σ_{α ∈ Δ} |Aα|`（離散情況）

4. **測度論**：
   - 在測度論中，可加性要求集合族成對不交
   - `μ(⋃_{i=1}^n Aᵢ) = Σ_{i=1}^n μ(Aᵢ)` 當集合族成對不交時成立

### 與普通不交的區別

- **兩個集合不交**：`A ∩ B = ∅`
  - 只涉及兩個集合的關係

- **集合族成對不交**：`∀ α ≠ β, Aα ∩ Aβ = ∅`
  - 涉及集合族中**所有**不同集合對的關係
  - 是一個更強的條件

**例子：**
- 集合族 `{A, B, C}` 即使 `A ∩ B = ∅` 且 `B ∩ C = ∅`，也不一定成對不交
- 還需要檢查 `A ∩ C = ∅`

### 應用場景

1. **等價類**：將集合劃分為互不相交的等價類
2. **分類問題**：將對象分成互不重疊的類別
3. **概率空間**：事件空間的分割
4. **圖論**：頂點的染色問題（相同顏色的頂點集合成對不交）

---

## 11. Omega 的最小性 (Minimality of Omega)

### 定義：歸納集（Inductive Set）

**定義：** 集合 `S` 稱為**歸納集**（Inductive Set），如果：
1. `0 ∈ S`（空集屬於 `S`）
2. 對所有 `n ∈ S`，有 `succ n ∈ S`（如果 `n` 在 `S` 中，則 `n` 的後繼也在 `S` 中）

其中 `succ n = insert n n = n ∪ {n}` 是 `n` 的後繼。

### Lean 4 中的定義

```lean
def is_inductive (S : ZFSet) : Prop :=
  ZFSet.empty ∈ S ∧ ∀ n ∈ S, (insert n n) ∈ S
```

**說明：**
- `ZFSet.empty ∈ S` 表示 `0 ∈ S`
- `∀ n ∈ S, (insert n n) ∈ S` 表示對所有 `n ∈ S`，有 `succ n ∈ S`

### Omega 是歸納集

**定理：** `omega` 本身是一個歸納集。

```lean
theorem omega_is_inductive : is_inductive ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero  -- 0 ∈ omega
  · intro n hn
    exact ZFSet.omega_succ hn  -- 如果 n ∈ omega，則 succ n ∈ omega
```

### 輔助公設

為了證明 omega 的最小性，我們需要以下三個基本性質：

#### 1. 正則公設（Axiom of Regularity）

**公設：** 對於任何非空集合 `T`，存在元素 `m ∈ T` 使得 `m ∩ T = ∅`。

```lean
axiom regularity_axiom (T : ZFSet) (h_nonempty : T ≠ ZFSet.empty) :
  ∃ m ∈ T, m ∩ T = ZFSet.empty
```

**說明：**
- 正則公設是 ZFC 的公設之一
- 它保證了集合論中不存在無限下降鏈
- `m ∩ T = ∅` 意味著 `m` 是 `T` 的"最小"元素（在 `∈` 關係下）

#### 2. Omega 的傳遞性（Transitivity of Omega）

**公設：** 在 von Neumann 構造中，如果 `m ∈ omega` 且 `k ∈ m`，則 `k ∈ omega`。

```lean
axiom omega_transitive_axiom (m k : ZFSet) (hm_omega : m ∈ ZFSet.omega) (hk_m : k ∈ m) :
  k ∈ ZFSet.omega
```

**說明：**
- 在 von Neumann 構造中，每個自然數都包含所有比它小的自然數
- 所以如果 `m` 是自然數，且 `k` 是 `m` 的元素，則 `k` 也是自然數
- 這是 omega 定義的直接推論

#### 3. 自然數的結構（Structure of Natural Numbers）

**公設：** 在 von Neumann 構造中，每個自然數要么是 `0`，要么是某個數的後繼。

```lean
axiom nat_structure_axiom (m : ZFSet) (hm_omega : m ∈ ZFSet.omega) :
  m = ZFSet.empty ∨ (∃ k, m = insert k k)
```

**說明：**
- 在 von Neumann 構造中，自然數的定義是：
  - `0 = ∅`
  - `n+1 = n ∪ {n} = insert n n`
- 所以每個自然數要么是 `0`，要么是某個數的後繼
- 這是 omega 定義的直接推論

### 定理：Omega 的最小性

**定理：** 如果 `S` 是歸納集，則 `omega ⊆ S`。

換句話說，`omega` 是**最小的**歸納集。

```lean
theorem omega_minimal (S : ZFSet)
  (h_inductive : is_inductive S):
  ZFSet.omega ⊆ S := by
  rcases h_inductive with ⟨h_zero, h_succ⟩
  intro x hx_omega
  by_contra hx_not_in_S
  let T := ZFSet.sep (fun y => y ∉ S) ZFSet.omega
  have hx_in_T : x ∈ T := by
    rw [ZFSet.mem_sep]
    exact ⟨hx_omega, hx_not_in_S⟩
  have h_T_nonempty : T ≠ ZFSet.empty := by
    intro h_T_empty
    rw [h_T_empty] at hx_in_T
    exact ZFSet.notMem_empty x hx_in_T
  have h_reg : ∃ m ∈ T, m ∩ T = ZFSet.empty := by
    exact regularity_applied T h_T_nonempty
  rcases h_reg with ⟨m, hm_T, hm_disjoint⟩
  have hm_omega : m ∈ ZFSet.omega := by
    rw [ZFSet.mem_sep] at hm_T
    exact hm_T.left
  have hm_not_S : m ∉ S := by
    rw [ZFSet.mem_sep] at hm_T
    exact hm_T.right
  have h_all_in_S : ∀ k ∈ m, k ∈ S := by
    intro k hk_m
    by_contra hk_not_S
    have hk_T : k ∈ T := by
      rw [ZFSet.mem_sep]
      constructor
      · exact omega_transitive m k hm_omega hk_m
      · exact hk_not_S
    have hk_in_inter : k ∈ m ∩ T := by
      rw [ZFSet.mem_inter]
      exact ⟨hk_m, hk_T⟩
    rw [hm_disjoint] at hk_in_inter
    exact ZFSet.notMem_empty k hk_in_inter
  have hm_eq_zero_or_succ : m = ZFSet.empty ∨ (∃ k, m = insert k k) := by
    exact nat_structure m hm_omega
  cases hm_eq_zero_or_succ with
  | inl hm_zero =>
    rw [hm_zero] at hm_not_S
    exact hm_not_S h_zero
  | inr h_succ =>
    rcases h_succ with ⟨k, hm_eq_succ⟩
    have hk_in_S : k ∈ S := h_all_in_S k (by
      rw [hm_eq_succ]
      rw [ZFSet.mem_insert_iff]
      left
      rfl)
    have hm_in_S : m ∈ S := by
      rw [hm_eq_succ]
      exact h_succ k hk_in_S
    exact hm_not_S hm_in_S
```

### 證明思路

**證明策略：** 使用反證法和正則公設。

1. **假設存在 `x ∈ omega` 但 `x ∉ S`**
   - 構造集合 `T = {y ∈ omega : y ∉ S}`
   - `T` 非空（因為 `x ∈ T`）

2. **使用正則公設**
   - 由正則公設，`T` 有最小元素 `m`
   - `m ∈ omega` 且 `m ∉ S`
   - `m ∩ T = ∅`（`m` 的所有元素都不在 `T` 中）

3. **證明 `m` 的所有元素都在 `S` 中**
   - 如果 `k ∈ m` 但 `k ∉ S`，則 `k ∈ T`
   - 但 `k ∈ m ∩ T`，與 `m ∩ T = ∅` 矛盾
   - 所以對所有 `k ∈ m`，有 `k ∈ S`

4. **使用自然數的結構**
   - `m = 0` 或 `m = succ k` 對某個 `k`
   - 如果 `m = 0`，則 `0 ∉ S`，與 `h_zero` 矛盾
   - 如果 `m = succ k`，則 `k ∈ S`（由步驟 3），所以 `m = succ k ∈ S`（由 `h_succ`），與 `m ∉ S` 矛盾

### 關鍵觀察

1. **Omega 是最小的歸納集**
   - 在 ZFC 中，`omega` 通常定義為所有歸納集的交集
   - 因此 `omega` 包含於任何歸納集中

2. **正則公設的作用**
   - 保證了我們可以找到"最小"的元素
   - 避免了無限下降鏈的問題

3. **Von Neumann 構造的性質**
   - 每個自然數都包含所有比它小的自然數
   - 每個自然數要么是 `0`，要么是某個數的後繼

### 應用

Omega 的最小性是證明**數學歸納法原理**（Principle of Mathematical Induction）的關鍵。如果一個性質 `P` 滿足：
- `P(0)`（基始步驟）
- 對所有 `n ∈ omega`，`P(n) → P(succ n)`（歸納步驟）

則對所有 `n ∈ omega`，`P(n)` 成立。

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

