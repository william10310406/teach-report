# Lean 4 集合論證明教學

本教學基於 `textbook.lean` 檔案，詳細講解 Lean 4 中集合論證明的語法和技巧。適合大一學生學習形式化數學證明。

---

## 目錄

1. [基礎語法](#基礎語法)
2. [證明策略詳解](#證明策略詳解)
3. [邏輯連接詞的處理](#邏輯連接詞的處理)
4. [集合運算的證明](#集合運算的證明)
5. [常見證明模式](#常見證明模式)
6. [完整證明範例](#完整證明範例)

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

**成員關係：** `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`

**使用：**
```lean
ZFSet.mem_union.mp   -- x ∈ A ∪ B → x ∈ A ∨ x ∈ B
ZFSet.mem_union.mpr  -- x ∈ A ∨ x ∈ B → x ∈ A ∪ B
```

**重要：在聯集證明中使用 `Or.inl` 和 `Or.inr`**

由于 `x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`，我们需要使用 `Or.inl` 或 `Or.inr` 来構造析取：

- **`Or.inl`**：當 `hx : x ∈ A` 時，構造 `x ∈ A ∨ x ∈ B` 的左分支
- **`Or.inr`**：當 `hx : x ∈ B` 時，構造 `x ∈ A ∨ x ∈ B` 的右分支

**範例 1：基本用法（左分支）**
```lean
theorem example21 (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 目標：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ A，這是 x ∈ A ∨ x ∈ B 的左分支
  -- 所以用 Or.inl hx 構造 x ∈ A ∨ x ∈ B
  -- 然后用 ZFSet.mem_union.mpr 轉換為 x ∈ A ∪ B
  exact ZFSet.mem_union.mpr (Or.inl hx)
```

**範例 2：基本用法（右分支）**
```lean
theorem example21_right (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  -- 目標：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ B，這是 x ∈ A ∨ x ∈ B 的右分支
  -- 所以用 Or.inr hx 構造 x ∈ A ∨ x ∈ B
  exact ZFSet.mem_union.mpr (Or.inr hx)
```

**範例 3：聯集交换律（展示如何選擇正確的分支）**
```lean
theorem example_union_comm (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，這是 x ∈ B ∨ x ∈ A 的右分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ A 是右分支！
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr（右分支）
  | inr hx =>  -- hx : x ∈ B
    -- 目標：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，這是 x ∈ B ∨ x ∈ A 的左分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ B 是左分支！
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl（左分支）
```

**關鍵理解：**

在證明 `x ∈ A ∪ B` 時：
1. 首先理解目標：`x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`
2. 确定你有的證明：`hx : x ∈ A` 或 `hx : x ∈ B`
3. 判断在 `x ∈ A ∨ x ∈ B` 中的位置：
   - 如果 `hx : x ∈ A`，它在**左分支**，用 `Or.inl hx`
   - 如果 `hx : x ∈ B`，它在**右分支**，用 `Or.inr hx`
4. 使用 `ZFSet.mem_union.mpr` 將析取轉換為聯集成員關係

### 4. 交集（`∩`）

**成員關係：** `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`

**使用：**
```lean
ZFSet.mem_inter.mp   -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B
ZFSet.mem_inter.mpr  -- x ∈ A ∧ x ∈ B → x ∈ A ∩ B
```

**範例：**
```lean
theorem example22 (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.left
```

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

---

## 常用技巧總結

### 1. `.mp` 和 `.mpr` - 等价关系的方向转换

#### 1.1 基本概念

在 Lean 中，當有一個等价关系 `P ↔ Q`（雙條件）時，我们可以使用 `.mp` 和 `.mpr` 来提取不同方向的蘊含：

- **`.mp`**：**M**odus **P**onens，从左到右使用等价关系
  - 如果 `h : P ↔ Q`，則 `h.mp : P → Q`
  - 含義：从 `P` 推出 `Q`

- **`.mpr`**：**M**odus **P**onens **R**everse，从右到左使用等价关系
  - 如果 `h : P ↔ Q`，則 `h.mpr : Q → P`
  - 含義：从 `Q` 推出 `P`

**記憶技巧：**
- `.mp` = "正向"（从左到右）
- `.mpr` = "反向"（从右到左）

#### 1.2 `ZFSet.mem_union.mpr` 詳解

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

