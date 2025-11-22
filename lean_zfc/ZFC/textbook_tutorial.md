# Lean 4 集合论证明教程

本教程基于 `textbook.lean` 文件，详细讲解 Lean 4 中集合论证明的语法和技巧。适合大一学生学习形式化数学证明。

---

## 目录

1. [基础语法](#基础语法)
2. [证明策略详解](#证明策略详解)
3. [逻辑连接词的处理](#逻辑连接词的处理)
4. [集合运算的证明](#集合运算的证明)
5. [常见证明模式](#常见证明模式)
6. [完整证明示例](#完整证明示例)

---

## 基础语法

### 1. 定理声明

```lean
theorem 定理名称(参数 : 类型) : 要证明的命题 := by
  -- 证明步骤
```

**示例：**
```lean
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- 证明步骤
```

**解释：**
- `theorem`：声明一个定理
- `theorem_2_1_1_a`：定理的名称
- `(A : ZFSet)`：参数 A，类型是 ZFSet（集合）
- `: ∅ ⊆ A`：要证明的命题（空集是 A 的子集）
- `:= by`：开始证明

### 2. 注释

```lean
-- 这是单行注释
-- 可以解释证明步骤的含义
```

---

## 证明策略详解

### 1. `intro` - 引入假设

**作用：** 将目标中的 `∀`（全称量词）或 `→`（蕴含）的前件引入为假设。

**语法：**
```lean
intro 变量名
```

**示例 1：处理全称量词**
```lean
theorem example1 (A : ZFSet) : A ⊆ A := by
  intro x hx  -- 引入 ∀ x, x ∈ A → x ∈ A 中的 x 和 x ∈ A
  exact hx     -- 直接使用假设 hx : x ∈ A
```

**解释：**
- 目标：`A ⊆ A`，展开为 `∀ x, x ∈ A → x ∈ A`
- `intro x`：引入任意元素 x
- `intro hx`：引入假设 `x ∈ A`
- 新目标：`x ∈ A`
- `exact hx`：直接使用假设完成证明

**示例 2：处理蕴含**
```lean
theorem example2 (A B : ZFSet) : (A ⊆ B) → (A ⊆ B) := by
  intro h  -- 引入前提 A ⊆ B 作为假设 h
  exact h   -- 直接使用假设
```

### 2. `exact` - 直接完成证明

**作用：** 当目标正好等于某个已有的假设或定理时，直接使用它完成证明。

**语法：**
```lean
exact 表达式
```

**示例：**
```lean
theorem example3 (A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx  -- hx 正好是目标 x ∈ A
```

### 3. `have` - 声明中间步骤

**作用：** 在证明过程中声明一个中间结果，可以给这个结果命名并在后续使用。

**语法：**
```lean
have 名称 : 类型 := 证明
```

**示例：**
```lean
theorem example4 (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h
  rcases h with ⟨hAB, hBC⟩
  intro x hxA
  have hxB : x ∈ B := hAB hxA  -- 声明中间步骤：x ∈ B
  have hxC : x ∈ C := hBC hxB  -- 使用上一步的结果
  exact hxC
```

**解释：**
- `have hxB : x ∈ B := hAB hxA`：
  - `hxB`：给这个中间结果命名
  - `: x ∈ B`：这个中间结果的类型
  - `:= hAB hxA`：如何证明它（使用 hAB 和 hxA）

### 4. `rcases` - 分解合取/析取

**作用：** 将合取（`∧`）或析取（`∨`）分解成多个假设。

**语法：**
```lean
rcases 假设 with ⟨假设1, 假设2, ...⟩  -- 合取
rcases 假设 with 假设1 | 假设2         -- 析取
```

**示例 1：分解合取**
```lean
theorem example5 (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h  -- h : A ⊆ B ∧ B ⊆ C
  rcases h with ⟨hAB, hBC⟩  -- 分解：hAB : A ⊆ B, hBC : B ⊆ C
  -- 现在可以使用 hAB 和 hBC
```

**示例 2：分解析取**
```lean
theorem example6 (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h
  rcases h with hx | hx  -- 分两种情况：x ∈ A 或 x ∈ B
  · exact Or.inl hx
  · exact Or.inr hx
```

### 5. `constructor` - 分解双条件

**作用：** 将双条件 `↔` 分解成两个方向：`→` 和 `←`。

**语法：**
```lean
constructor
· -- 证明第一个方向
· -- 证明第二个方向
```

**示例：**
```lean
theorem example7 (A B x : ZFSet) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  constructor
  · intro h  -- 方向1：x ∈ A ∩ B → x ∈ A ∧ x ∈ B
    -- 证明步骤
  · intro h  -- 方向2：x ∈ A ∧ x ∈ B → x ∈ A ∩ B
    -- 证明步骤
```

### 6. `apply` - 应用定理

**作用：** 当目标匹配某个定理的结论时，应用该定理，目标变成证明该定理的前提。

**语法：**
```lean
apply 定理名
```

**示例：**
```lean
theorem example8 (A : ZFSet) : A = A := by
  apply ZFSet.ext  -- 应用外延性公理
  -- 目标从 A = A 变成 ∀ x, x ∈ A ↔ x ∈ A
  intro x
  constructor
  · intro hx; exact hx
  · intro hx; exact hx
```

**解释：**
- `ZFSet.ext` 是外延性公理：`A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`
- `apply ZFSet.ext` 后，目标从 `A = A` 变成 `∀ x, x ∈ A ↔ x ∈ A`

### 7. `rw` / `rewrite` - 重写

**作用：** 使用等式或等价关系重写目标或假设。

**语法：**
```lean
rw [等式]           -- 在目标中重写
rw [等式] at 假设    -- 在假设中重写
rw [← 等式]         -- 反向重写（从右到左）
```

**示例：**
```lean
theorem example9 (A B : ZFSet) : A = B → A = B := by
  intro h  -- h : A = B
  rw [h]   -- 将目标中的 A 替换为 B，目标变成 B = B
  rfl      -- 自反性
```

**示例 2：在假设中重写**
```lean
theorem example10 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h
  rcases h with ⟨hA, hB⟩
  rw [hA] at hB  -- 在 hB 中将 A 替换为 ∅
  -- 现在 hB : ∅ = ∅
```

### 8. `calc` - 链式等式

**作用：** 通过一系列等式链式证明。

**语法：**
```lean
calc
  表达式1 = 表达式2 := 证明1
  _ = 表达式3 := 证明2
  _ = 表达式4 := 证明3
```

**示例：**
```lean
theorem example11 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h
  rcases h with ⟨hA, hB⟩
  calc
    A = ∅ := hA      -- A = ∅
    _ = B := hB.symm -- ∅ = B（hB.symm 将 B = ∅ 转换为 ∅ = B）
```

**解释：**
- `_` 表示上一步的表达式（这里是 `∅`）
- `hB.symm` 是 `hB : B = ∅` 的对称形式：`∅ = B`

### 9. `by_contra` - 反证法

**作用：** 假设结论的否定，推出矛盾。

**语法：**
```lean
by_contra 假设名  -- 假设结论的否定
-- 证明步骤，最终推出矛盾
```

**示例：**
```lean
theorem example12 (A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  by_contra hx_in_A  -- 假设 x ∈ A（要证明 x ∉ A，所以假设其否定）
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A  -- 推出 x ∈ B
  exact hx_notin_B hx_in_B  -- 矛盾：x ∉ B 和 x ∈ B
```

**解释：**
- 要证明 `x ∉ A`，使用反证法假设 `x ∈ A`
- 从 `x ∈ A` 和 `A ⊆ B` 推出 `x ∈ B`
- 但前提有 `x ∉ B`，矛盾
- 因此 `x ∉ A` 成立

### 10. `cases` - 分情况讨论

**作用：** 对析取命题（`∨`）进行分情况讨论。

**语法：**
```lean
cases 假设 with
| inl 假设1 => -- 左分支的情况
| inr 假设2 => -- 右分支的情况
```

**示例：**
```lean
theorem example13 (A x : ZFSet) : x ∈ A ∪ ∅ → x ∈ A := by
  intro h  -- h : x ∈ A ∪ ∅
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ ∅
  cases h with
  | inl hx => exact hx        -- 情况1：x ∈ A，直接得到目标
  | inr hx => exact False.elim (ZFSet.notMem_empty x hx)  -- 情况2：x ∈ ∅，矛盾
```

**解释：**
- `inl`：Left，表示析取的左分支
- `inr`：Right，表示析取的右分支
- 两种情况都要处理

---

## 逻辑连接词的处理

### 1. 合取（`∧`）- "且"

**构造：** 使用 `⟨证明1, 证明2⟩`
```lean
have h : P ∧ Q := ⟨证明P, 证明Q⟩
```

**分解：** 使用 `rcases` 或 `.left` / `.right`
```lean
rcases h with ⟨hP, hQ⟩
-- 或
have hP : P := h.left
have hQ : Q := h.right
```

**示例：**
```lean
theorem example14 (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h  -- h : x ∈ A ∩ B
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.left  -- 取出 x ∈ A
```

### 2. 析取（`∨`）- "或"

#### 2.1 构造析取：`Or.inl` 和 `Or.inr`

**类型签名：**
```lean
Or.inl {a b : Prop} (h : a) : a ∨ b  -- 左注入（Left injection）
Or.inr {a b : Prop} (h : b) : a ∨ b  -- 右注入（Right injection）
```

**详细说明：**

- **`Or.inl`**：将类型为 `a` 的证明注入到 `a ∨ b` 的左分支
  - 如果 `h : a`，则 `Or.inl h : a ∨ b`
  - 表示"选择左分支"，即"a 成立"

- **`Or.inr`**：将类型为 `b` 的证明注入到 `a ∨ b` 的右分支
  - 如果 `h : b`，则 `Or.inr h : a ∨ b`
  - 表示"选择右分支"，即"b 成立"

**构造语法：**
```lean
have h : P ∨ Q := Or.inl 证明P  -- 左分支：证明 P，得到 P ∨ Q
have h : P ∨ Q := Or.inr 证明Q  -- 右分支：证明 Q，得到 P ∨ Q
```

**重要理解：**

1. **`Or.inl` 和 `Or.inr` 的选择取决于目标类型**
   - 如果目标是 `P ∨ Q`，且我们有 `h : P`，则用 `Or.inl h`
   - 如果目标是 `P ∨ Q`，且我们有 `h : Q`，则用 `Or.inr h`

2. **在并集证明中的应用**
   - `x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ A`，要证明 `x ∈ A ∪ B`，需要构造 `x ∈ A ∨ x ∈ B`
   - 因为 `x ∈ A` 是 `x ∈ A ∨ x ∈ B` 的**左分支**，所以用 `Or.inl hx`
   - 如果 `hx : x ∈ B`，要证明 `x ∈ A ∪ B`，需要构造 `x ∈ A ∨ x ∈ B`
   - 因为 `x ∈ B` 是 `x ∈ A ∨ x ∈ B` 的**右分支**，所以用 `Or.inr hx`

**示例 1：基本用法**
```lean
theorem example15 (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 目标：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ A，这是 x ∈ A ∨ x ∈ B 的左分支
  exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl 选择左分支
```

**示例 2：使用右分支**
```lean
theorem example15_right (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  -- 目标：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ B，这是 x ∈ A ∨ x ∈ B 的右分支
  exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr 选择右分支
```

**示例 3：在并集交换律中的应用**
```lean
theorem example_union_comm (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，这是 x ∈ B ∨ x ∈ A 的右分支
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr（注意：在 B ∨ A 中，A 是右分支）
  | inr hx =>  -- hx : x ∈ B
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，这是 x ∈ B ∨ x ∈ A 的左分支
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl（注意：在 B ∨ A 中，B 是左分支）
```

**关键要点：**

- **`Or.inl`** = "Left injection" = 注入到左分支
- **`Or.inr`** = "Right injection" = 注入到右分支
- 选择哪个取决于**目标析取类型中证明所在的位置**
  - 如果证明在目标类型的**左边**，用 `Or.inl`
  - 如果证明在目标类型的**右边**，用 `Or.inr`

**常见错误：**

```lean
-- ❌ 错误示例
theorem wrong (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  exact ZFSet.mem_union.mpr (Or.inl hx)  -- 错误！x ∈ B 是 x ∈ A ∨ x ∈ B 的右分支，应该用 Or.inr

-- ✅ 正确示例
theorem correct (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  exact ZFSet.mem_union.mpr (Or.inr hx)  -- 正确！x ∈ B 是 x ∈ A ∨ x ∈ B 的右分支
```

#### 2.2 分解析取：`cases` 和 `rcases`

**分解语法：**
```lean
cases h with
| inl hP => -- 处理 P 的情况（hP : P）
| inr hQ => -- 处理 Q 的情况（hQ : Q）
```

**示例：**
```lean
theorem example16 (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx => exact Or.inl hx  -- 情况1：hx : x ∈ A，构造 x ∈ A ∨ x ∈ B 的左分支
  | inr hx => exact Or.inr hx  -- 情况2：hx : x ∈ B，构造 x ∈ A ∨ x ∈ B 的右分支
```

### 3. 蕴含（`→`）- "如果...那么"

**引入：** 使用 `intro`
```lean
intro h  -- 引入前提作为假设
```

**应用：** 直接使用函数应用
```lean
have hQ : Q := hP_to_Q hP  -- 如果 hP_to_Q : P → Q，hP : P，则 hQ : Q
```

**示例：**
```lean
theorem example16 (A B x : ZFSet) : A ⊆ B → (x ∈ A → x ∈ B) := by
  intro hAB hxA  -- hAB : A ⊆ B, hxA : x ∈ A
  exact hAB hxA  -- 直接应用 hAB 到 hxA
```

### 4. 双条件（`↔`）- "当且仅当"

**分解：** 使用 `constructor`
```lean
constructor
· -- 证明 P → Q
· -- 证明 Q → P
```

**示例：**
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
by_contra h  -- 假设 P，推出矛盾，从而证明 ¬P
```

**否定消除：** 直接应用
```lean
have : False := h_notP hP  -- 如果 h_notP : ¬P，hP : P，则矛盾
```

**示例：**
```lean
theorem example18 (A x : ZFSet) : x ∉ ∅ := by
  exact ZFSet.notMem_empty x  -- 空集没有元素
```

---

## 集合运算的证明

### 1. 子集关系（`⊆`）

**定义：** `A ⊆ B := ∀ x, x ∈ A → x ∈ B`

**证明模式：**
```lean
theorem subset_proof (A B : ZFSet) : A ⊆ B := by
  intro x hx  -- 引入任意 x 和假设 x ∈ A
  -- 证明 x ∈ B
```

**示例：**
```lean
theorem example19 (A : ZFSet) : A ⊆ A := by
  intro x hx
  exact hx  -- 直接使用假设
```

### 2. 集合相等（`=`）

**使用外延性公理：**
```lean
apply ZFSet.ext  -- 将 A = B 转换为 ∀ x, x ∈ A ↔ x ∈ B
intro x
constructor
· -- 证明 x ∈ A → x ∈ B
· -- 证明 x ∈ B → x ∈ A
```

**示例：**
```lean
theorem example20 (A : ZFSet) : A = A := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx; exact hx
  · intro hx; exact hx
```

### 3. 并集（`∪`）

**成员关系：** `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`

**使用：**
```lean
ZFSet.mem_union.mp   -- x ∈ A ∪ B → x ∈ A ∨ x ∈ B
ZFSet.mem_union.mpr  -- x ∈ A ∨ x ∈ B → x ∈ A ∪ B
```

**重要：在并集证明中使用 `Or.inl` 和 `Or.inr`**

由于 `x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`，我们需要使用 `Or.inl` 或 `Or.inr` 来构造析取：

- **`Or.inl`**：当 `hx : x ∈ A` 时，构造 `x ∈ A ∨ x ∈ B` 的左分支
- **`Or.inr`**：当 `hx : x ∈ B` 时，构造 `x ∈ A ∨ x ∈ B` 的右分支

**示例 1：基本用法（左分支）**
```lean
theorem example21 (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 目标：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ A，这是 x ∈ A ∨ x ∈ B 的左分支
  -- 所以用 Or.inl hx 构造 x ∈ A ∨ x ∈ B
  -- 然后用 ZFSet.mem_union.mpr 转换为 x ∈ A ∪ B
  exact ZFSet.mem_union.mpr (Or.inl hx)
```

**示例 2：基本用法（右分支）**
```lean
theorem example21_right (A B x : ZFSet) : x ∈ B → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ B
  -- 目标：x ∈ A ∪ B，即 x ∈ A ∨ x ∈ B
  -- 我们有 hx : x ∈ B，这是 x ∈ A ∨ x ∈ B 的右分支
  -- 所以用 Or.inr hx 构造 x ∈ A ∨ x ∈ B
  exact ZFSet.mem_union.mpr (Or.inr hx)
```

**示例 3：并集交换律（展示如何选择正确的分支）**
```lean
theorem example_union_comm (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，这是 x ∈ B ∨ x ∈ A 的右分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ A 是右分支！
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 Or.inr（右分支）
  | inr hx =>  -- hx : x ∈ B
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，这是 x ∈ B ∨ x ∈ A 的左分支
    -- 注意：在 x ∈ B ∨ x ∈ A 中，x ∈ B 是左分支！
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 Or.inl（左分支）
```

**关键理解：**

在证明 `x ∈ A ∪ B` 时：
1. 首先理解目标：`x ∈ A ∪ B` 等价于 `x ∈ A ∨ x ∈ B`
2. 确定你有的证明：`hx : x ∈ A` 或 `hx : x ∈ B`
3. 判断在 `x ∈ A ∨ x ∈ B` 中的位置：
   - 如果 `hx : x ∈ A`，它在**左分支**，用 `Or.inl hx`
   - 如果 `hx : x ∈ B`，它在**右分支**，用 `Or.inr hx`
4. 使用 `ZFSet.mem_union.mpr` 将析取转换为并集成员关系

### 4. 交集（`∩`）

**成员关系：** `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`

**使用：**
```lean
ZFSet.mem_inter.mp   -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B
ZFSet.mem_inter.mpr  -- x ∈ A ∧ x ∈ B → x ∈ A ∩ B
```

**示例：**
```lean
theorem example22 (A B x : ZFSet) : x ∈ A ∩ B → x ∈ A := by
  intro h
  have h_pair : x ∈ A ∧ x ∈ B := ZFSet.mem_inter.mp h
  exact h_pair.left
```

### 5. 差集（`A - B`）

**定义：** `set_diff A B = {x ∈ A : x ∉ B}`

**成员关系：** `x ∈ set_diff A B ↔ x ∈ A ∧ x ∉ B`

**使用：**
```lean
(mem_diff A B x).mp   -- x ∈ A - B → x ∈ A ∧ x ∉ B
(mem_diff A B x).mpr  -- x ∈ A ∧ x ∉ B → x ∈ A - B
```

**示例：**
```lean
theorem example23 (A x : ZFSet) : x ∈ A → x ∈ set_diff A ∅ := by
  intro hx
  exact (mem_diff A ∅ x).mpr ⟨hx, ZFSet.notMem_empty x⟩
```

---

## 常见证明模式

### 模式 1：传递性证明

**模式：** 证明 `A ⊆ B` 和 `B ⊆ C` 推出 `A ⊆ C`

```lean
theorem transitivity (A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h
  rcases h with ⟨hAB, hBC⟩
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  have hxC : x ∈ C := hBC hxB
  exact hxC
```

### 模式 2：外延性证明

**模式：** 证明两个集合相等

```lean
theorem extensionality (A B : ZFSet) : A = B := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx  -- x ∈ A → x ∈ B
    -- 证明步骤
  · intro hx  -- x ∈ B → x ∈ A
    -- 证明步骤
```

### 模式 3：反证法

**模式：** 假设结论的否定，推出矛盾

```lean
theorem by_contradiction (A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  by_contra hx_in_A  -- 假设 x ∈ A
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A
  exact hx_notin_B hx_in_B  -- 矛盾
```

### 模式 4：分情况讨论

**模式：** 对析取命题分情况处理

```lean
theorem case_analysis (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h
  rw [ZFSet.mem_union] at h
  cases h with
  | inl hx => exact Or.inl hx
  | inr hx => exact Or.inr hx
```

### 模式 5：空真命题

**模式：** 从矛盾推出任何结论

```lean
theorem vacuous_truth (A : ZFSet) : ∅ ⊆ A := by
  intro x hx  -- hx : x ∈ ∅（这是矛盾的）
  have : False := ZFSet.notMem_empty x hx
  exact this.elim  -- 从矛盾推出任何东西
```

---

## 完整证明示例

### 示例 1：空集是任何集合的子集

```lean
theorem theorem_2_1_1_a(A : ZFSet) : ∅ ⊆ A := by
  intro x hx
  -- hx : x ∈ ∅，但空集没有元素，这是矛盾的
  have : False := ZFSet.notMem_empty x hx
  -- 从矛盾可以推出任何东西（包括 x ∈ A）
  exact this.elim
```

**步骤解析：**
1. `intro x hx`：引入 `∀ x, x ∈ ∅ → x ∈ A` 中的 x 和 `x ∈ ∅`
2. `have : False := ZFSet.notMem_empty x hx`：从 `x ∈ ∅` 推出矛盾
3. `exact this.elim`：从矛盾推出任何结论（包括 `x ∈ A`）

### 示例 2：集合包含关系的传递性

```lean
theorem theorem_2_1_1_c(A B C : ZFSet) : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intro h  -- h: A ⊆ B ∧ B ⊆ C
  rcases h with ⟨hxAB, hxBC⟩  -- 分解：hxAB: A ⊆ B, hxBC: B ⊆ C
  intro x hxA  -- hxA: x ∈ A
  have hxB : x ∈ B := hxAB hxA  -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B
  have hxC : x ∈ C := hxBC hxB  -- ∵ x ∈ B ∧ B ⊆ C ∴ x ∈ C
  exact hxC
```

**步骤解析：**
1. `intro h`：引入前提 `A ⊆ B ∧ B ⊆ C`
2. `rcases h with ⟨hxAB, hxBC⟩`：分解合取，得到两个子集关系
3. `intro x hxA`：引入任意元素 x 和假设 `x ∈ A`
4. `have hxB : x ∈ B := hxAB hxA`：应用 `A ⊆ B` 得到 `x ∈ B`
5. `have hxC : x ∈ C := hxBC hxB`：应用 `B ⊆ C` 得到 `x ∈ C`
6. `exact hxC`：完成证明

### 示例 3：使用外延性公理证明集合相等

```lean
theorem thm2_1_2 (A B : ZFSet) : (A = ∅ ∧ B = ∅) → A = B := by
  intro h  -- h: A = ∅ ∧ B = ∅
  rcases h with ⟨hA, hB⟩  -- hA: A = ∅, hB: B = ∅
  -- 使用 calc 进行链式等式证明：A = ∅ = B
  calc
    A = ∅ := hA  -- hA: A = ∅
    _ = B := hB.symm  -- hB : B = ∅，所以 hB.symm : ∅ = B
```

**步骤解析：**
1. `intro h`：引入前提
2. `rcases h with ⟨hA, hB⟩`：分解合取
3. `calc`：使用链式等式
   - `A = ∅ := hA`：第一步
   - `_ = B := hB.symm`：第二步（`_` 表示上一步的结果 `∅`）

### 示例 4：反证法

```lean
theorem exercise_2_1_7(A B x : ZFSet) : (x ∉ B ∧ A ⊆ B) → x ∉ A := by
  intro h  -- h: x ∉ B ∧ A ⊆ B
  rcases h with ⟨hx_notin_B, hA_subset_B⟩
  -- By contradiction, suppose x ∈ A
  by_contra hx_in_A  -- 假设 x ∈ A（要证明 x ∉ A，所以假设其否定）
  -- ∵ x ∈ A ∧ A ⊆ B ∴ x ∈ B
  have hx_in_B : x ∈ B := hA_subset_B hx_in_A
  -- ∵ x ∈ B ∧ x ∉ B ∴ False
  exact hx_notin_B hx_in_B
```

**步骤解析：**
1. `intro h`：引入前提
2. `rcases h with ⟨hx_notin_B, hA_subset_B⟩`：分解合取
3. `by_contra hx_in_A`：假设 `x ∈ A`（要证明 `x ∉ A`）
4. `have hx_in_B : x ∈ B := hA_subset_B hx_in_A`：推出 `x ∈ B`
5. `exact hx_notin_B hx_in_B`：矛盾（`x ∉ B` 和 `x ∈ B`）

### 示例 5：复杂的外延性证明

```lean
theorem exercise_2_1_18_a(A B : ZFSet) : A = B ↔ ZFSet.powerset A = ZFSet.powerset B := by
  constructor
  · intro h  -- h: A = B
    rw [h]  -- 如果 A = B，直接重写即可得到 𝒫(A) = 𝒫(B)
  · intro h  -- h: 𝒫(A) = 𝒫(B)
    -- 步骤 1：证明 A ∈ 𝒫(A)（因为 A ⊆ A）
    have hA_in_powerset_A : A ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr (fun x hx => hx)
    -- 步骤 2：由于 𝒫(A) = 𝒫(B)，所以 A ∈ 𝒫(B)，即 A ⊆ B
    have hA_in_powerset_B : A ∈ ZFSet.powerset B := by
      rw [← h]  -- 将 𝒫(B) 重写为 𝒫(A)
      exact hA_in_powerset_A
    have hA_subset_B : A ⊆ B := ZFSet.mem_powerset.mp hA_in_powerset_B

    -- 步骤 3：类似地，B ∈ 𝒫(B)，所以 B ∈ 𝒫(A)，即 B ⊆ A
    have hB_in_powerset_B : B ∈ ZFSet.powerset B := ZFSet.mem_powerset.mpr (fun x hx => hx)
    have hB_in_powerset_A : B ∈ ZFSet.powerset A := by
      rw [h]  -- 将 𝒫(A) 重写为 𝒫(B)
      exact hB_in_powerset_B
    have hB_subset_A : B ⊆ A := ZFSet.mem_powerset.mp hB_in_powerset_A

    -- 步骤 4：由 A ⊆ B 和 B ⊆ A，使用外延性公理得到 A = B
    apply ZFSet.ext  -- 将 A = B 转换为 ∀ x, x ∈ A ↔ x ∈ B
    intro x  -- 引入任意元素 x，需要证明 x ∈ A ↔ x ∈ B
    constructor  -- 将双条件 ↔ 分解成两个方向
    · exact fun hx => hA_subset_B hx  -- 方向1：x ∈ A → x ∈ B
    · exact fun hx => hB_subset_A hx  -- 方向2：x ∈ B → x ∈ A
```

**步骤解析：**
1. `constructor`：分解双条件 `↔`
2. 第一个方向：`A = B → 𝒫(A) = 𝒫(B)`，直接重写
3. 第二个方向：`𝒫(A) = 𝒫(B) → A = B`
   - 证明 `A ∈ 𝒫(A)`（因为 `A ⊆ A`）
   - 利用 `𝒫(A) = 𝒫(B)` 得到 `A ∈ 𝒫(B)`，即 `A ⊆ B`
   - 类似地得到 `B ⊆ A`
   - 使用外延性公理得到 `A = B`

---

## 常用技巧总结

### 1. `.mp` 和 `.mpr` - 等价关系的方向转换

#### 1.1 基本概念

在 Lean 中，当有一个等价关系 `P ↔ Q`（双条件）时，我们可以使用 `.mp` 和 `.mpr` 来提取不同方向的蕴含：

- **`.mp`**：**M**odus **P**onens，从左到右使用等价关系
  - 如果 `h : P ↔ Q`，则 `h.mp : P → Q`
  - 含义：从 `P` 推出 `Q`

- **`.mpr`**：**M**odus **P**onens **R**everse，从右到左使用等价关系
  - 如果 `h : P ↔ Q`，则 `h.mpr : Q → P`
  - 含义：从 `Q` 推出 `P`

**记忆技巧：**
- `.mp` = "正向"（从左到右）
- `.mpr` = "反向"（从右到左）

#### 1.2 `ZFSet.mem_union.mpr` 详解

**类型签名：**
```lean
ZFSet.mem_union : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

ZFSet.mem_union.mp   : x ∈ A ∪ B → x ∈ A ∨ x ∈ B  -- 从并集成员关系推出析取
ZFSet.mem_union.mpr  : x ∈ A ∨ x ∈ B → x ∈ A ∪ B  -- 从析取推出并集成员关系
```

**详细说明：**

`ZFSet.mem_union` 是一个等价关系，表示：
- `x ∈ A ∪ B`（x 是 A 和 B 的并集的成员）
- 当且仅当
- `x ∈ A ∨ x ∈ B`（x 属于 A 或 x 属于 B）

**`ZFSet.mem_union.mpr` 的作用：**

`ZFSet.mem_union.mpr` 将析取（`∨`）转换为并集成员关系（`∈ A ∪ B`）。

**使用场景：**

当我们需要证明 `x ∈ A ∪ B` 时，通常的步骤是：

1. **构造析取**：先证明 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ A`，用 `Or.inl hx` 构造 `x ∈ A ∨ x ∈ B`
   - 如果 `hx : x ∈ B`，用 `Or.inr hx` 构造 `x ∈ A ∨ x ∈ B`

2. **转换为并集**：使用 `ZFSet.mem_union.mpr` 将析取转换为并集成员关系
   - `ZFSet.mem_union.mpr (Or.inl hx)` 或
   - `ZFSet.mem_union.mpr (Or.inr hx)`

**完整示例：**

```lean
theorem example_union_left (A B x : ZFSet) : x ∈ A → x ∈ A ∪ B := by
  intro hx  -- hx : x ∈ A
  -- 步骤 1：构造析取 x ∈ A ∨ x ∈ B
  have h_or : x ∈ A ∨ x ∈ B := Or.inl hx  -- 用 Or.inl 选择左分支
  -- 步骤 2：转换为并集成员关系
  exact ZFSet.mem_union.mpr h_or
  -- 或者直接写成：
  -- exact ZFSet.mem_union.mpr (Or.inl hx)
```

**常见模式：**

```lean
-- 模式 1：x ∈ A → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inl hx)  -- hx : x ∈ A

-- 模式 2：x ∈ B → x ∈ A ∪ B
exact ZFSet.mem_union.mpr (Or.inr hx)  -- hx : x ∈ B

-- 模式 3：在分情况讨论中使用
cases h with
| inl hx => exact ZFSet.mem_union.mpr (Or.inl hx)  -- 情况1：x ∈ A
| inr hx => exact ZFSet.mem_union.mpr (Or.inr hx)  -- 情况2：x ∈ B
```

**`ZFSet.mem_union.mp` 的作用（反向）：**

`ZFSet.mem_union.mp` 将并集成员关系转换为析取：

```lean
theorem example_union_mp (A B x : ZFSet) : x ∈ A ∪ B → (x ∈ A ∨ x ∈ B) := by
  intro h  -- h : x ∈ A ∪ B
  exact ZFSet.mem_union.mp h  -- 转换为 x ∈ A ∨ x ∈ B
```

**其他集合运算的类似用法：**

```lean
-- 交集
ZFSet.mem_inter.mp   -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B
ZFSet.mem_inter.mpr  -- x ∈ A ∧ x ∈ B → x ∈ A ∩ B

-- 差集（使用自定义的 mem_diff）
(mem_diff A B x).mp   -- x ∈ A - B → x ∈ A ∧ x ∉ B
(mem_diff A B x).mpr  -- x ∈ A ∧ x ∉ B → x ∈ A - B

-- 幂集
ZFSet.mem_powerset.mp   -- x ∈ 𝒫(A) → x ⊆ A
ZFSet.mem_powerset.mpr  -- x ⊆ A → x ∈ 𝒫(A)
```

**关键理解：**

1. **`.mpr` 用于"构造"**：当我们有析取（`x ∈ A ∨ x ∈ B`）时，用 `.mpr` 转换为并集成员关系（`x ∈ A ∪ B`）

2. **`.mp` 用于"分解"**：当我们有并集成员关系（`x ∈ A ∪ B`）时，用 `.mp` 转换为析取（`x ∈ A ∨ x ∈ B`）

3. **配合 `Or.inl` 和 `Or.inr` 使用**：
   - 先构造析取：`Or.inl hx` 或 `Or.inr hx`
   - 再转换为并集：`ZFSet.mem_union.mpr (Or.inl hx)`

**实际应用示例（并集交换律）：**

```lean
theorem thm_2_2_1_i (A B x : ZFSet) : x ∈ A ∪ B → x ∈ B ∪ A := by
  intro h  -- h : x ∈ A ∪ B
  rw [ZFSet.mem_union] at h  -- h : x ∈ A ∨ x ∈ B
  cases h with
  | inl hx =>  -- hx : x ∈ A
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ A，这是 x ∈ B ∨ x ∈ A 的右分支
    exact ZFSet.mem_union.mpr (Or.inr hx)  -- 用 .mpr 转换为并集
  | inr hx =>  -- hx : x ∈ B
    -- 目标：x ∈ B ∪ A，即 x ∈ B ∨ x ∈ A
    -- 我们有 hx : x ∈ B，这是 x ∈ B ∨ x ∈ A 的左分支
    exact ZFSet.mem_union.mpr (Or.inl hx)  -- 用 .mpr 转换为并集
```

**总结：**

- `ZFSet.mem_union.mpr` 是证明 `x ∈ A ∪ B` 的关键工具
- 它需要配合 `Or.inl` 或 `Or.inr` 使用
- 记住：先构造析取，再用 `.mpr` 转换为并集成员关系

### 2. `.left` 和 `.right`

从合取命题中提取左右部分：
```lean
h.left   -- 如果 h : P ∧ Q，则 h.left : P
h.right  -- 如果 h : P ∧ Q，则 h.right : Q
```

### 3. `.symm`

等式的对称形式：
```lean
h.symm  -- 如果 h : A = B，则 h.symm : B = A
```

### 4. `False.elim`

从矛盾推出任何结论：
```lean
False.elim 矛盾  -- 从 False 推出任何类型
```

### 5. `rfl` / `rfl`

自反性，用于证明 `x = x`：
```lean
rfl  -- 证明任何 x = x
```

---

## 练习建议

1. **从简单开始**：先理解 `intro`、`exact`、`have` 等基础策略
2. **逐步增加复杂度**：学习 `rcases`、`constructor`、`apply` 等
3. **理解逻辑连接词**：掌握 `∧`、`∨`、`→`、`↔`、`¬` 的处理方法
4. **熟悉集合运算**：理解子集、并集、交集、差集的定义和使用
5. **练习常见模式**：传递性、外延性、反证法等

---

## 参考资料

- [Lean 4 官方文档](https://leanprover-community.github.io/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib 文档](https://leanprover-community.github.io/mathlib4_docs/)

---

**祝学习愉快！** 🎓

