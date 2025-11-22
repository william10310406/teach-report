# ZFC Axioms in Lean 4

使用 Lean 4 形式化实现的 Zermelo-Fraenkel 集合论（ZFC）公理系统及其应用。

## 📖 项目简介

本项目在 Lean 4 中实现了 ZFC 集合论的公理系统，包括：

- **ZF 公理的完整实现**：外延公理、空集公理、配对公理、并集公理、幂集公理、分离公理、替换公理、无穷公理、选择公理等
- **自然数的构造**：使用 von Neumann 构造法从 ZF 公理出发构造自然数
- **教科书定理的证明**：包含集合论教科书中的经典定理及其形式化证明

## 🏗️ 项目结构

```
lean_zfc/
├── LeanZfc/              # 基础库模块
│   └── Basic.lean        # 基础定义和工具
├── ZFC/                  # ZFC 公理系统核心
│   ├── Axioms.lean       # ZF 公理的实现和陈述
│   ├── AxiomsTutorial.lean # 公理教程和示例
│   ├── Numbers.lean      # 使用 ZF 公理构造自然数
│   ├── textbook.lean     # 教科书中的定理证明
│   ├── Test.lean         # 测试文件
│   └── SimpleTest.lean   # 简单测试
├── Main.lean             # 主入口文件
├── LeanZfc.lean          # 库入口
├── lakefile.lean         # Lake 项目配置
├── lean-toolchain        # Lean 版本配置
└── README.md             # 项目说明
```

## 🚀 快速开始

### 前置要求

- [Lean 4](https://leanprover-community.github.io/get_started.html)（推荐使用最新版本）
- [Elan](https://github.com/leanprover/elan)（Lean 版本管理器）

### 安装步骤

1. **克隆仓库**
   ```bash
   git clone https://github.com/william10310406/teach-report.git
   cd teach-report/lean_zfc
   ```

2. **安装依赖**
   ```bash
   lake update
   lake build
   ```

3. **验证安装**
   ```bash
   lake env lean --version
   ```

### 使用示例

在 VS Code 中打开项目（推荐安装 [lean4 扩展](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)），然后可以：

- 查看 `ZFC/Axioms.lean` 了解 ZF 公理的实现
- 查看 `ZFC/Numbers.lean` 了解自然数的构造
- 查看 `ZFC/textbook.lean` 了解定理的证明

## 📚 主要内容

### ZF 公理系统

项目实现了以下 ZF 公理：

1. **外延公理 (Axiom of Extensionality)**
   - 两个集合相等当且仅当它们有相同的元素

2. **空集公理 (Axiom of Empty Set)**
   - 存在一个不包含任何元素的集合

3. **配对公理 (Axiom of Pairing)**
   - 对于任意两个集合，存在一个包含它们的集合

4. **并集公理 (Axiom of Union)**
   - 对于任意集合，存在一个包含其所有元素的并集

5. **幂集公理 (Axiom of Power Set)**
   - 对于任意集合，存在其所有子集构成的集合

6. **分离公理 (Axiom Schema of Separation)**
   - 对于任意集合和性质，存在满足该性质的子集

7. **替换公理 (Axiom Schema of Replacement)**
   - 对于任意函数和集合，函数的值域是集合

8. **无穷公理 (Axiom of Infinity)**
   - 存在一个包含空集且对每个元素都包含其后继的集合

9. **选择公理 (Axiom of Choice)**
   - 对于任意非空集合族，存在选择函数

### 自然数的构造

使用 von Neumann 构造法从 ZF 公理出发构造自然数：

- `0 = ∅`（空集）
- `1 = {0} = {∅}`
- `2 = {0, 1} = {∅, {∅}}`
- `3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}`
- ...

### 定理证明

包含集合论教科书中的经典定理，如：

- 空集是任何集合的子集
- 集合的包含关系具有传递性
- 集合运算的基本性质
- 等等

## 🛠️ 技术栈

- **Lean 4**：定理证明器和编程语言
- **Mathlib**：Lean 的数学库，提供 ZFC 的基础实现
- **Lake**：Lean 的构建系统和包管理器

## 📝 开发说明

### 构建项目

```bash
lake build
```

### 运行测试

项目中的测试文件位于 `ZFC/Test.lean` 和 `ZFC/SimpleTest.lean`。

### 代码风格

项目遵循 Lean 4 的代码风格指南。建议使用 `lean-toolchain` 文件中指定的 Lean 版本。

## 🤝 贡献

欢迎提交 Issue 和 Pull Request！

## 📄 许可证

本项目采用 MIT 许可证。

## 🔗 相关资源

- [Lean 4 官方文档](https://leanprover-community.github.io/)
- [Mathlib 文档](https://leanprover-community.github.io/mathlib4_docs/)
- [ZFC 集合论](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)

## 👤 作者

william10310406

---

**注意**：本项目主要用于学习和教学目的，展示如何在 Lean 4 中形式化集合论公理系统。

