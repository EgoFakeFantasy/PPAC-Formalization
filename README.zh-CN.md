# PPAC-Formalization

[English](README.md) | **简体中文**

本仓库收录划分原理（Partition Principle，PP）与选择公理（Axiom of Choice，AC）研究中的 Lean 4 证明组件和接口原型。

**这是一份部分形式化成果。它没有证明 ZF + PP 蕴含 AC，没有构造 ZF + PP + ¬AC 的模型，也没有完成 Cohen、随机或 Fuchs–Prikry 模型相关定理的整体形式化。**

仓库包含已通过检查的证明项，涉及拉回、传递阶段中的捕获、良基关系拼接、关系式部分条件的扩张、编码稠密性论证，以及带显式假设的矛盾推导。较高层模块的名称表示研究动机，不表示相应的模型论应用已经完成。

## 构建与审计

Lean 版本固定为 `leanprover/lean4:v4.33.1`，不依赖外部 Lean 包。

```sh
lake build
lake env lean Audit.lean
python3 scripts/verify.py
```

验证脚本会重新构建证明库，逐项检查 `Audit.lean` 中列出的声明，拒绝不允许的公理依赖和占位证明，并将源码哈希与日志写入 `verification/`。允许的公理依赖仅限于 `propext` 和 `Quot.sound`。统计数量指受审计的声明（包括定义），不表示有同样数量的独立数学定理。

## 形式化范围

| 模块 | 已检查的内容 | 尚缺的内容 |
|---|---|---|
| `Pullback`、`StageCapture` | 满射的拉回恒等式；由传递性与显式类幂集对象推出捕获；最终稳定性 | 与模型内部集合、真类阶段链的衔接 |
| `Choice` | Lean 宿主类型上的良基关系拼接，以及带假设的拆分论证 | 良序化、PP、SVC 和选择原则在模型内部的忠实解释 |
| `Repair` | 关系式条件扩张、编码稠密性，以及依赖显式输入数据的覆盖蕴含 | 真正的力迫语义、旧／新宇宙的区分、具体编码与新鲜性实例、完整的投影提升性质 |
| `ClassObstruction` | 双分支迹分离、拉回，以及显式冻结／新鲜性假设之间的矛盾 | SVC 切片及整体模型层面的障碍论证 |
| `Cohen` | 良基下降，以及秩构成二循环时的矛盾 | 布尔代数、Borel 映射、加速、混合，以及从局部性构造秩的过程 |
| `Random` | 有限列表扩张与支撑引理、良序的转移 | 测度代数、随机力迫、研究笔记 R139 中的反例 |
| `FuchsPrikry` | 抽象数据结构、沿满射转移良序 | 模有限包含关系下的支撑理想、群与滤子的构造，以及实际的等价判据 |

**语义边界。** `PPAC.Choice.WO X` 对 Lean 类型上的所有宿主关系量化，并未把关系限制为某个不满足选择公理的内部模型中的元素。因此，即使一个以 `not WO X` 为假设的条件证明没有公理依赖，也不能据此确认存在满足该假设的 ZF 模型。同样，即使 `#print axioms` 没有列出 `Classical.choice`，显式提供的选择数据参数仍可能携带选择原则的内容。`Repair` 模块目前使用宿主类型 `Nat -> Bool`；真正表示旧模型实数的类型及其模型解释仍然缺失。

具体限制与发布前的修正见[证明覆盖表](THEOREM_COVERAGE.md)、[待补证明清单](GAPS.md)和[发布核查记录](docs/PUBLICATION_REVIEW.md)（这三份文档目前为英文）。

## 来源与参考文献

初始实现：glm5.3f。发布核查、修正与可复现验证：Codex。AI 的实现与核查不等于独立的人类数学认证。本仓库不主张数学成果的优先权。

背景文献（不是已导入的形式化依赖）：

- Thomas Jech，*The Axiom of Choice*（1973），§2.4、Example 2.4.1 与 Lemma 2.7：[原文](https://gwern.net/doc/math/1973-jech-theaxiomofchoice.pdf)。
- C. Ryan-Smith，*Local reflections of choice*，Acta Math. Hungar. **176**（2025），244–257：[DOI](https://doi.org/10.1007/s10474-025-01533-3)。
- A. Karagila，*Iterating Symmetric Extensions*，JSL **84**（2019）：[arXiv](https://arxiv.org/abs/1606.06718)。

本地任务平台记录、私有研究原稿和早期实现报告不包含在本仓库中。
