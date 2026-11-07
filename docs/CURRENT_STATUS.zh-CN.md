# 本地工作进度（2026-11-07）

## 本批验收（2026-11-07）：实际 outsideClassSet_denseBelow，仍为阶段 8

`ForcingOutsideClassSet` 已迁移固定源 `ClassFibers.outsideClassSet:255–262` 与 `outsideClassSet_denseBelow:265–306`。对每个更强内部 Cohen 条件，从非良序性及实际商名字取得 canonical 类，复用现有支撑构造、二集合并基数界及扩图，覆盖完整条件支撑和标签；用 `actual_labelClass/class_unique` 保留同一个实际类并得到本地名字。若右因子为单位，`sub_one` 与根／值域／固定子群唯一性将该名字送回完整原根局部列表，与持久非成员矛盾，因此因子非平凡。

`density_kernel_certificate` 是原 `nativeZF` 中同一内部 L 相对化密度闭句的 `FirstOrder.Derives`，由已完成的 L/ZFC 桥消去辅助 Choice；没有向普通 nativeZF 添加对象 Choice。完整见证保留实际条件、新根、右因子、值域／固定子群、条件码、canonical 类及全部更强条件下的排除。

全量验收通过：9 条命令（5 条 trust=0）退出 0，零警告，37126 项旧声明足迹不变，无新增公理依赖。报告：`verification/outside-class-set-acceptance.json`。

下一主线为 `ConcreteQuotients.nonwellorderable_quotient_bijection:401–443`：消费上述见证和已完成的具体商双射，并从既有构造器统一最终父输入。此项、阶段 9–11、最终内部 Con 仍未完成。完整局部列表、逆图、持久列表外成员和实际类密度不再列为待从头证明的基础。

本分支迁移固定 OpenAI PPAC 源证明到 YesMetaZFC 的原对象推导核，继续采用原计划 1–11 阶段。当前仍在第 8 阶段，最终目标尚未完成。

最终目标：`FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)`，其中 `U = ZF + PP + ACwo + ¬AC`。内部 Con 必须覆盖全部内部证明编码，包括非标准编码。

## 已验收基点

`PPAC/Migration/ForcingCheckOrdinal.lean`（以及此前的 `ForcingConcreteQuotientBijection.lean`、`ForcingAssignedGraphBijection.lean` 和 `ForcingAssignedGraphOnto.lean`）现已完成并接入主入口与全量验收，具体范围与检查记录见 `verification/forcing-check-ordinal-acceptance.json`、`verification/concrete-quotient-bijection-acceptance.json`、`verification/assigned-graph-bijection-acceptance.json` 与 `verification/assigned-graph-onto-acceptance.json`。

已接通实际 Assigned 图的单值性、单射性、全域性、满射性、实际赋值图名字构造与基条件处的强迫双射（`assignmentGraph_bijection`），全轨道参数计数（`all_counts`）、具体商双射（`quotient_bijection_above`），以及纯 `nativeZF` 中核名字序数强迫（`forces_checkOrdinal`）与 `WellorderableF` 核单射反射（`forces_wellorderable` / `wellorderable_of_check_injection` / `no_check_injection_of_not_wellorderable`）。

## 随本快照保存的完成代码

- `PPAC/Migration/ForcingAssignedGraphOnto.lean`：包含 `holds_onto`、`ontoSentence`、`onto_models` 与 `onto_kernel_certificate`。
- `PPAC/Migration/ForcingAssignedGraphBijection.lean`：包含 `relation_moves`、`exists_assignmentGraph`、`assignmentGraph_bijection`、`bijectionSentence`、`bijection_models` 与 `bijection_kernel_certificate`。
- `PPAC/Migration/ForcingConcreteQuotientBijection.lean`：包含 `restricted_fixed_subset`、`all_counts`、`quotient_bijection_above`、`bijectionSentence`、`bijection_models` 与 `bijection_kernel_certificate`。
- `PPAC/Migration/ForcingCheckOrdinal.lean`：包含 `wellorderableFormula`、`wellorderable`、`transF_checkOrdinal`、`ordF_checkOrdinal`、`forces_membershipWellFounded`、`forces_checkOrdinal`、`forces_wellorderable`、`wellorderable_of_check_injection`、`no_check_injection_of_not_wellorderable`、`childClosed`、`childClosed_semantics`、`sentence`、`models` 与 `kernel_certificate`。四者均已加入 `PPAC.lean`、`CheckStep4.lean`、`Audit.lean`、`docs/SOURCE_LOCK.json` 和 `scripts/verify.py` 并通过全量验收。

## 必要的后续工作

1. 第 8 阶段：接通 `ConcreteQuotients.nonwellorderable_quotient_bijection:401–443` 及共同构造参数实例化。
2. 第 9 阶段：在同一构造中迁移源证明的 SVC、ACwo、全局商集单射和 ¬AC。
3. 第 10 阶段：接通完整 PP/Main，完成 ZF/U 的内部一致性传输。
4. 第 11 阶段：最终对象推导定理、干净检出复现及剩余验收；原 OpenAI Comparator 尚未验收。

复用 YesMetaZFC 与已固定伴随仓库中已有的 L 解释、全体公理模式、递归及 ProofSat 基础。不得把这些已存在的基础重新列为待从头实现。
