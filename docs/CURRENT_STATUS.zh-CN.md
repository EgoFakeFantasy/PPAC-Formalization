# 本地工作进度（2026-11-07）

## 本批验收（2026-11-07）：实际逆图与持久列表外成员，仍为阶段 8

`ForcingUniformInverseGraph` 消费已完成的最小下标关系，迁移固定源 `UniformInverse.least_move/relation_move:212–233`、实际逆图／限制逆图单射 `UniformNames:239–277`，以及 `outside_uniformRange:282–311` 对实际完整局部名字列表的消费者 `ClassFibers.outside_localList:224–241`。现有条件置换的逆像保持每个更强条件下的负相等，现有 `map_checked` 给出核名字固定性；现有 HS 图构造器与 `graph_injection` 产生真实受支撑图和完整强迫单射公式。

非良序性直接排除这个实际单射，再用已有成员正则性取得稠密的持久列表外成员；未把不存在单射或逆图当作额外前提。`construction_kernel_certificate` 与 `outside_kernel_certificate` 均为普通 `nativeZF` 中的原 `FirstOrder.Derives` 对象闭句证书，量化全部内部 HS 名字、条件与下标。局部载体／序数枚举／根支撑的父输入仍显式保留，其生产者 `ForcingLocalList.construct` 已有。

全量验收已通过：9 条命令（5 条 trust=0）退出 0，零警告，37104 项旧声明足迹不变，无新增公理依赖。报告：`verification/uniform-inverse-graph-acceptance.json`。

下一项仍是固定源 `outsideClassSet_denseBelow:265`：把成员与实际商的 canonical 类对齐，扩图覆盖条件支撑及标签，并证明右因子非平凡；随后接 `nonwellorderable_quotient_bijection`。这些及阶段 9–11、最终内部 Con 尚未完成。L、全公理模式、递归与 Proof/Sat 基础继续复用，不重建。

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
