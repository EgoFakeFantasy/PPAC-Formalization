# 本地工作进度（2026-11-07）

## 本批验收（2026-11-07）：同根辅助父系统实际构造，仍为阶段 8

`ForcingAssignedParentSystem.construct` 直接复用已有标签系统、顶点／候选名字、完整轨道商／投影、代表与共尾链构造器，再调用既有 `ForcingAssignedParameterConstruction.construct`。在同一个给定根下实际生成 27 个兼容内部集合／函数，保留同一整族记录、全部投影及 Germs；不把轨道、链、记录或参数表作为未消去的输入。

`construction_kernel_certificate` 是原 `nativeZF`／`FirstOrder.Derives` 中同一内部 L 的对象闭句证书，存在量化全部输出。辅助 Choice／全局序由既有 L/ZFC 桥消去；普通背景不增加对象 Choice。原始塔／Context／历史／转移、加权目标、强迫呈现／基数和给定支撑根仍是明确前提，其现成生产者不重建；本批不声称最终全局实例化已完成。

全量验收通过：3197 构建任务，37145 项声明；全部 37136 项旧足迹不变，9 条命令（5 条 trust=0）退出 0，零警告，无新增公理依赖；2752 个当前文件哈希、75 份源哈希及三个干净固定版本均已核对。报告：`verification/assigned-parent-system-acceptance.json`。

下一主线仍是 `ConcreteQuotients.nonwellorderable_quotient_bijection:401–443`：将已完成的实际 outsideClassSet 见证、新根辅助父系统及具体商双射接到同一加强条件，再从现成具体构造器消去最终全局父输入。此项、阶段 9–11、最终覆盖所有内部／非标准证明码的 Con 及原 Comparator 尚未完成。完整局部列表、逆图、持久列表外成员、实际类密度及同根轨道／记录辅助装配均不再列作待从头证明的基础。

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

1. 第 8 阶段：接通 `ConcreteQuotients.nonwellorderable_quotient_bijection:401–443` 及剩余原始／全局父参数实例化；同根轨道／代表／链／整族记录和投影辅助装配已完成。
2. 第 9 阶段：在同一构造中迁移源证明的 SVC、ACwo、全局商集单射和 ¬AC。
3. 第 10 阶段：接通完整 PP/Main，完成 ZF/U 的内部一致性传输。
4. 第 11 阶段：最终对象推导定理、干净检出复现及剩余验收；原 OpenAI Comparator 尚未验收。

复用 YesMetaZFC 与已固定伴随仓库中已有的 L 解释、全体公理模式、递归及 ProofSat 基础。不得把这些已存在的基础重新列为待从头实现。
