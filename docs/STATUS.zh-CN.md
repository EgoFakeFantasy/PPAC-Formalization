# 当前状态：原 1–11 阶段

本批输入基点 `f601e0f`；已直接回读最初 `f28b0334a740108057adf18a24dc11abd866efbe` 的流程核对编号。**实际仍在第 7 阶段，5–6 尚有接入义务，不是收尾。最终对象一致性命题未证明。**

| 原阶段 | 当前实际状态 |
|---|---|
| 1 语言桥 | 已验收，不重做 |
| 2 源推导传输 | 重命名、替换、19 规则到原核及双向回放已验收；全部内部码传输归阶段 10 |
| 3 全理论对应 | 全 Separation/Replacement 与 Separation/Collection、固定公理和两种 AC 已验收 |
| 4 原环境基线 | 原 Main 和五端点已验收；完整 Comparator 未验收 |
| 5 内部构造 | 配对／图／ω／序列／递归、名字、check/pair/union 已验收；实际消费者对接未全部完成 |
| 6 背景和解释 | 相对化／原核回传已有；新版任意 ZF 模型内部 L→ZF/ZFC 已有，版本／语言／原核接入未完成 |
| 7 强迫前端 | 当前阶段。源 Extensionality、EmptySet、Pairing、Union、Foundation、Infinity 六条强迫公理已有原核证书；原 collectRaw/collect_HS、共同支撑、具体 separate 及完整 forces_separation 已迁移；PowerSet 和完整 Replacement 尚未闭合 |
| 8 代数／构造 | 原 Algebra/Construction 的具体单子、placement、conservative hull 和不变量尚未完成目标端迁移 |
| 9 模型应用 | 原 SVC、ACwo、同一系统商单射、非选择见证主链尚未完成目标端迁移 |
| 10 全局装配 | 原 Main 全秩 PP、ZF/U 内部证明码归约及最终 Con 未完成 |
| 11 终验 | 最终主定理验收未开始 |

背景不变：纯成员／等词语言、完整 Separation/Collection 的 nativeZF，原 FirstOrder.Derives。终点为 `Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC；Con 量化全部内部证明码，包括外部非标准码。

## 本批实际推进与验收

沿固定 OpenAI `SymmetricNames.entry_permute → separationTest_permute → separate → edge_separate → mem_separate → forces_separation` 完成当前 HS 解释中的完整 Separation 模式。`ForcingSeparation` 构造原名字全部边上的内部子名字投影图，使用字面的分离测试；实际共同稳定子及已有公式对称性证明条目置换，复用 collect_HS 得到名字的 HS 性质与精确边方程。

`ForcingSeparationAxiom` 保留源 mem_separate 的稠密见证、原子相等替换及公式 tuple_congr，并装配原 SourceStatements.separation 的 close/all/ex/iff/rename。任意外部公式和有限参数长度给出纯对象句子及原 `FirstOrder.Derives nativeZF [] ...` 证书；参数、条件和 HS 名字遍历任意模型内部的对象，没有秩界或外部标准性前提。

**这完成了强迫解释的 Separation 模式，但没有完成全部强迫 ZF 或最终 Con。** 证书保留原单子／呈现／正规滤子前提，预序已由源代数合同推出；阶段 8 的具体构造仍须提供这些前提。任意内部证明码与内部公式码的统一归约仍属阶段 10。

新增 36 项声明、2 项原核证书。完整验收：**2926 项构建任务；9 条命令全部退出 0，其中 5 次 --trust=0；30218 项声明通过，696 项无公理依赖、29522 项使用已记录可信基；0 条编译警告；2495 个当前文件指纹匹配。** 证据：`verification/commands.json`、`summary.json`、`build.log`、`audit.log`、`forcing-separation-preaudit.log` 与 `forcing-separation-full-verification.log`。

可信基没有扩大。具体 Separation 收集实例、精确边／成员等价、完整强迫 Separation 模式标志现为 true；完整强迫 ZF、阶段 8 具体构造及最终对象 Con 仍为 false。现有七项基础句子、15 项递归及九项基数 native Bool 证书继续显式记录／重算。

## 已完成资产与真正缺口

底座完整 ZF 模式、内部递归、Proof/Sat、强完备性都已存在。新版 YesMetaZFC `7979336` 的任意内部 ZF 模型 L→ZF/ZFC 定理与全模式已核实；本批没有重复供体构建。待做的是固定版本／语言／原核接入，不能重新称为“L 尚未证明”。GCH 不增加为本项目义务。BMS 的原核完备性收尾方法已经在 ModelTransfer 中使用。

原 Main 的 8998 项构建与五端点审计属于已有验收，本批未重跑；它不是完整 Comparator，也不表示源模块都已迁移。源 Main 的外部一致性证明不包含本工程要求的完整 ZF 内部 Con 推导，故内部化义务仍须沿原构造完成，不能通过宿主一致性或改名消去。

此前复审已修正覆盖表中将偏序律报为未完成的旧描述：ProductPoset 已从源代数合同推出它们，实际待做的是阶段 8 的具体代数构造。Foundation、Infinity 已从待办删除。collectRaw/collect_HS 合同现已完成。tupleStabilizer、共同支撑、entry_permute、separationTest_permute 和 separate/mem_separate → forces_separation 现已全部接通。下一直接依赖为原 SymmetricSets.subsetBound → normalize → power → forces_powerSet；normalize 直接消费本批已证的分离成员等价。Replacement 继续沿 SymmetricChoice，本地见证义务须使用已选背景及现成内部 Collection 正确处理，不能暗带宿主选择。它们是当前 HS 解释的义务，不是底座缺失，也不是新增工程阶段。

## 清理与此前误判

本批删除已由正式 Audit.lean 接管的一次性 Separation 探针，按绝对路径、普通文件和 SHA-256 白名单核对；预审及全验收日志保留，无新持久脚本或独立验收报告。清单见 CLEANUP。验收后没有残留 Lean/Lake，未修改供体或恢复冻结字节／泛滤真值支线。已验收冻结字节模块仍未全部裁剪，不宣称所有无用代码已删除。

此前失误是将实现选项升级为必经任务、漏查供体和误读已有定理范围，再用辅助编译数量判断主定理进度。对象层要求从早期就已存在，责任在规划和报告。本轮恢复原十一阶段的真实完成边界，不给无依据的“只剩几步”或完成比例。
