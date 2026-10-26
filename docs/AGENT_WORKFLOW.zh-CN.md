# 原 1–11 阶段迁移流程（2026-10-26 重审）

阶段编号恢复为最初提交 `f28b0334a740108057adf18a24dc11abd866efbe` 的表。阶段 0 是来源审查前置；下表不再用四项验收或历史 S3/STEP4 批次重新编号。迁移对象始终为固定 OpenAI PPAC 证明，底座为固定 YesMetaZFC 原推导核。

**实际位置：1–3 已验收；4 原 Main／端点审计已通过、Comparator 未验收；5–6 部分完成。7–10 主数学链没有完成迁移，不能称为收尾。**

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；继续向阶段 7 接实际条件／群／赋值呈现、具体系统中的 HS 作用实例与强迫公式解释。完整阶段的消费者对接尚未验收；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；本轮 InterpretedZF 消费已证全模式回放 | 新版 YesMetaZFC 的任意 ZF 模型内部 L→ZF/ZFC 已定位并验收端点（GCH 不增加为本项目义务）；补其与固定旧版、当前对象语言及原核相对化的接口。停止重证 L 全模式；不把模型定理等同于最终内部 Con |
| 7 | 源强迫前端 | 已固定 Forcing 16 文件，源 atomic/regular/forces_ZF 等证明可复用；左／右／交换归纳已验收；内部条件码上的原子递归及精确方程已验收；基础原子定律和作用对称性已验收；完整公式强迫及 19 规则固定证明保真已验收；公式作用对称性通用迁移已验收；HS 字面定义、展开、唯一性及空/check 闭包已验收；通用 HS.smul 和实际 HS 域公式对称性已验收；标签置换载体、逐点稳定子闭包及逐点共轭已验收；共轭集合图、精确稳定子像与子群像闭包已验收；小支撑族、有限并基数界、交闭包及四项正规性已构造；目标端主链未完成 | Diagram 载体／实际作用图、作用律、子图构造和平移关系不变性已验收；Cohen 坐标及条件载体上的实际保序双射已完整验收；Cohen 群律与实际乘积作用已完整验收；WithTop 载体／固定顶条件／作用律已完整验收；固定载体上的统一标签作用公式、Family/Covariance、支撑滤子 Context 与 HS 作用已完整验收；原 omega/2 载体特化和实际 HS 域公式对称性已完整验收；原单子/conical 合同下的 Diagram→Product→WithTop 预序、反对称性、顶条件已证明；具体单子由阶段 8 提供。实际稳定子子群与 pair/union HS 闭包已证明；已接通 Extensionality、Empty Set、Pairing、Union；已沿源 minimal_member 接通 Foundation；本批沿 mem_check/check_successor 接通 Infinity，原 collectRaw 的内部图精确值域和 collect_HS 合同已迁移；tupleStabilizer 的有限交构造、滤子成员性及实际固定作用已接入原核，并给出 separate 所需共同支撑；已接原 entry_permute/separationTest_permute、精确 separate、mem_separate 与完整 forces_separation；继续 PowerSet 和 Replacement 模式；固定证明实例的 forcing_sound 已完成，内部任意码归约仍归阶段 10；保留全秩和完整模式 |
| 8 | 源代数／构造核心 | Algebra 13、Construction 13 文件已锁定，尚未完成目标端迁移 | 沿原 Monoid/Placement/ConservativeHull 实际构造及不变量迁移；不得以字段假设核心结论 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

阶段 0 已纠正既有资产误分类；本轮重新核对 75 份主链文件哈希全部匹配；原隔离验收另含 3 份入口文件。哈希匹配只证明来源未变，不是这些文件均已迁移。现有 L 完成范围及实际待接接口见 REUSE_CONTRACTS；主数学链见 MATH_REDUCTION_ROUTE。

每个后续改动必须注明：原源文件／定理，目标完整类型，已复用入口，精确背景差异，当前消费者，实际命令和退出码。不能仅给一个名称相似的新辅助定理算迁移完成。

执行顺序：第 4 阶段的原 Main／端点审计已完成，完整 Comparator 保留为独立未验项；第 5–6 阶段只处理进入源强迫链所需的接口，再按源依赖推进 7–10。现有完整模式、识别器、满足关系、完备性不重复建设。若还没找到某个已声称存在的接口，标“未定位到精确合同”，不能直接标“数学未证明”。

背景：纯 ℒ，nativeZF 含全 Separation/Collection，U = ZF+PP+ACwo+¬AC；终点为 `Derives nativeZF [] (Con_ZF → Con_U)`。不添加对象 AC、不可达或新推导核。

一次仅一个 Lean/Lake 构建；正式证明改动运行 scripts/verify.py，检查依赖及禁用缺口。文档改动不触发重复全量编译。保留其他仓库脏改动和已退役反射状态。不用文件数、辅助布尔门或构建任务数估计完成比例。

## 当前直接消费者

原 `tupleStabilizer → entry_permute/separationTest_permute → separate → edge_separate → mem_separate → forces_separation` 已迁移。ForcingSeparation 构造原名字全部边上的内部子名字投影图，选取精确原分离测试；共同稳定子和已有公式对称性证明条目置换，再由既有 collect_HS 给出 HS。ForcingSeparationAxiom 保留源稠密见证和 tuple_congr 证明，封闭原 Separation 公理句子。任意外部公式及有限参数长度均给出原核证书，内部名字／参数无秩界；全部内部证明码仍归阶段 10。

下一直接消费者是原 `SymmetricSets.subsetBound → normalize → power → forces_powerSet`。normalize 直接使用本批已证 separate/mem_separate；不重建分离名字或底座幂集。随后沿 SymmetricChoice 处理 Replacement 的本地见证与群轨道界；源 chosenWitness 的宿主选择必须通过已有内部 Collection／所选背景履行对象见证义务。

以上仍属原阶段 7。当前强迫模式证书保留源单子／呈现／正规滤子前提；阶段 8 必须给出原 Algebra/Construction 的实际构造。阶段 6 的已有 L 接口接入、9 的模型应用、10 的内部码及最终 Con 义务不变。
