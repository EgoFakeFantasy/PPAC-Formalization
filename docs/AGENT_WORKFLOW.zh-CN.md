# 原 1–11 阶段迁移流程（2026-10-26 重审）

阶段编号恢复为最初提交 `f28b0334a740108057adf18a24dc11abd866efbe` 的表。阶段 0 是来源审查前置；下表不再用四项验收或历史 S3/STEP4 批次重新编号。迁移对象始终为固定 OpenAI PPAC 证明，底座为固定 YesMetaZFC 原推导核。

**实际位置：1–3 已验收；4 尚未验收；5–6 部分完成。7–10 主数学链没有完成迁移，不能称为收尾。**

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 本轮重算固定源 75 文件 SHA-256，全部匹配；源证明端点已读 | 原 Comparator 尚未运行；新增隔离的原版 4.34.1；目标仓仍用 4.33.1。官方 GitHub 同版工具链已下载并验 SHA-256；75 源模块和 Mathlib 的 9 个依赖提交均保持原样。隔离目录中原 Main 定向构建已启动，尚未验收；本机缺 Linux/landrun，完整 Comparator 未运行，本仓 CheckStep4 不是此验收 |
| 5 | 内部名字、图、元组、递归 | 已有对象配对／图／ω／序列／原内部递归；固定 Def、原历史与规范参数已接入；原 ForcingNames.Child 对象归纳已验收；集合条件 P 的 IsName 定义、原展开方程及可定义解唯一性已验收；内部集合 G 的全秩 evaluate 已验收；可定义 mapConditions 的存在、唯一、成员／边展开及空名字已完整验收 | 继续原 mapConditions_id／comp、IsName.mapConditions、evaluate_mapConditions，再接 Name.act；不重造现成基础，不开发字节兼容 |
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；本轮 InterpretedZF 消费已证全模式回放 | 其他 L 工程的 ZF/ZFC 结论已有；核对并补到当前对象解释的接口和真实前提。原 LCarrier 是 ZFSet 子类，不能直接代替所有 nativeZF 模型的结论 |
| 7 | 源强迫前端 | 已固定 Forcing 16 文件，源 atomic/regular/forces_ZF 等证明可复用；尚无完成的目标端主链 | 迁移原 poset/正规滤子/HS、原子递归、逐公式 forcing_sound、全部解释公理；保留全秩和完整模式 |
| 8 | 源代数／构造核心 | Algebra 13、Construction 13 文件已锁定，尚未完成目标端迁移 | 沿原 Monoid/Placement/ConservativeHull 实际构造及不变量迁移；不得以字段假设核心结论 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

阶段 0 本轮纠正了既有资产误分类；75 文件哈希匹配只证明来源未变，不是 75 文件均已迁移。现有 L 完成范围及实际待接接口见 REUSE_CONTRACTS；主数学链见 MATH_REDUCTION_ROUTE。

每个后续改动必须注明：原源文件／定理，目标完整类型，已复用入口，精确背景差异，当前消费者，实际命令和退出码。不能仅给一个名称相似的新辅助定理算迁移完成。

执行顺序：先关闭第 4 阶段的原环境复现证据；第 5–6 阶段只处理进入源强迫链所需的接口，再按源依赖推进 7–10。现有完整模式、识别器、满足关系、完备性不重复建设。若还没找到某个已声称存在的接口，标“未定位到精确合同”，不能直接标“数学未证明”。

背景：纯 ℒ，nativeZF 含全 Separation/Collection，U = ZF+PP+ACwo+¬AC；终点为 `Derives nativeZF [] (Con_ZF → Con_U)`。不添加对象 AC、不可达或新推导核。

一次仅一个 Lean/Lake 构建；正式证明改动运行 scripts/verify.py，检查依赖及禁用缺口。文档改动不触发重复全量编译。保留其他仓库脏改动和已退役反射状态。不用文件数、辅助布尔门或构建任务数估计完成比例。

当前批次：原 ForcingNames.lean:96–128 的 mapConditions 递归、成员／边展开及空名字。任意参数公式表示条件映射，其全定义单值性保留为对象前提；对象名字不设秩界。已有 Child 归纳、Collection、函数式 Replacement、积、分离和原 ModelTransfer 被实际消费。完整验收已通过；阶段 5 整体及最终 Con 均未完成。

本批完整验收通过：2841 构建任务、28968 项声明审计（555 项无公理依赖、28413 项依赖已记录）、9 条命令退出 0、5 条 trust=0、零警告；新增 69 项声明全部覆盖，2431 份源码哈希全部一致。五类 mapConditions 原核证书仅继承标准三项及原七项 ZF 句子证书。
