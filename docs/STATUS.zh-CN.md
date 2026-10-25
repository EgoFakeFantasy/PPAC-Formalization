# 当前状态

按最初提交 f28b033 的 1–11 阶段表：**1–3 已完成；4 的原 Main／五端点已验收、Comparator 未验；5–6 部分完成；当前推进 7；8–10 主链未完成；11 未开始。** 不是收尾，最终对象 Con 未证明。

背景为纯成员语言、完整 Separation/Collection 的 nativeZF。终点为原核 `Derives nativeZF [] (Con_ZF → Con_U)`，其中 U = ZF + PP + ACwo + ¬AC，Con 量化全部内部证明码。

## 本轮纠正的实质误报

此前以固定旧版 YesMetaZFC 和另一 LCarrier 工程的边界推断现有资产范围，漏查了 `../yesmetazfc-analytic-comprehension` 的新版底座。这使“尚未定位到任意 nativeZF 模型的 L 终局”的判断不成立。

新版底座 7979336 已有 `InnerModel.l_model_zf_l / l_model_zfc_l / l_model_gch_l`：任意 ZF 模型中的实际内部 L 满足完整 ZF、ZFC、GCH，含全部 Separation/Collection，允许外部非标准、非良基模型。本轮 ZFC 端点定向构建通过（224 任务），三端点 trust=0 依赖审计通过。这里不是只有 ZFSet 上的 LCarrier。

真正待接的是新版供体到本仓固定 039c8e1 底座的版本／语言／对象相对化接口及内部证明归约。不能把这些现成数学定理再列为待证明，也不能把供体模型定理直接当成最终对象 Con。ZFC 依赖闭包有 223 模块，其中旧底座缺 142 个、另有 28 个内容不同；本轮未擅自整体换底座。GCH 不属于当前主线的新增义务。

## 已完成，不再误列待做

- 全语言、重命名／替换、19 源规则原核传输、ZF/U 双向回放、全公理模式和两种 AC 对应。
- 底座内部集合构造、递归和原完备性；BMS 原核回传方法已用于 ModelTransfer。
- 名字、求值、映射、条件作用、check/pair/union 构造、原子递归／定律及公式作用对称性。
- 固定公式强迫与逐固定证明保真；HS 字面定义、空/check 闭包、通用 HS.smul 和实际 HS 域公式对称性。
- 标签置换集、稳定子、共轭集合图、精确稳定子像和子群像闭包。

## 本轮继续迁移

沿锁定 OpenAI `SupportFilter.inf_mem/isNormalFilter → ProductNames.system`，已将新版底座 `Card/Omega` 和 `Card/InfiniteBound` 的五个证明正文原样适配到固定 039c8e1 底座。只改变 import／命名空间；源文件及选取正文哈希纳入 SOURCE_LOCK 并由 verifier 核对。

ForcingSupportIntersection 使用供体 `infinite_union_two_l` 证明实际支撑 J∪J' 仍不超过 μ，再构造交子群的支撑见证。ForcingNormalFilter 合成顶、向上、交、共轭四项，返回 `construction_kernel_certificate`：对内部 ω、无限基数 μ 和任意标签集 I，实际存在完整置换载体 G 与定义正确的正规滤子 F。ω 的基数性由供体证明，不作为新增假设。

本轮完整验收通过：2898 个构建任务，29740 项声明审计（625 项无公理依赖、29115 项依赖已记录）；9 条命令退出 0，其中 5 条 trust=0；零 Lean 警告；2467 份文件哈希匹配。新增 30 项声明、一条原核正规滤子构造证书。原 15 项递归与新消费的 9 项基数 native Bool 证书均重算通过；最终 Con 仍未证明。 具体命令见 verification/commands.json。旧版基数算术额外消费 9 项已有 native Bool 证书；Check.lean 逐项重新计算，SOURCE_LOCK 记录精确名字和底座源哈希。这是活动依赖范围扩大，不是“仅标准三项”或“可信依赖完全未变”；没有向对象 ZF 添加 AC 或新数学公理。

普通正规滤子的四项已完成，不再误列待做。`bot_not_mem` 的非平凡性、具体 ProductNames.actionHom、HS pair/union 及解释后的全 ZF 公理仍未接通。

## 真正剩余

5–6：具体系统呈现、新版现成 L 定理的版本／语言／原核适配。
7：具体条件作用、HS 闭包及解释公理；非平凡性按原 ChoiceFailure 消费者继续迁移。有限并支撑界和四项正规性不再列为缺口。
8–9：原 Algebra/Construction/Models 的构造、不变量、SVC、ACwo、商单射和非选择见证。
10：原 Main 全秩 PP 装配、现成证明机器 ZF/U 特化、全部内部码归约、最终 Con。
11：完整终验。

冻结 NatPacket／字节兼容，排除泛滤真值支线。无现行消费者不自动证明一个已验收引理无用；未对现有证明库按文件名批量删除。本轮清理范围见 CLEANUP。

此前误判的责任在我：没有把旧锁定依赖与用户已经完成的新版库分开，没有充分查明现成接口，又把辅助验收误当成主链接近完成。对象层要求从早期就存在，不能归因于用户改变目标。
