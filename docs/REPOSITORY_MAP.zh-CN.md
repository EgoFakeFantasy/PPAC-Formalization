# 名下仓库复用评估

2026-10-25 用户纠正：不能停留在README级评估。现已核对可调用的底座及其他项目收尾接口，具体复用决定、前提和验收见 [REUSE_CONTRACTS](REUSE_CONTRACTS.zh-CN.md)。
2026-10-21 通过已连接 GitHub owner 列表确认账号 EgoFakeFantasy，共13仓库。
下述相关仓库逐一读取当前 README；这些是接口候选，不是本轮重新验证的定理。

| 仓库 | 对本迁移的帮助 | 用法与限制 |
|---|---|---|
| [YesMetaZFC](https://github.com/EgoFakeFantasy/YesMetaZFC) | 必需直接依赖 | 原纯语言、Hilbert推导、Collection版ZF、递归/集合图、模型可靠性。固定039c8e1；不整库迁入或重启退役反射。 |
| [PPAC-Formalization](https://github.com/EgoFakeFantasy/PPAC-Formalization) | 迁移承载、少量条件辅助 | 保留清单见 CLEANUP；旧宿主PP不是对象PP，旧验收不等于迁移验收。 |
| [BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) | 有效的可选工程先例 | BMSTools 的集合构造、内部递归、有限赋值/记录编码、有符号真值证书；SecondOrderHereditaryBMSWellOrder.derives_m 是按实例交付 Derives 的先例。需逐模块核实依赖，不导入BMS终局或大基数。 |
| [IBLP-Wellfoundedness](https://github.com/EgoFakeFantasy/IBLP-Wellfoundedness) | 可选编码/语义参考 | SetAssignmentDecoding、SetSatisfaction、GraphEvaluation、Collapse 等有内部图和赋值经验；Lean4.30+mathlib 与 I3/反射背景不同，不把宿主模型定理当对象推导，不直接作为步骤1依赖。 |
| [FullMarkedBLP](https://github.com/EgoFakeFantasy/FullMarkedBLP) | 有限工程参考 | 模块化与定理陈述核对/审计模板；I2/Steel良基结果没有所需强迫内容，不作为数学依赖。 |
| [InfinitaryCombinatorics](https://github.com/EgoFakeFantasy/InfinitaryCombinatorics) | 局部组合工具候选 | 有限交、理想、序数指标等只在新图式具体引理需要时选用；mathlib4.30且有元层选择，当前不引入。 |
| [OpenProblemFormalizations](https://github.com/EgoFakeFantasy/OpenProblemFormalizations) | 审计方式参考 | 定义/条件结果/未完结论分离；未找到该PP模型直接模块，当前不依赖。 |
| [RankElementarity](https://github.com/EgoFakeFantasy/RankElementarity) | 当前无直接帮助 | 秩初等/反射背景不是本轮普通相对一致性的构造输入。 |
| [PCFAlephOmega4](https://github.com/EgoFakeFantasy/PCFAlephOmega4) | 当前无直接帮助 | PCF应用不提供本次语法桥或对称图式强迫；不引入。 |
| huanbiao-consistency-atlas | 理论强度导航 | 展示文献关系，不是形式证明库。 |
| agent-plaza / EFF / qq-assistant-core | 无数学依赖 | 协作或产品项目，不能提供ZF推导证书。 |

只把 YesMetaZFC 放入本次 Lake 依赖。其余“有效帮助”是按接口分层可选复用，
不是仅凭仓库名相近就整体引入。IBLP/BLP 等未经本轮全量构建。

另一本地现成项目 `lean-constructible-universe-stage4` 已有 LStageZF、Def／Gödel运算、逐公式编译和集合满足关系配套；应消费其构造与有限公式，补到本项目语言／背景／原核的必要接口，不重新从外部工程造同类基础。其 ZFSet 特定模型终局与本项目的原ZF内部Con目标仍须通过实际接口衔接。

本轮纠错：本地新版 YesMetaZFC `work/yesmetazfc-analytic-comprehension`（7979336）具有任意内部 ZF 模型的 Jensen L、全 Separation/Collection、ZFC/GCH 结论及内部 forcing 配套。此前只查固定旧版和另一 LCarrier 工程不充分；精确端点审计、版本差异和移植边界见 REUSE_CONTRACTS。活动 Lake 依赖仍为固定 039c8e1，不能声称新版已接入。
