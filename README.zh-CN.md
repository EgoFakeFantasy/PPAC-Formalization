# PPAC 向 YesMetaZFC 迁移
[English](README.md)

本分支已完成第一步语言桥、第二步正向句法传输，以及第三步中的反向语法/原核规范化呈现。
第二步覆盖19条源规则，直接给出原FirstOrder.Derives，不经过完备性或模型语义；
闭句源证明可带任意有限变量环境，输出仍为空free上下文。原核证书的有限公理支撑已证明。

最终目标固定为对象ZF中的 Derives B [] (Con_ZF → Con_target)，
参见[内部Con及背景规格](docs/OBJECT_TARGET.zh-CN.md)。
内部ZF/U检查器完整AST、任意内部码正确性与对象主句尚未实现。
第三步已完成七条固定公理的双向原核推导，以及任意参数、任意矩阵的全部源分离模式在原ZF中的推导。
分离模式已覆盖两个方向的全部参数和矩阵，包括任意原生Project矩阵的反向回放。
原Collection加分离已实质推出任意源Replacement实例，并取得原核Derives。
源ZF与源目标理论的全部证明现在可正向回放到真正的原生ZF/目标理论。
原核全部6种推导构造与27类逻辑公理现已反向回放到原19条源规则，实际返回Source.Derives；
覆盖任意有限局部假设，闭句在一个未用源变量的环境中回译。内部编译器表示仍待完成。
对象秩前置已完成全参数的有界极小元和集合内成员归纳模式，源ZF与原生ZF均有实际推导；
每个模式只用Foundation与一个分离实例。原Kuratowski对的全对象存在唯一性与分量刻画亦已完成，
严格匹配源PP/AC编码，只用配对与外延公理。单点函数图已实际构造，原edge/functionOn完整保留，
任意函数图的边输入定义域、域内输出存在及单值性亦有对象推导。任意函数图的新点扩展现已在对象层构造并证明唯一，保留完整functionOn与精确边关系；
前提为新输入x不在旧域。任意图限制亦已实际构造，证明完整原functionOn、精确边、唯一性、恒等及组合律。
任意图的实际定义域以及任意内部相容图集合族（含空族）的并图现已构造并证明唯一，保留完整functionOn和精确边。
内部最小归纳集ω现已实际构造并证明唯一，任意参数公式的对象ω归纳模式及成员刻画已完成。
全部内部ω成员的零/后继分解、ω及其成员的传递性、后继消去与新鲜后继存在已在原核推导；
Foundation和Pairing也给出任意内部集合不自属。完整函数图的逐点外延性、相容图的域包含到图包含、
同域图相等以及实际定义域唯一性现已仅用Extensionality取得原核推导。
现已定义实际并集递推轨迹，并用对象ω归纳证明给定轨迹的全部内部共同输入一致、相容及同域唯一；
这些给定轨迹结果现已用于全部内部n∈ω长度的实际轨迹构造，后继域及图唯一性也已完成。
原Replacement现已实际收集全部内部末值的精确集合；其并集给出∀a∃b(a⊆b∧Transitive(b))的源ZF与原核推导。
任意参数、任意公式的全体集合归纳及无界成员极小元模式现已在源ZF和原核中证明，未假定宿主良基性。
原Source.ordinal及全内部子集极小元定义现已严格保持；序数成员闭包、不自属、实际空序数及后继序数构造已完成。
任意两序数比较、全局ω函数图、最小传递闭包、秩/累积层、
源Replacement到Collection的反向数学方向、两种AC与内部Con仍待完成。
Presentation中的双向回放两端都是原Derives，不能将它读成完整反向编译。
详见[原对象序数基础验收](docs/STEP3_ORDINAL_BASIC_ACCEPTANCE.zh-CN.md)、[全体集合归纳及无界成员极小元验收](docs/STEP3_SET_INDUCTION_ACCEPTANCE.zh-CN.md)、[精确末值集合及对象传递覆盖验收](docs/STEP3_TRANSITIVE_COVER_ACCEPTANCE.zh-CN.md)、[全部内部有限迭代存在唯一验收](docs/STEP3_FINITE_ITERATION_ACCEPTANCE.zh-CN.md)、[给定迭代轨迹唯一性验收](docs/STEP3_ITERATION_UNIQUENESS_ACCEPTANCE.zh-CN.md)、[完整函数图逐点外延性验收](docs/STEP3_GRAPH_POINTWISE_ACCEPTANCE.zh-CN.md)、[对象ω结构验收](docs/STEP3_OMEGA_STRUCTURE_ACCEPTANCE.zh-CN.md)、[对象ω及归纳模式验收](docs/STEP3_OBJECT_OMEGA_ACCEPTANCE.zh-CN.md)、[内部相容图族合并验收](docs/STEP3_GRAPH_FAMILY_ACCEPTANCE.zh-CN.md)、[对象图限制验收](docs/STEP3_GRAPH_RESTRICTION_ACCEPTANCE.zh-CN.md)、[一般新点图扩展验收](docs/STEP3_GRAPH_INSERT_ACCEPTANCE.zh-CN.md)、[对象函数图验收](docs/STEP3_OBJECT_GRAPHS_ACCEPTANCE.zh-CN.md)、[对象有序对验收](docs/STEP3_OBJECT_PAIRS_ACCEPTANCE.zh-CN.md)、[有界正则模式验收](docs/STEP3_BOUNDED_FOUNDATION_ACCEPTANCE.zh-CN.md)、[反向演绎验收](docs/STEP3_REVERSE_DERIVATION_ACCEPTANCE.zh-CN.md)、[Replacement及全正向回放验收](docs/STEP3_REPLACEMENT_FORWARD_ACCEPTANCE.zh-CN.md)及[先前阶段验收](docs/STEP3_ACCEPTANCE.zh-CN.md)。

第一步中的目标理论公理推导只检查连线，不表示 ZF 已证明 PP，也不表示目标理论一致。
默认 import PPAC 只导入迁移主线；旧宿主辅助单独 import PPAC.Auxiliary。
旧宿主 PP 不当作对象 PP，旧研究候选与旧验收已移出活动主线。
清理之前保留了完整 Git bundle 和源码备份，未删除 Git 历史。

运行 python scripts/verify.py；Lean 4.33.1，唯一依赖为固定提交的 YesMetaZFC。
脚本串行构建、trust=0 检查、公理与缺口扫描，记录真实退出码和文件哈希。
verification/ 是本地生成结果，不作为远端验收或自动发布材料。

阅读：
- [可行性与完整边界](docs/FEASIBILITY.zh-CN.md)
- [名下13仓库的用途评估](docs/REPOSITORY_MAP.zh-CN.md)
- [工程流程与逐步验收门](docs/AGENT_WORKFLOW.zh-CN.md)
- [清理决定](docs/CLEANUP.zh-CN.md)
- [当前缺口](GAPS.md)


公理审计边界：固定 YesMetaZFC 的 sentence! 宏用 native_decide 生成7个基础句子的 FreeClosed 证书，原生ZF合同继承其7个 native_decide.ax_1 依赖。见 docs/TRUST_BASELINE.json。当前检查精确守住此基线，不标成“仅三项标准公理”；未修改底座，也未添加新的自定义公理。后续若要求纯内核证书，需另行把这些证书改为 kernel-checked decide 并核对原理论不变。

任意两原对象序数比较更新：OrdinalInitialSegment证明原序数的传递子集等于它或属于它，
OrdinalComparison/Trichotomy给出任意内部序数的三分支比较及两两排斥，另有序数包含当且仅当相等或属于的刻画。
差性质用界a上的有界成员极小元处理，实际有限理论仅含Extensionality、Foundation及正文x∉b的一个Separation实例；
无需Replacement、Collection、传递覆盖或对象AC输入。六条完整闭句均有源Replacement版ZF和原YesMetaZFC核的实际Derives。
实际验收见[对象序数比较验收](docs/STEP3_ORDINAL_COMPARISON_ACCEPTANCE.zh-CN.md)。
内部序数族并集、递归/秩和内部ProofZF/U/Con及最终相对一致性对象主句仍未完成。

任意内部序数族上界更新：OrdinalFamilyOrder证明原序数集合传递时即为原序数；OrdinalUnion实际构造任意内部序数族的并，
并保持原序数定义。UnionUpperBounds证明它在全部内部集合上界中最小且唯一，OrdinalStrictBound以实际后继取得严格序数上界，
使族中每个序数都作为成员属于上界。族可为空，不假设外部有限、可数或已给序数界。
并集/最小上界的有限理论为Extensionality、Foundation、Union和一个分离实例；严格上界再加入Pairing。
六条完整闭句均有源ZF和原YesMetaZFC核的实际Derives；见[序数族并与上界验收](docs/STEP3_ORDINAL_UNION_ACCEPTANCE.zh-CN.md)。
内部递归、秩/累积层、反向Collection及内部ProofZF/U/Con和最终一致性主句仍未完成。

任意参数递归模式更新：OrdinalRecursionSyntax保留原完整functionOn，每条输出边显式存在实际历史限制集合并在其上满足递推公式。
传递初段限制保持递推条件，并用原Separation实际构造受限递归图；算子在原序数索引及有效完整前段图上单值时，
对象有界成员归纳证明给定递归图在所有共同内部位置相容，同域图实际相等。
每个任意参数矩阵都有四个完整闭句及源ZF/原核Derives，有限理论只含Extensionality、Foundation和两个明确Separation实例。
见[递归图限制与相容性验收](docs/STEP3_ORDINAL_RECURSION_COMPATIBILITY_ACCEPTANCE.zh-CN.md)。
这批以前提中的实际递归图为条件；全部内部序数上递归图的存在仍未证明，不能由唯一性代替。
下一项为总算子下实际后继扩展，再以Replacement收集唯一前段图并实际合并；秩及内部Con主句仍未完成。
