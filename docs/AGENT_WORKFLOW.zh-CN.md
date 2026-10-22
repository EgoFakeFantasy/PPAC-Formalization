# 对象层迁移工程流程
最终交付：Derives B [] (Formula.imp Con_ZF Con_target)。
B固定原YesMetaZFC的ZF纯语言像，不额外加入AC、不可达或Con(B)。
内部Con的展开、编码与全内部ω范围见[对象目标规格](OBJECT_TARGET.zh-CN.md)。
这里只按明确工作单元推进，不要求并行启动agent；Lean/Lake构建始终串行。

| 步骤 | 输入与负责职责 | 必须交付的模块/结果 | 验收门 | 状态 |
|---|---|---|---|---|
| 0 | 来源审查：固定OpenAI244/YesMetaZFC/PPAC | SOURCE_LOCK、REPOSITORY_MAP、CLEANUP | 来源/前提分开；备份可恢复 | 完成 |
| 1 | 原语言与原核接口 | SourceSyntax、SourceStatements、Translation、Contract | 全8构造器语义保真；正确对象句子 | 完成，中间层 |
| 2 | 19条源规则与原Hilbert核 | SyntaxTransport、SourceDerivation、DerivationTransport、TheoryTransport、FiniteSupport | 非单射rename、嵌套instantiate、fresh量词、等词、任意n闭句、有限公理支撑；原核回放与trust=0 | 完成，正向传输 |
| 3a | 原生11构造器／源8构造器、原核theory_cut | Normalization、ReverseSyntax、Presentation、SourceTheory | 全公式严格往返/规范化；量词下任意替换；原核对象等价；任意理论与开放推导回放；源九类ZF溯源 | 完成，中间层 |
| 3b | 源Replacement版ZF与原Collection版ZF | ZFEquivalence、CollectionFromReplacement、ReverseZFReplay | 七固定公理、全参数Separation与Collection/Replacement两个方向的实际Derives，完整开放推导回放 | 完成；内部证明码表示仍归步骤5 |
| 3b.1 | Foundation与一个全分离实例 | MinimalPredicates、MinimalLogic、MinimalInstances、BoundedMinimal、BoundedInduction | 每个任意参数矩阵产生完整闭句；源Replacement版ZF及原nativeZF均有实际Derives | 完成：有界极小元和集合内成员归纳 |
| 3b.2 | 纯对象集合图与内部ω迭代 | Pairs、Omega、FiniteIteration、TransitiveClosure | Kuratowski编码唯一性；内部ω的全部成员上迭代；源ZF证明每个集合有传递覆盖集 | 内部有限迭代、末值精确族及每集合传递覆盖完成；不使用Collection作为输入 |
| 3b.2a | 原源Kuratowski定义、Pairing与Extensionality | PairSyntax、UnorderedPairLogic、OrderedPairExistence/Elimination/Witnesses/Logic、ObjectPairs | 原源编码严格rfl；全对象存在唯一、分量相等刻画；源ZF和原核Derives；含重复分量 | 完成 |
| 3b.2b | 3b.2a及源图定义 | Graphs、Omega、FiniteIteration、TransitiveClosure | 对象函数图操作；内部ω有限迭代；源Replacement版ZF内传递覆盖集 | 内部有限迭代、末值精确族及每集合传递覆盖完成 |
| 3b.2b.1 | 原edge/functionOn与对象有序对 | GraphSyntax、GraphLogic、GraphProperties、SingletonGraphLogic、SingletonMap、ObjectGraphs | 完整原公式严格对应；单点函数图实际存在；任意图的边定义域、域内输出存在及单值性；原核Derives | 完成 |
| 3b.2b.2 | 源集合图和Pairing/Union/Extensionality/Separation | 图插入、相容图合并、限制、定义域/求值 | 实际构造集合图，证明完整原functionOn及边刻画，保持全部对象参数 | 图插入、限制及任意内部相容族合并完成 |
| 3b.2b.2a | Pairing、Union、Extensionality及原functionOn | InsertSyntax/Logic/Existence、GraphInsert*、ObjectGraphInsert | 任意旧函数图与x∉d下的实际扩展图存在唯一；完整functionOn及全部边刻画；源ZF与原核Derives | 完成 |
| 3b.2b.2b | 全Separation、Union与Extensionality | 图限制、任意内部相容图集合族的合并 | 对象域/图的存在唯一及精确边关系；覆盖任意内部集合族 | 图限制及任意内部相容族合并完成 |
| 3b.2b.2b.i | Extensionality及一个完整Separation实例 | RestrictionSyntax/Edges/Function/Algebra/Existence、ObjectRestriction | 任意图的限制集合实际存在；子域上的原functionOn、精确边、唯一/恒等/组合闭句 | 完成 |
| 3b.2b.2b.ii | 原对象Kuratowski编码、Union、Extensionality与一个Separation实例 | GraphDomain*、GraphFamily*、ObjectGraphFamily | 任意图定义域实际存在唯一；任意内部相容图集合族（含空族）并图存在唯一；完整原functionOn和精确边关系 | 完成 |
| 3b.2b.3 | 3b.2b.2与Infinity/Separation | 内部ω、有限迭代、传递覆盖 | 覆盖全部内部ω成员；对象图存在唯一；不假设外部标准ω | 内部有限迭代、末值精确族及传递覆盖完成 |
| 3b.2b.3a | 原Infinity、Extensionality及完整Separation | OmegaSyntax/Universal/Cut/Existence/Algebra、OmegaInduction*、ObjectOmega | 实际最小归纳集合ω存在唯一；任意参数公式的每个模式实例均有完整对象ω归纳闭句及原核Derives | 完成 |
| 3b.2b.3a.i | 对象ω归纳及原Foundation/集合图设施 | OmegaStructureSyntax/Induction/Algebra、OmegaElementary、ObjectIrreflexivity、ObjectOmegaStructure | 内部0/后继分解、成员闭包/传递性、后继消去及迭代图所需的新输入不在旧域事实；均保留对象量词 | 完成 |
| 3b.2b.3b | 3b.2b.3a、图扩展/限制/相容合并及Replacement | GraphPointwise、FiniteIteration、TransitiveCover | 完整图外延性；全部内部n的唯一有限图及末值；Replacement精确收集末值后取并，构造传递覆盖 | 内部有限轨迹存在唯一、末值精确集合及传递覆盖完成 |
| 3b.2b.3b.i | 原完整functionOn、Kuratowski边和Extensionality | GraphPointwiseSyntax/Entries/Domain、GraphPointwise、ObjectGraphPointwise | 逐边相等推出实际图相等；相容函数域包含推出图包含；同域图相等；实际定义域唯一；源ZF与原核Derives | 完成 |
| 3b.2b.3b.ii | 对象ω归纳、Extensionality和一个四参数Separation实例 | IterationSyntax/Values/Step/Induction/Compatibility、ObjectIterationUniqueness | 给定并集递推轨迹在全部内部共同输入相等、相容及同域唯一；实际轨迹存在另外验收 | 相容/唯一完成；实际存在见下一行 |
| 3b.2b.3b.iii | 对象图扩展、ω归纳、Extensionality/Pairing/Union/Foundation与四个完整Separation实例 | FiniteIterationSyntax/Uniqueness、IterationBase/Existence、IterationExtension*、IterationExistence、ObjectFiniteIteration | 全部内部n∈ω的实际有限图存在；后继域与图唯一；原完整functionOn/种子/递推条件；源ZF与原核Derives | 完成 |
| 3b.2b.3b.iv | 上项全内部存在唯一、原Replacement与Union | IterationContext、IterationValue*/Range*、TransitiveCover*、ObjectTransitiveCover | 实际取得全部内部n末值的精确集合并取并；无额外前提的∀a∃b(a⊆b∧Transitive(b))，源ZF和原核Derives | 完成 |
| 3b.3 | 3b.1–3b.2及全Replacement | Ordinals、Recursion、Rank、CumulativeHierarchy | 内部序数比较/极小秩、秩覆盖与Vα存在性；原推导核全参数证明 | 完成：对象集合归纳、原序数/族上界、完整超限递归、层代数、全内部集合覆盖及实际唯一秩；不使用宿主WellFounded |
| 3b.3a | 实际传递覆盖、有界成员归纳、Foundation及相应完整Separation实例 | SetInductionSyntax/Logic、SetInduction、GlobalMinimalSyntax、GlobalMinimal | 每个任意参数公式有全体集合归纳与无界成员极小元的完整对象闭句；源ZF和原核Derives；不引入统一真值谓词 | 完成 |
| 3b.3b | 原Source.ordinal、Foundation/EmptySet/Pairing/Union | OrdinalSyntax/Foundation/Transitivity/Restriction/Empty/Successor、ObjectOrdinalBasic | 原定义严格rfl；全内部子集极小元、不自属、成员闭包、实际空/后继序数；源ZF与原核Derives | 完成 |
| 3b.3c | 原序数基础、Extensionality、Foundation及正文x∉b的一个Separation | OrdinalDifference、OrdinalInitialSegment、OrdinalComparison/Trichotomy、ObjectOrdinalComparison | 内部传递子集为初段或相等；任意两个原序数三歧比较及两两排斥，保留全部对象序数量词；六条原核闭句 | 完成 |
| 3b.3d | 原序数比较、Extensionality/Foundation/Union与一个Separation；严格界加Pairing | OrdinalFamilySyntax/Order、UnionUpperBounds、OrdinalUnion/StrictBound、ObjectOrdinalUnion | 任意内部序数集合的实际并是原序数，且在全部内部集合上界中最小唯一；实际严格序数上界；六条原核闭句 | 完成 |
| 3b.3e | 原序数比较、完整图限制/扩展/相容族并、对象集合归纳及全Replacement | OrdinalRecursionSyntax/Compatibility/Existence | 任意参数公式给出的单值总递推算子，在全部内部序数上的完整递归图存在唯一；先证共同初段相容，再构造实际图；不以宿主递归替代 | 完成；全部内部原序数上实际存在唯一，见ObjectTransfiniteRecursion |
| 3b.3e.i | 原完整functionOn、实际历史限制、Extensionality/Foundation与两个Separation | RestrictionHistory、OrdinalRecursionSyntax/Restriction/Determinism/History/Values/Compatibility、ObjectOrdinalRecursion | 每个任意参数递推公式有四个完整闭句：传递初段保持、实际限制图、给定原序数域图相容与同域唯一 | 完成；以前提中实际递归图为条件 |
| 3b.3e.ii | 原图新鲜扩展、有效序数/完整历史上的总性；Extensionality/Foundation/Pairing/Union和一个Separation | GraphInsertRestriction/Elimination、OrdinalRecursionTotal/ExtensionAlgebra/Extension/SuccessorSyntax/SuccessorExistence/SuccessorUnique、ObjectOrdinalRecursionSuccessor | 实际下一值、保留旧前段的实际后继递归扩展、实际唯一后继图纤维及原Replacement接口；六个原核模式 | 完成 |
| 3b.3e.iii | 实际后继唯一纤维、全Replacement、相容图族并和对象集合归纳 | OrdinalRecursionCollection/Union/Existence | Replacement收集全部内部前驱的实际唯一后继图，合并并校验精确域和历史方程，取得全部内部序数上的递归图存在唯一 | 完成 |
| 3b.3f | 内部序数递归、PowerSet、序数族严格界与全Replacement | Rank、CumulativeHierarchy | 实际Vα及秩覆盖；每个需要模式均提供完整对象句子和原核Derives | 完成：实际层值、完整层代数、全体集合的层包含/成员覆盖和实际唯一最小秩 |
| 3b.3f.i | 原对象PowerSet、完整超限递归、精确图值域及原Replacement | PowerSetOperation、HierarchyRecursion | 实际构造并证明有效历史上算子F(h)=∪{P(z):z为h的值}总单值；实例化递归，取得全部内部α的实际Vα | 完成；算子前提已实际消去，零层为空亦证明 |
| 3b.3f.ii | 原完整图限制/相容、实际幂集并算子和层值、序数比较与对象归纳 | HierarchyMembership、HierarchyAlgebra | 历史图早期值与相应Layer严格对应；层成员递归公式、后继/极限层公式、层单调/传递 | 完成；历史对应、成员递归、单调/传递与零/后继/极限式均有原核闭句 |
| 3b.3f.ii.a | 实际后继域限制、递归图相容、PowerSet及精确像/并 | HierarchyHistory、HierarchyMemberSyntax/Transfer、PowerUnionMembership、HierarchyMembership/Algebra/Successor、ObjectHierarchyAlgebra | 全部内部α/β的早期值双向对应、完整成员递归、包含单调、早层实际成员、层传递及后继PowerOf；七条原核闭句 | 完成；见STEP3_HIERARCHY_ALGEBRA_ACCEPTANCE.zh-CN.md |
| 3b.3f.ii.b | 已证成员递归、后继幂集、层存在唯一及一个原Replacement实例 | HierarchyLimitSyntax/Membership、HierarchyFamilySyntax/Union、HierarchyLayerCollection、ObjectHierarchyLimit | 全内部零或极限索引的成员并式；实际精确早层集合和原UnionOf；六条原核闭句 | 完成；见STEP3_LIMIT_AND_ORDINAL_LEAST_ACCEPTANCE.zh-CN.md |
| 3b.3f.iii | 原序数比较、全参数成员极小元、对象传递覆盖 | OrdinalLeastSyntax/Logic/Existence、ObjectOrdinalLeast | 任意可定义非空序数性质的实际唯一最小序数；源ZF与原核全参数存在/唯一纤维/值相等三个模式 | 完成；外部模式索引保留，每个实例有实际闭句Derives |
| 3b.3f.iv | 实际层代数、序数最小元、全Replacement和序数族严格界 | LayerCoverSyntax/Induction/Membership、LayerRankSyntax/Collection/Bound、ObjectRankCover | 任意内部集合实际包含于某层、具有唯一最小包含层秩并属于某层；源ZF与原核完整推导 | 完成；见STEP3_RANK_COVER_ACCEPTANCE.zh-CN.md |
| 3b.3f.iv.a | 实际Layer、任意参数序数最小元及原Replacement接口 | LayerCoverSyntax、LayerRankSyntax、LayerCoverClosedInstances | 定义x⊆Vα及其唯一最小内部序数索引；唯一秩纤维逐式匹配原Replacement矩阵 | 完成；归纳步内仅从成员覆盖前提取得唯一秩 |
| 3b.3f.iv.b | 上项唯一纤维、全Replacement及序数族严格界 | LayerRankCollection、LayerRankBound | 实际收集所有成员的唯一秩，取共同严格序数界和实际层值，证明原集合包含于该层 | 完成；精确秩像、序数性及全部内部成员覆盖均已证明 |
| 3b.3f.iv.c | 上项进步步、对象全体集合归纳及后继PowerOf | LayerCoverInduction、LayerCoverMembership、ObjectRankCover | 全内部层包含、实际唯一秩、实际成员覆盖及成员秩精确族；六条原核闭句 | 完成；无未证归纳/算子前提残留 |
| 3b.4 | 已证全内部集合秩覆盖、序数最小元、全Replacement与层成员递归 | WitnessRankSyntax/Fibers/Collection/Bounds、CollectionFromReplacement | 取唯一最小见证秩，实际共同界层给真实原关系见证；完整原Collection句子 | 完成；见STEP3_FULL_ZF_EQUIVALENCE_ACCEPTANCE.zh-CN.md |
| 3b.4.a | 任意参数关系p、全体集合唯一秩、最小序数模式 | WitnessRankSyntax/Fibers | 定义∃y(p(x,y)∧Rank(y,α))；从实际见证取得唯一最小见证秩，匹配原Replacement矩阵 | 完成；不要求原见证唯一，不选择宿主见证族 |
| 3b.4.b | 上项唯一纤维、原Replacement和任意内部序数族严格界 | WitnessRankCollection/Bounds | 实际精确秩族、共同严格界及真实层值；对每个x取得层内原p见证，证明原Collection完整覆盖 | 完成；全部原参数、内部量词和非函数关系均保留 |
| 3b.4.c | 上项全Collection模式、已证完整双向Separation及固定公理 | CollectionFromReplacement、ReverseZFReplay | 任意源/原生Project矩阵的完整Collection；原ZF九类公理及ZF/目标理论任意开放推导双向回放 | 完成；闭句可实际回到源19规则，外部变量环境为1 |
| 3c | 原六规则Hilbert证书与源19规则 | ReverseDerivation | 全27逻辑模式/6构造→原源演绎；任意局部假设、非单射变量环境；闭句在一个未用变量中回译 | 完成，外部证书传输；内部码表示归步骤5 |
| 3d | 源图选择与原生不交族选择集 | ChoiceSyntax、ObjectGraphChoiceSelector、ObjectSelectorGraphChoice、ChoiceNativeBridge | 原ZF内双向对象推导，内部集合图、全量词、无外加AC | 完成；原nativeZF核已有原AC与原Axioms.choice的双条件 |
| 3d.a | 原Source.choiceOn/AC与原Axioms.choice | ChoiceSyntax、ChoiceNativeBridge | 两种原公式严格对应；完整functionOn、全内部族和唯一交点；原Axioms.choice AST精确接合 | 完成；原choice闭性证书额外依赖单列CHOICE_TRUST_BASELINE.json |
| 3d.b | 完整选择图、实际函数值精确像及不交性 | GraphRangeSyntax/Collection、ChoiceLogic/SelectorPoints、GraphChoiceToSelector、ObjectGraphChoiceSelector | 一个明确Replacement实例实际取得精确值集合；逐成员交点存在唯一；图AC→原选择集AC原核闭句 | 完成；源有限理论核心仅标准三项依赖 |
| 3d.c | 原Pairing/Extensionality及两个明确Replacement、Kuratowski分量唯一性 | TaggedRowSyntax/Existence/Logic、TaggedFamilySyntax/Context/Collection/Logic | 实际构造每个成员x的带标签纤维{〈x,y〉:y∈x}及其精确族；证明非空及两两不交 | 完成；行及族均从原公理取得，覆盖全部内部非空族 |
| 3d.d | 原选择集公式、实际标签族及第三个明确Replacement | SelectedPairSyntax/Fiber、SelectedGraphLogic/Choice、SelectorChoiceToGraph、ObjectSelectorGraphChoice | 精确收集每个输入的唯一被选标签对，排除原选择集杂项；完整原functionOn/choiceOn及原核AC双向蕴含/双条件 | 完成；反向五句有限背景，核心证书仅标准三项，原choice桥接可信基仍隔离 |
| 4 | 固定原核六规则及ZF/U公理识别 | Internal/ProofZF、ProofTarget、ConFormula | 完整纯ℒ公式AST；任意内部ω中的Proof/Con正确性；不得套用ZFC专用检查器 | 4a有限序列前置完成；专用检查器与Con未完成 |
| 4a.1 | 原完整functionOn、对象ω归纳及原图插入/限制 | Internal/SequenceSyntax、SequenceLogic、SequenceContext | 内部有界值序列的完整图AST；空序列及每个域内点的实际唯一有界值 | 完成；无宿主序列或外部长度限制 |
| 4a.2 | 外延/配对/并/基础及两个明确Separation实例 | Internal/SequenceAppend、SequenceExistence、SequencePrefix、ObjectSequences | 实际唯一追加、旧图精确限制、实际唯一前缀、全部内部ω长度的实际序列；八个完整原核闭句 | 完成；六句有限背景、源ZF及nativeZF实际证书 |
| 4a.3 | 任意参数纯公式行条件及上项精确边 | Internal/CheckedSequence、ObjectCheckedSequences | 每个矩阵的完整对象追加/前缀保持闭句及原核Derives；不把测试谓词作为新公理 | 完成；此通用接口不替代ZF/U专用检查器 |
| 4b | 全内部序列、自然数递归和原Gödel/结构列表约定 | Internal/NaturalArithmetic、GodelPairing、StructuralCode | 全内部数值运算实际存在唯一、编码/解码/界性质及原核Derives；紧凑quotation避免展开巨大一元数值 | 全内部递推/算术、原配数、列表唯一编解码及树结构递归检查/唯一解码完成；11构造类型检查见4c |
| 4b.a.1 | Foundation、一个序数正文Separation及对象ω归纳 | Internal/OmegaOrdinals | 每个内部ω成员满足原完整ordinal定义；有限两句背景及原核闭句 | 完成 |
| 4b.a.2 | 任意参数总单值步进关系、实际自然前驱与完整历史图 | Internal/NaturalRecursionSyntax/Total/Determinism、NaturalRecursion | 对任意有效历史实际证明算子总单值；原超限递归给实际存在唯一递归图；四个完整原核模式 | 完成；不假定历史已经符合递推 |
| 4b.a.3 | 上项真实递归图、后继域及图唯一性 | Internal/NaturalEvaluationSyntax/Existence/Uniqueness/Fiber、ObjectNaturalRecursion、NaturalRecursionLaws | 每个内部n∈ω有实际唯一末值；算子零点/后继方程和求值零点律；保留所有对象量词和公式参数 | 完成；步进公式是外部模式索引，每个实例有原核闭句 |
| 4b.a.4 | 原Pairing/Union/Extensionality的后继总单值证明 | Internal/SuccessorRecursion | 具体原后继关系消去所有算子前提，给全内部自然长度唯一后继迭代及零点求值方程 | 完成；不据此声称完整自然数加法/乘法或ω值域闭包 |
| 4b.b.1 | 通用递推、实际前段限制及ω归纳 | Internal/NaturalEvaluationRange/Step、NaturalSuccessorStep、NaturalAddition*、NaturalMultiplication*、ObjectNaturalAddition/Multiplication | 全部内部自然索引上的加乘实际自然值存在唯一、ω闭包、零点和双向后继方程、左零律；十个完整原核闭句 | 完成；见STEP4_BASIC_ARITHMETIC_ACCEPTANCE.zh-CN.md |
| 4b.b.2a | 基本加法、原后继单射、对象ω归纳与明确Separation实例 | Internal/NaturalAdditionShift/Commutative/Associative/Cancellation/Bounds、ObjectNaturalAdditionAlgebra/Order | 双向左后继、交换、双向结合、两侧抵消、两加数不降界、正加数严格成员界及和值为零刻画；九个完整原核闭句 | 完成；见STEP4_ADDITION_ALGEBRA_ACCEPTANCE.zh-CN.md |
| 4b.b.2b | 上项加法代数与基本乘法、内部ω归纳及原自然顺序 | Internal/NaturalMultiplicationAlgebra/Order、NaturalDifference | 乘法交换/结合/分配、自然次序差分及Gödel配数所需界；每项有原核闭句 | 乘法代数、自然差分/单调和平方界完成；原配数界/区间/单射见4b.c.2，全码解码待做 |
| 4b.b.2b.i | 已证加法交换/结合及实际和存在唯一 | Internal/NaturalAdditionReassociation | 用原关系Add逐见证证明四项重排/重新结合；每次中间和实际存在于ω | 完成；实际中间和、三项/四项重排原核闭句 |
| 4b.b.2b.ii | 基本乘法后继式、上项加法重排及对象ω归纳 | Internal/NaturalMultiplicationDistributive | 从Add(b,c,d)、Mul(a,b,p)、Mul(a,c,q)、Add(p,q,r)推出Mul(a,d,r)，保留全部内部自然数与见证 | 完成；双向分配闭句，见STEP4_MULTIPLICATION_ALGEBRA_ACCEPTANCE.zh-CN.md |
| 4b.b.2b.iii | 实际乘积/和及分配、加法左右后继 | Internal/NaturalMultiplicationShift/Commutative | 左参数后继乘积方程及Mul(a,b,p)↔Mul(b,a,p)，全内部ω归纳 | 完成；左后继双向式及交换闭句 |
| 4b.b.2b.iv | 已证分配与基本乘法递推、完整原核图和值 | Internal/NaturalMultiplicationAssociative | 以实际中间乘积见证给出双向结合式，所有原递归辅助证书由ZF消去 | 完成；双向结合闭句 |
| 4b.b.2b.iv.a | 实际Empty(z)、Succ(e,z)、乘法零点及后继式 | Internal/NaturalMultiplicationAlgebraLaws | 内部e作为乘法两侧单位元的双向值刻画；不固定宿主1 | 完成；两侧单位元一个完整闭句 |
| 4b.b.2b.v | 加乘半环关系律、加法抵消/基本顺序界、内部前驱分解与ω归纳 | Internal/NaturalDifference/Order | 实际自然差分、严格非零差分、加乘单调/反射及基本平方界 | 完成；原配数专门界在4b.c实际验收 |
| 4b.b.2b.v.a | 原内部序数比较、实际自然后继和值、对象ω归纳 | NaturalOrderBasic、NaturalDifferenceSyntax/Step/Positive、NaturalDifference | 全序/后继刻画；次序↔实际自然差分，严格次序↔非零差分；仅在内部ω候选内唯一 | 完成；八个闭句，见STEP4_NATURAL_ORDER_ACCEPTANCE.zh-CN.md |
| 4b.b.2b.v.b | 上项实际差分及加乘分配/抵消 | NaturalAdditionMonotone、NaturalMultiplicationPositive/Monotone/OrderLaws | 两侧加法顺序等价；零因子刻画、含零乘数弱单调及非零乘数的严格等价/反射/消去 | 完成；十三个闭句，零乘数边界保持 |
| 4b.b.2b.v.c | 实际内部空集/后继单位、上项单调与原序数传递 | NaturalArithmeticBounds、ObjectNaturalNumericBounds | 非零数至少为内部一，非零因子乘积下界，平方下界/严格单调/单射 | 完成；五个闭句，不据此声称已完成配数 |
| 4b.c | 内部算术、全部内部有限序列及原编码约定 | Internal/GodelPair*、StructuralCode | 配数/结构列表的实际内部存在唯一、解码/界与正确性；区分树数值和字节传输码 | 原配数/节点、列表唯一编解码/完整往返及树结构递归检查/唯一解码完成 |
| 4b.c.1 | 固定原配数/结构列表数值约定、全部已证自然算术关系 | Internal/GodelPairSyntax | 严格a∈b时p=b*b+a，否则p=(a*a+a)+b；实际自然中间值与纯ℒ分支AST | 完成；原多项式AST有rfl核对，实际Derives见下一行 |
| 4b.c.2 | 上项分支、实际加乘总单值、平方与顺序界 | GodelPairCore/Bounds/Intervals/Bands/BandUnique/Cancellation/Injective、ObjectGodelPair | 全内部a,b的实际唯一配数，分量界、平方区间及配数单射；七个原ZF闭句 | 完成；源ZF及原nativeZF实际Derives，见STEP4_GODEL_PAIR_ACCEPTANCE.zh-CN.md |
| 4b.c.3 | 原配数四种后继转移、对象ω归纳及输入单射性 | GodelUnpairSyntax/Arithmetic/Transitions/Step/Existence/Unique、ObjectGodelUnpair | 全内部自然码的实际唯一解码、双向精确纤维及分量界；含非标准码 | 完成；六个源ZF及原nativeZF闭句，见STEP4_GODEL_UNPAIR_ACCEPTANCE.zh-CN.md |
| 4b.c.4 | 原structural_list_code/节点后继约定及配数对象证明 | Internal/StructuralCode | 内部结构列表、节点与字段的实际编码/解码、子码界和递归正确性 | 原节点/构造器、列表长度/字段图/双向往返及树结构递归检查/唯一解码完成 |
| 4b.c.4a | 原raw_node=Succ(Pair(tag,payload))及上项全内部配数 | StructuralNodeSyntax/Existence/Properties/Core、StructuralNodeDecodeSyntax/Existence/Unique、ObjectStructuralNode | 原节点关系、全内部存在唯一、正码精确唯一分解及tag/payload严格子码界；九个源ZF与原nativeZF闭句 | 完成；见STEP4_STRUCTURAL_NODE_ACCEPTANCE.zh-CN.md |
| 4b.c.4b | 原Nil标签0、Cons标签1及节点关系 | StructuralListSyntax/Units、StructuralNil、StructuralConsAt/Core/Unique、ObjectStructuralList | 原Nil精确单位值、Cons全内部实际唯一值、互斥/输入单射、严格head/tail界及零叶封装内部二值 | 完成；九个源ZF及原nativeZF闭句，见STEP4_STRUCTURAL_LIST_CONSTRUCTORS_ACCEPTANCE.zh-CN.md |
| 4b.c.4c | 严格子码界、全部内部有限序列及相邻Cons关系 | StructuralListTrace*、StructuralListValidity/Decode*、后续TreeCode | 全内部码的有效/无效分支、有效列表/树的实际解码及递归正确性 | 内部列表轨迹、唯一编解码/往返及树结构递归检查/唯一解码完成 |
| 4b.c.4c.i | 原完整sequence图、内部长度l及其实际后继域 | StructuralListTraceSyntax/Properties | 纯公式轨迹：Nil种子、全部相邻步Cons、实际末值；Valid量化五个内部对象 | 完成；原完整函数图及全部内部长度 |
| 4b.c.4c.ii | 实际空序列、追加及精确旧边关系 | StructuralListTraceRows/Base/Append、StructuralListValidity | 实际Nil种子与Cons追加；旧相邻步逐见证迁移，新末步单独构造 | 完成；真实Derives，无宿主有限深度限制 |
| 4b.c.4c.iii | 实际前驱/前缀、Nil/Cons互斥及输入单射 | StructuralListTraceOrder/Prefix/Invert、StructuralListDecodeSyntax/Decode、ObjectStructuralListTrace | 有效码精确Nil或Cons有效尾双向式、已知Cons的有效尾反射、范围及零码排除 | 完成；十个源ZF及原nativeZF闭句，见STEP4_INTERNAL_LIST_TRACES_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.iv.a | 精确前驱长度前缀、Nil/Cons反演、严格尾码界；内部ω上的成员归纳 | StructuralListLengthSyntax/Basic/Rules/Step/Unique/Fiber、StructuralListTerminal、ObjectStructuralListLength | 任意实际长度候选相等、任意同码轨迹长度相等、每个有效码的实际唯一内部自然长度纤维 | 完成；九个源ZF及原nativeZF闭句，见STEP4_INTERNAL_LIST_LENGTH_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.iv.b.i | 原Cons输入单射性、内部空集、原自然递归 | StructuralListProjectionSyntax/Projection/Recursion、ObjectStructuralListProjection | 全内部集合上实际总单值head/tail投影；全内部自然索引唯一求值、真实递归图、零点/后继/值域规律 | 完成；11个闭句模式、head/tail共22个原nativeZF实例 |
| 4b.c.4c.iv.b.ii.a | 真实head/tail递归、内部ω归纳、精确前驱长度及严格尾码成员归纳 | StructuralListIterationTransport、StructuralListShift*、StructuralListEnd*、ObjectStructuralListEnd | 任意内部种子的一步移位双条件；实际列表长度处到达Nil，恢复原迹Nil种子；实际端点对存在唯一 | 完成；九个闭句/模式、12个原nativeZF实例 |
| 4b.c.4c.iv.b.ii.b | 原迹相邻Cons行、内部加法r+k=l、ω归纳、完整图单值性和实际自然差 | StructuralListPositionLogic/Arithmetic/Syntax/Base/Step/Induction、StructuralListPositions、ObjectStructuralListPositions | 原迹边与真实tail求值精确双条件；每个域内位置实际取得内部自然反向索引及全输出对象的双条件 | 完成；八个闭句/模式、九个原nativeZF实例 |
| 4b.c.4c.iv.b.ii.c | 真实tail/head求值、原Cons、原Replacement及Kuratowski对 | StructuralListFieldSyntax/Values/Cons/PairSyntax/Pairs/Graph*/Decode/Trace、ObjectStructuralListFields | 全内部自然字段值总单值、原Cons零/后继式；实际唯一完整有序图、全边精确式、ω值域、Valid实际长度/图解码及联合唯一性 | 完成；15个源ZF及原nativeZF完整闭句 |
| 4b.c.4c.iv.c.i | 原Nil/Cons精确长度构造、字段零/后继式、内部加法和ω归纳 | StructuralListLengthConstruct、StructuralListSuffix*、StructuralListEncodeSyntax/Graph/Existence/Readback、ObjectStructuralListEncode | 任意原完整内部ω值序列实际编码为指定长度和原字段图的原列表码；码有效，任意实际解码恢复原长度/图 | 完成；13个源ZF及原nativeZF完整闭句 |
| 4b.c.4c.iv.c.ii | 全内部实际逆编码、原Nil/Cons反演/单射、指定长度与内部ω归纳 | StructuralListCodeSyntax/Length/Fields/Step/Induction/Graph、StructuralListRoundTripSyntax/RoundTrip、ObjectStructuralListRoundTrip | 同实际长度且所有域内字段相同的列表码相等；实际唯一编码纤维；解码后重新编码恢复原码 | 完成；10个源ZF及原nativeZF完整闭句，见STEP4_INTERNAL_LIST_ROUNDTRIP_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.v | 上项唯一字段解码、有效性关系及严格子码界 | StructuralListCheck*、后续StructuralTree* | 全内部码的列表/树检查、接受/拒绝正确性与实际解码 | 列表检查及树结构递归检查/唯一解码完成；11构造类型检查见4c |
| 4b.c.4c.v.a | 原实际tail递归/移位、严格尾码界、Foundation/Separation及对象ω归纳 | StructuralListCheckSyntax/Termination*/Minimal/Unique/PreservationStep/Invariant*/Correctness、ObjectStructuralListCheck | 全内部自然码真实执行的首个Nil/空集终端存在唯一；接受↔Valid、拒绝↔¬Valid、互斥分类及接受后实际解码 | 完成；16个源ZF及原nativeZF完整闭句，见STEP4_INTERNAL_LIST_CHECK_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.v.b | 原完整字段图、严格子码界及具体前段算子 | StructuralListFieldBounds、StructuralTreeOperator*、StructuralTreeEvaluation/History/Check/Decode | 全内部树递归检查、实际存在唯一及有效/无效对应 | 完成；字段严格界、实际全序数递归图、树结构递归检查/唯一解码均有原核证书 |
| 4b.c.4c.v.b.i | 原Cons头/尾界、精确长度反演和字段零/后继规律 | StructuralListFieldBoundsSyntax/Step/FieldBounds、ObjectStructuralFieldBounds | 全部域内字段严格属于原列表码；完整图边界和父raw码界 | 完成；4个源ZF及原nativeZF闭句 |
| 4b.c.4c.v.b.ii | 上项严格子码界、真实字段图和原对象超限递归 | StructuralTreeOperatorSyntax/Logic/Step、StructuralTreeRecursors、ObjectStructuralTreeOperator | 原raw树具体二值算子仅查询严格较小子码；Total/Deterministic实际消去；全内部序数唯一完整递归图及真实零/单位标志 | 完成；10个源ZF及原nativeZF闭句，见STEP4_TREE_OPERATOR_RECURSORS_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.v.b.iii | 上项实际递归图、初段相容和严格子码界 | StructuralTreeEvaluation*/GraphValues/History、StructuralTreeRecursive*/Check/Canonical/Recursion/Decode、ObjectStructuralTreeCheck | 实际后继域/图/边的唯一求值；子码前段值一致；完整递归接受/拒绝对应与实际唯一树解码 | 完成；20个源ZF及原nativeZF闭句；所有内部码/字段，见STEP4_INTERNAL_TREE_CHECK_ACCEPTANCE.zh-CN.md |
| 4b.c.4c.vi | 实际树解码、全内部列表唯一逆编码及原raw节点 | StructuralTreeEncodeSyntax/ShapeUnique/Encode/EncodeReadback、ObjectStructuralTreeEncode | 任意内部标签及完整字段序列实际唯一树码；无有效性预设的Shape唯一；精确tag/长度/全图回读、原码恢复和构造有效性反射 | 完成；8个源ZF及原nativeZF完整闭句，见STEP4_INTERNAL_TREE_ENCODE_ACCEPTANCE.zh-CN.md |
| 4c | 上项数值编码、纯语言唯一关系编号0及无函数符号 | Internal/SyntaxCode、SyntaxTransform | 全11公式构造、bound/free长度及全部非单射替换的内部关系和正确性；不得只覆盖标准码 | 标签/字段/变量构造及纯项作用域/唯一索引解码完成；公式类型/上下文递归/替换待做 |
| 4c.a | 已证实际唯一树编解码及恢复、原SyntaxEncode标签与纯签名 | 计划Internal/SyntaxCode、TypedSyntaxOperator | 锁定term的bvar/fvar及公式0–10全构造；函数符号表空，membership编号0；精确字段数、scalar叶和bound/free长度；原核闭句 | 构造a.i及纯项作用域a.ii完成；公式类型见a.iii及4c.b |
| 4c.a.i | 真实内部数码、原Nil/Cons及raw节点 | SyntaxNumeralSyntax/Numerals、SyntaxForestSyntax/Forests/ForestLength、SyntaxNodeSyntax/Nodes/Constructors、SyntaxVariableSyntax/Variables、ObjectSyntaxConstructors | 有限标签存在唯一/顺序/互斥；精确字段数/实际长度/严格界；scalar全内部索引单射；bvar/fvar实际存在唯一/互斥；11标签/字段数构造实例 | 完成；18个源ZF/原nativeZF闭句模式，见STEP4_SYNTAX_CONSTRUCTORS_ACCEPTANCE.zh-CN.md |
| 4c.a.ii | 上项精确字段、原raw/Cons输入单射性 | SyntaxForestInjective/Arity、SyntaxNodeInjective/Arity、SyntaxVariableDecodeSyntax/Decode、SyntaxTermSyntax/Branches/Terms/Reject、ObjectSyntaxTerms | 同码字段/内部索引恢复；实际唯一解码；纯项完整scope双条件与实际构造；空/错域、错字段及任意内部payload函数标签拒绝 | 完成；27个源ZF/原nativeZF闭句模式，见STEP4_SYNTAX_TERM_SCOPE_ACCEPTANCE.zh-CN.md |
| 4c.a.iii | 纯项实际作用域检查、原11构造标签及字段数 | 计划SyntaxFormulaLocal、TypedSyntaxOperator | membership编号0必须为scalar叶；原关系/等词项类型；五个联结词及两个量词的精确类型分支；量词子式bound真实后继 | a/b局部分支完成；完整递归类型仍待4c.b |
| 4c.a.iii.a | 上项纯项scope及实际scalar/数码 | SyntaxAtomSyntax/Logic/Typing/Existence/Unique/Decode/Cases/Reject、SyntaxZeroScalar、ObjectSyntaxAtoms | 原关系唯一编号0的scalar字段；falsum/truth空分支、membership三个字段、equal两个字段；原子项在相同内部bound/free长度检查；原核证书 | 完成；25个闭句模式，见STEP4_SYNTAX_ATOM_TYPING_ACCEPTANCE.zh-CN.md |
| 4c.a.iii.b | 原精确字段及局部前段状态读取 | SyntaxContextReadSyntax/Read、SyntaxLogicalSyntax/Typing/Existence/Fields/Decode/Reject、ObjectSyntaxLogical | neg/conj/disj/imp/iff子式保持上下文；forall/exists子式bound取实际后继，free不变；全部真实子码严格界 | 完成；27个闭句模式，见STEP4_SYNTAX_LOGICAL_CONTEXT_ACCEPTANCE.zh-CN.md |
| 4c.b | 上项具体类型算子、实际内部序数递归和严格子码界 | 计划Internal/TypedSyntaxRecursion/Check | 实际构造类型状态及任意内部上下文上的总单值检查；量词体bound长度真实后继；接受/拒绝双条件及类型正确码实际解码 | 待做；不能只验外部标准quotation |
| 4c.c | 全11构造及全内部类型检查 | 计划Internal/SyntaxTransform | 全部重命名、提升、加强和非单射统一替换的实际内部图与正确性；保持捕获规避和bound/free槽位；原核推导 | 待做；步骤2的外部编译器仅作参考 |
| 4d | 七固定原ZF公理、全Separation/Collection及PP/ACwo/notAC | Internal/AxiomZF、AxiomTarget | 专用纯公式公理识别；完整模式任意参数正文；不混入ZFC选择公理 | 待做 |
| 4e | 上项完整语法、公理识别与有限序列 | Internal/ProofZF、ProofTarget | 全6原核规则及27逻辑模式；前驱索引严格更小、完整结论和上下文核验；全部内部ω码 | 待做 |
| 4f | 专用Proof关系、唯一内部ω及原矛盾句码 | Internal/ConFormula | 实际有限纯语言Con闭句，精确展开¬∃p∈ω Proof_T(p,code(⊥))；语言/原核对应 | 待做；规格文档不计实现 |
| 5 | 句法转换器及步骤2–3 | Internal/CompilerRepresentation | 代码函数的内部表示及原核推导；覆盖非标准码，不能只列外部标准实例 | 待做 |
| 6 | 原OpenAI 4.34.1环境 | 原源码定向构建、两个Comparator记录 | 分开普通Con与带不可达传递模型；真实命令与允许公理 | 待做 |
| 7 | 原生集合构造与递归 | Internal/Names、Pairs、Tuples、Recursion | 内部图与唯一性；不假定外部良基或标准ω | 待做 |
| 8 | 论文的内部解释路线 | Interpretation/Constructible、Background | 在对象ZF中逐公理证明L相对化；背景/语言/universe对应明确 | 待做 |
| 9 | 实际对称强迫系统 | Forcing/Atomic、Truth、Symmetry、ZF | 实际poset/正规滤子/HS、混合、全部ZF模式的对象证明 | 待做 |
| 10 | 单子与图式构造 | Geometry/Monoid、Placement、ConservativeHull | 核心局部存在性实际证明，不以结构字段假定结论 | 待做 |
| 11 | 模型应用 | Models/SVC、ACwo、Quotient、NotAC | 任意秩集合、同一HS模型内商双射及非选择见证 | 待做 |
| 12 | 全局装配与内部化结果 | Consistency/ObjectMain | 实际 Derives B [] (Con_ZF → Con_target)，原量词与前提不变 | 待做 |
| 13 | 最终验收 | 量词/编码/可信基/完整依赖审计 | 全build、无缺口、完整对象主句；源与目标一致性边界分开 | 待做 |

步骤编号标识工作单元，并非强制线性顺序。3b.2–3b.3提前实现步骤7中所需的
集合构造与递归；不能先声称ZF等价，再用这个未证等价循环证明Collection。

每单元交接必须记录：固定提交、允许文件、目标完整Lean类型、实际命令/退出码、
剩余义务、禁止强假设和下一最小工作。外部Consistent传输不替代对象Con推导。

第二步只实现正向传输。反向对应、ZF/U内部检查公式和完整内部化没有被偷偷列为完成。
当前原生ZF合同仍继承底座7个native_decide句子闭合证书，见TRUST_BASELINE.json；
新增第二步传输关键声明的公理审计只允许标准propext/Classical.choice/Quot.sound。

第三步边界：Presentation.theory T 是任意原理论T经回译再正向翻译的规范化呈现，
并不等于OpenAI源Replacement版ZF。Presentation.derives_iff 的两端都使用原FirstOrder.Derives；
它不是返回Source.Derives的反向编译器。源Source.Consistent量化全部变量环境，
后续反向接口必须核对源末变量规则与原free_strengthening的非空环境要求，不能默认n=0逐条对齐。
第三步验收与下一最小工作见STEP3_ACCEPTANCE.zh-CN.md。

持续目标批次：七条固定公理均已双向接入原核；ProjectSyntax覆盖任意参数矩阵的反序、重命名与闭合。
SeparationSyntax.source_separation对任意n与p : Source.Formula (n+1)返回原ZF的对象Derives；
native_separation_of_source_matrix返回同一矩阵对应的原生分离实例在源ZF句子像中的Derives。
任意原生Project矩阵的反向覆盖尚未证明；后续不得把这一受限反向接口当作完整分离模式等价。
本批验收见STEP3_SCHEMAS_ACCEPTANCE.zh-CN.md；完整内部Con主句仍为最终完成门。

全分离覆盖更新：SeparationReverse.native_separation现对任意原生Project.UnarySchema n返回原核推导，
任意原生矩阵的反向覆盖缺口已关闭。ProjectDecode展开子集原子，并证明两侧rename与参数闭合交换。
CollectionSyntax已给出任意源矩阵的原ZF收集推导，以及任意原生二元矩阵的完整回译/原核逻辑等价；
尚未从源Replacement版ZF证明Collection，也未从Collection与Separation证明源Replacement。
本批验收见STEP3_FULL_SEPARATION_ACCEPTANCE.zh-CN.md；持续目标仍为内部Con对象主句。

Replacement实质方向更新：ReplacementFromCollection.native_replacement对任意n和源矩阵p返回
原FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p))。
该证明只回放一个Collection实例和一个Separation实例，不把Replacement作为输入。
ZFReplay已覆盖源ZF九类公理及源目标理论的全部正向推导；此前“只到未对应理论像”的边界已解除。
源Replacement版ZF→原Collection实例的反向数学方向和内部Con仍待完成。反向六规则编译见后续更新。
本批实际验收见STEP3_REPLACEMENT_FORWARD_ACCEPTANCE.zh-CN.md。

反向演绎更新：ReverseCompile.certificate逐项处理全部6个原HilbertDerivation构造，
ReverseLogicalAxioms.replay逐项覆盖全部27个HilbertBaseAxiom模式，结论实际返回Source.Derives。
任意有限原核局部假设经eliminate_discharge按原核卸载顺序回放，源上下文只含回译公理及回译假设。
free_strengthening使用显式default : Fin n，因此回译环境要求n非零；没有向对象语言加入常元或非空公理。
ReverseCompile.sentence在n=1回译闭句；source_sentence_iff对任意源理论与原源闭句给出两个实际演算的往返。
这是外部有限证书变换，不包含内部非标准证明码上的表示/正确性；步骤4–5仍待做。
源Replacement证明原Collection、两种AC及最终内部Con仍未完成。
本批实际验收见STEP3_REVERSE_DERIVATION_ACCEPTANCE.zh-CN.md。

对象秩前置更新：BoundedMinimal.native_minimal与BoundedInduction.native_induction
分别对任意p : Source.Formula (n+1)返回原nativeZF内完整闭句的Derives。
源Replacement版ZF亦有source_ZF_minimal/source_ZF_induction证书；各自只用Foundation与
一个Separation实例（归纳使用反例矩阵p.neg），未使用Collection或Replacement。
它们量化一个界集合A；没有据此声称无界集合归纳、全局类极小元、外部良基或内部递归已完成。
下一最小工程为3b.2的纯对象集合图与内部ω/迭代/传递覆盖集，随后3b.3秩与累积层。
实际验收见STEP3_BOUNDED_FOUNDATION_ACCEPTANCE.zh-CN.md。

Kuratowski对象构造更新：PairSyntax.pair_original/ordered_original以rfl确认与源PP/AC
实际使用的无序对/有序对定义严格相同，没有更换编码约定。
ObjectPairs.native_exists_unique返回∀x∀y∃!p K(p,x,y)的实际原核Derives；
native_characterization返回全量词K(p,x,y)与K(q,a,b)下p=q ↔ (x=a∧y=b)的原核Derives。
源Replacement版ZF端也有对应Source.Derives；仅Pairing与Extensionality两个闭公理已足够。
全部存在见证由原exI/exE处理；无对象Choice、宿主有序对函数或外部良基前提。
3b.2尚未整体完成；图操作、内部ω与迭代/传递闭包仍是下一工作。
实际验收见STEP3_OBJECT_PAIRS_ACCEPTANCE.zh-CN.md。

对象图前置更新：GraphSyntax严格证明edge/functionOn与源PP/AC完整公式相等；
没有删去“每个图成员是定义域内的有序对”或“定义域每点有唯一输出”的任一部分。
SingletonMap.exists_map用Pairing与Extensionality实际构造域{x}和图{<x,y>}，证明完整functionOn。
ObjectGraphs的单点存在、全部边取值刻画、任意函数图边输入属于定义域、域内点存在输出及同输入输出相等
均有源Replacement版ZF证明和实际nativeZF闭句Derives；两公理理论上也有kernel_certificate。
图扩展、内部ω迭代与传递闭包仍未完成；本批不是有限迭代或Collection的最终证明。
实际验收见STEP3_OBJECT_GRAPHS_ACCEPTANCE.zh-CN.md。

新点图扩展更新：InsertExistence从Pairing与Union构造A∪{x}，Source.successor逐式相同。
ObjectGraphInsert在三个原始闭公理（Pairing/Union/Extensionality）的理论像中给出实际原核证书，
并回放到源Replacement版ZF和实际nativeZF。
对任意原functionOn(f,d)及对象x∉d、任意y，实际构造p=<x,y>、e=d∪{x}、g=f∪{p}，
证明完整原functionOn(g,e)及∀a∀b(E(g,a,b)↔(E(f,a,b)∨(a=x∧b=y)))。
相同f/d/x/y的编码、扩展域和扩展图在对象层唯一；没有抽取宿主选择函数。
不要求旧图有限，也不要求新输出y与输入或旧对象不同。
相容族合并/限制、内部ω迭代与传递闭包仍未完成。
实际验收见STEP3_GRAPH_INSERT_ACCEPTANCE.zh-CN.md。

图限制更新：RestrictionSyntax用一个完整原Separation实例实际构造
R(g,f,b) := ∀p(p∈g ↔ (p∈f ∧ ∃x∈b∃y K(p,x,y)))。
ObjectRestriction的六个闭句覆盖任意对象f/b、子域b⊆d下的完整原functionOn、
∀x∀y(E(g,x,y)↔(E(f,x,y)∧x∈b))、限制唯一性、限制到自身定义域的恒等律和子域组合律。
源Replacement版ZF及实际nativeZF都有正式推导，原核kernel_certificate只以Extensionality
和上述一个Separation实例为输入；没有使用Collection/Replacement或抽取宿主数据。
下一项为实际图定义域构造和任意内部相容图集合族合并，继而内部ω/传递覆盖。
实际验收见STEP3_GRAPH_RESTRICTION_ACCEPTANCE.zh-CN.md。

任意内部相容族合并更新：GraphDomainBound直接从原Kuratowski编码证明图输入落在∪∪G；
GraphDomainExistence用两次Union和一个完整Separation实例构造实际定义域D。
GraphFamilyExistence对任意内部集合F，在每个成员为完整函数图且逐输入相容时，
实际构造G=∪F及定义域D，证明完整原functionOn(G,D)、精确逐成员边刻画以及G/D唯一。
空族单独取得原对象闭句证书；没有添加族非空、有限或外部可数前提。
ObjectGraphFamily的六个原核闭句只以Union、Extensionality及上述一个Separation实例为输入，
源Replacement版ZF与实际nativeZF均有推导；不需要选择成员定义域或使用Collection/Replacement。
下一项为内部最小归纳集ω及对象ω归纳模式，不能以外部Lean.Nat归纳替代全部内部ω成员。
实际验收见STEP3_GRAPH_FAMILY_ACCEPTANCE.zh-CN.md。

内部ω更新：OmegaExistence从原Infinity的实际归纳集见证出发，以一个完整Separation实例
分离“属于每个归纳集合”的对象，实际构造最小归纳集ω；外延性给出唯一性。
ObjectOmega有存在、唯一及∀x(x∈ω↔x属于每个内部归纳集)的原核闭句。
OmegaInduction对任意p : Source.Formula (n+1)构造全参数闭句，并以该矩阵的一个分离实例
证明基础/后继条件推出∀x∈ω p(x)。没有用宿主Lean.Nat充当对象ω、外部标准性或外部良基。
外部n只索引有限变量数与定理模式；不是把每个外部标准n的实例当作全部内部ω结论。
下一项为ω结构与全部内部n上的唯一迭代图；ProofZF/U/Con内部化仍未完成。
实际验收见STEP3_OBJECT_OMEGA_ACCEPTANCE.zh-CN.md。

对象ω结构更新：以三个明确的分离矩阵分别实例化上轮完整ω归纳，取得
∀n∈ω(Empty(n)∨∃m∈ω Succ(n,m))、Transitive(ω)、∀n∈ω Transitive(n)。
Foundation在实际单元集上给出∀x x∉x；未使用宿主WellFounded。
ObjectOmegaStructure还给出零/后继成员闭包、非零前驱、后继消去以及
∀n∈ω∃s∈ω(Succ(s,n)∧s∉s)的完整原核闭句。给定Omega前提的结构证书
只以Extensionality、Foundation、Pairing和三个Separation实例为理论输入，未调用Collection。
下一项先补完整函数图的逐点外延性，再定义内部有限迭代图及其存在唯一；不能把后继新鲜性
或现有相容族合并单独计为内部迭代定理完成。实际验收见STEP3_OMEGA_STRUCTURE_ACCEPTANCE.zh-CN.md。

函数图逐点外延更新：保留完整entriesOn以排除图中的杂项，利用Kuratowski唯一性将
边包含转为图集合包含，边相同转为图相等。任意相容完整函数图在域包含时得到图包含，
同域时得到图相等；完整functionOn还确定实际边定义域并证明域唯一。
六条全参数闭句仅以Extensionality为理论输入，均有源ZF和原核实际Derives。
实际验收见STEP3_GRAPH_POINTWISE_ACCEPTANCE.zh-CN.md。

内部迭代的下一目标仍未完成，约定如下：给定任意内部集合a、空集z和n∈ω，
实际构造唯一图f，其域d满足Succ(d,n)、functionOn(f,d)、edge(f,z,a)，
并对域内所有j,k,u,v满足[Succ(k,j)∧edge(f,j,u)∧edge(f,k,v)→UnionOf(v,u)]。
所有n、图与中间值都在对象语言中量化，不采用外部标准有限长数组替代。
先在对象ω归纳中证明任意两份迭代轨迹在共同输入处输出一致；利用域的传递性，
从后继输入属于两个域推出前驱也属于两个域，归纳步再用UnionOf唯一性。
再以本批逐点外延性推出同一n的图唯一；存在步用新鲜后继扩展并核对全部旧/新边的递推关系。
最终用Replacement收集全部内部n的图或末值，实际合并并证明传递覆盖；这些步骤仍待实施。

给定迭代轨迹唯一性更新：IterationSyntax.track(f,d,z,a)精确展开为完整functionOn(f,d)、
edge(f,z,a)和∀j,k,u,v[Succ(k,j)→edge(f,j,u)→edge(f,k,v)→UnionOf(v,u)]。
完整functionOn已保证每条边的输入属于实际域；局部递推条件覆盖全部对象输入/输出，
没有用结构字段直接假定两个图相容或相等。四参数矩阵commonAt(f,g,d,e,x)在对象ω归纳中
给出所有内部共同索引的输出一致。传递域及d⊆ω下两图相容，同域时由完整图外延性推出相等。
ObjectIterationUniqueness有三个完整闭句及源ZF/原核Derives，理论输入仅Extensionality和一个Separation实例。
以上以前提中的实际轨迹为条件，尚未构造每个内部n的轨迹，不能把唯一性当作存在唯一性。
下一项从零长度单点图和新鲜后继扩展出发，验证完整递推条件，证明所有内部n的实际图存在；
随后装配n的后继域、相容性和唯一性，再Replacement收集并合并。实际验收见STEP3_ITERATION_UNIQUENESS_ACCEPTANCE.zh-CN.md。

全部内部有限迭代更新：FiniteIterationSyntax.witness(f,d,n,z,a)精确为Succ(d,n)∧Track(f,d,z,a)。
IterationBaseExistence由实际单点图与原存在消去构造空集索引的∃d∃f见证；
IterationExtensionAlgebra检查旧/新边的四种组合，IterationExtensionExistence先从原Union取得下一值，
再实际构造图扩展并保留全部递推条件。IterationExistence以两个种子参数的完整公式
实例化对象ω归纳，取得∀n∈ω∃d∃f witness(f,d,n,z,a)。
FiniteIterationUniqueness将后继域的传递性及包含于ω接入已有轨迹相容/图外延性，证明域与图都唯一。
ObjectFiniteIteration有基础存在、全部内部长度存在和全部域/图唯一性的原核闭句及源ZF推导。
有限八句公理理论包含Extensionality、Pairing、Union、Foundation和四个Separation实例，未调用Replacement/Collection/AC。
现在可推进Replacement收集全部内部轨迹/末值及实际合并；全族集合、全局并图与传递覆盖仍未构造。
实际验收见STEP3_FINITE_ITERATION_ACCEPTANCE.zh-CN.md；最终内部Con状态仍未完成。

精确末值集合及传递覆盖更新：IterationValueCollection先证明每个内部n有唯一实际末值，
再将唯一纤维代入原完整Replacement，实际构造c并证明∀r(r∈c↔∃n∈ω Value(n,z,a,r))。
IterationRangeSeed/Closed证明a∈c及∀r∈c∃t∈c UnionOf(t,r)；相邻长度关系由实际有限轨迹相容性取得。
TransitiveCoverLogic直接证明b=∪c包含a的全部成员且传递，TransitiveCoverExistence取得实际b。
ObjectTransitiveCover消去原ZF中实际ω与空集见证，最终得到无额外前提闭句∀a∃b(a⊆b∧Transitive(b))。
源Replacement版ZF的source_cover与原YesMetaZFC核的native_cover均已实现；源证明没有Collection输入。
IterationContext.Evidence只包装既有八句对象公理的Derives证书；没有加入新可信规则或假定覆盖结论。
下一主项为内部序数、递归、秩/累积层和反向Collection；全局ω函数图及传递覆盖的最小性亦未声称完成。
实际验收见STEP3_TRANSITIVE_COVER_ACCEPTANCE.zh-CN.md，内部ProofZF/U/Con与最终主句仍未完成。

全体集合归纳更新：SetInductionSyntax固定Below(p,x):=∀y(y∈x→p(y))、
Progressive(p):=∀x(Below(p,x)→p(x))及Holds(p):=∀x p(x)。
SetInductionLogic在实际传递覆盖中将有界成员归纳提升到全部成员归纳；再由a⊆b得到a的全部成员满足p，
应用全局进步性取得p(a)。SetInduction对每个外部p : Formula(n+1)给出全参数闭句及源ZF/原核实际推导。
GlobalMinimal以该模式作用于¬p，证明∃x p(x)→∃x(p(x)∧∀y∈x ¬p(y))；没有增加对象类或内部统一真值谓词。
外部模式索引只描述有限公式与参数数目，不是将外部标准实例当作模型内的统一真值断言。
源证明沿用Replacement版ZF中已证传递覆盖，无Collection或对象AC输入；未假定模型外部良基性。
实际验收见STEP3_SET_INDUCTION_ACCEPTANCE.zh-CN.md。下一项核对并保持原Source.ordinal的传递性、严格线性及
全内部子集极小元定义，继续内部序数比较/递归/秩；最终内部Con主句仍未完成。

原序数基础更新：OrdinalSyntax逐字保持Source.transitiveSet、membershipLinear、membershipWellFounded与ordinal，
四项对应均由rfl验证。内部良基条件量化每个内部非空子集，未替换为宿主WellFounded。
OrdinalFoundation由原Foundation正规元条件逐点推出源定义所需的成员极小元；
OrdinalRestriction证明线性/内部子集极小元条件沿子集传输，并证明原序数成员仍为原序数。
OrdinalEmpty/Successor保留全部线性条件，分别处理后继中的旧/新成员；ObjectOrdinalBasic实际构造空序数及后继序数。
七条完整原核闭句的有限理论仅含Foundation、EmptySet、Pairing、Union；未用Extensionality、Separation、Replacement、Collection或对象AC。
下一项对差性质x∈a∧x∉b应用已证全参数成员极小元，证明传递子集的初段性质，再取得任意两序数比较。
序数内部元素的线性与任意两序数比较是不同结论，后者仍待证明。实际验收见STEP3_ORDINAL_BASIC_ACCEPTANCE.zh-CN.md。

两序数比较的证明路线（现已完成，差元实际复用有界极小元）：若b传递、b⊆a且Ord(a)，按a⊆b分类；双向包含时用Extensionality。
否则对a中不属于b的性质取成员极小元u，证明u⊆b；再由a内的比较和b的传递性证明b⊆u，
外延得到b=u∈a。对任意Ord(a),Ord(b)，若a⊆b则直接用该初段结论；否则取a\b的成员极小元u，
证明u⊆b且Ord(u)，再次用初段结论；u∈b与差性质矛盾，故u=b且b∈a。
上述步骤现均已实现完整对象Derives，具体依赖收缩和验收见下述更新。

原序数比较完成更新：差性质x∈a∧x∉b有显式界a，因此直接复用BoundedMinimal，
而无需通过已证传递覆盖取得无界极小元。这使本批实际理论只有Extensionality、Foundation和一个正文x∉b的完整Separation实例。
OrdinalInitialSegment先在同一个原序数a内用其原线性条件识别传递子集的差极小元，证明b=a∨b∈a；
OrdinalComparison再处理任意Ord(a),Ord(b)，用a\b极小元u满足u⊆b并且传递，得到u=b或u∈b，后者与差性质矛盾。
OrdinalTrichotomy还在对象公式内证明相等分支排除两个成员分支、两个成员分支互斥。
六条完整闭句及有限三句理论证书、源ZF和原核回放见ObjectOrdinalComparison；无外部良基/标准性前提。
实际验收见STEP3_ORDINAL_COMPARISON_ACCEPTANCE.zh-CN.md。接着用任意内部序数族的实际Union见证，
逐点证明传递性和成员均为原序数，由任意两序数比较取得族并的线性，再由Foundation取得全内部子集极小元条件。
还须证明并是最小包含上界，随后建设内部序数递归与秩；不能用宿主Ordinal或外部族上确界替代。

任意内部序数族并与上界完成更新：OrdinalFamilySyntax将族、包含上界及对全部内部集合上界的最小性写成纯成员公式。
OrdinalFamilyOrder由原序数成员的传递性给关系传递性，再由任意两原序数比较给线性，Foundation给内部子集极小元，
因此传递的原序数集合是原序数。OrdinalUnion逐点消去原Union的实际族成员见证，证明并传递且其成员均是原序数，
并以Union取得实际并见证。UnionUpperBounds不要求族成员是序数就证明并的最小包含上界性质；外延性给最小上界唯一。
OrdinalStrictBound实际构造该并的后继，利用初段性质将每个族成员的子集关系转换为相等或成员，从而取得严格成员上界。
任意内部族包括空族；本批不假定外部有限、可数、外部良基或已给序数界。
六个完整闭句、四句/五句有限理论证书、源ZF及原核回放见ObjectOrdinalUnion和STEP3_ORDINAL_UNION_ACCEPTANCE.zh-CN.md。

下一项递归关卡保持全目标：每个外部公式Φ及任意有限参数数目产生完整对象句子，
以前提中在每个内部序数初段函数图上的总单值性，推出全部内部序数α上递归图的实际存在唯一。
递推条件必须用原完整functionOn、实际Kuratowski边及对前驱初段的实际图限制表达，不新增函数符号或把递归方程放进结构字段当假设。
先以首个差异的对象成员极小元证明共同初段相容，结合逐边外延性取得唯一性。
存在路线在对象集合归纳中：对每个β∈α已存在的唯一前段图，按算子取得下一值并实际扩展到β的后继域；
Replacement收集这些唯一扩展图，再用已证任意内部相容图族并及精确域/边规律构造α上的递归图。
此处不能把未界定的所有候选图当作集合，不能直接假定所有前段图存在或在宿主选择一族图。
后继域扩展使同一路线同时覆盖α为零、后继和极限的情形；这些递归证明尚未实现，不能由本批上界验收代替。

递归图限制与给定图相容更新：Φ的最后三槽依次为内部索引x、实际历史图h和输出y，任意外部有限参数数目保留为模式索引。
Rec(f,d)包含原完整functionOn(f,d)以及∀x∈d∀y[edge(f,x,y)→∃h(restrict(h,f,x)∧Φ(x,h,y))]。
限制到传递b⊆d时，RestrictionHistory.through把同一个实际h传到限制图g，无需重新选择历史图；
OrdinalRecursionRestriction以一个Separation实际构造g并证明Rec(g,b)。
单值性只对原Ord(x)且完整functionOn(h,x)的有效输入要求；没有要求宿主算子或假定其总性。
共同初段输出相容时，完整图外延性先给两个实际历史集合相等，再由Φ单值性给当前输出相等。
以agreementMatrix在实际域d上作对象有界成员归纳，取得任意原序数域d,e的给定递归图相容及同域唯一。
ObjectOrdinalRecursion为每个Φ给出四个全参数闭句及有限四句理论、源ZF和原核推导；实际验收见STEP3_ORDINAL_RECURSION_COMPATIBILITY_ACCEPTANCE.zh-CN.md。
本批不含全部内部序数上的递归图实际存在，不含算子总性到实际输出/扩展的证明，不以条件唯一性替代完整递归。
下一步先固定有效前段上的总性公式，用β上的实际递归图作为历史取得Φ(β,f,y)的真实输出，
再利用β∉β和原图新鲜扩展实际构造后继域图，并验证旧历史在新图中的限制关系与全部旧/新输出方程。
随后才在对象集合归纳内以Replacement收集唯一后继扩展图，实际合并并校验精确域和每个历史方程。

实际后继递归扩展完成更新：OrdinalRecursionTotal以纯对象公式要求每个有效Ord(x)/FunctionOn(h,x)输入有实际Φ输出，
没有引入宿主算子或选择函数。GraphInsertRestriction证明新鲜插入后旧图本身就是新图在旧域的精确限制。
OrdinalRecursionExtensionAlgebra在旧位置用限制复合传输同一历史；在新位置直接以旧图为历史，
用精确新值唯一性及等词替换核对每条输出边。OrdinalRecursionExtension因此保留完整functionOn和全部递推方程。
OrdinalRecursionSuccessorExistence消去实际输出、Kuratowski码、后继域、新图见证，得到保留旧域限制的实际后继扩展。
OrdinalRecursionSuccessorUnique先对两个后继域用外延性取等，再对齐递归图域并调用已证同域唯一，取得实际唯一后继图纤维。
successorMatrix的relation/unique/fiber与原Replacement接口逐式相等；尚未在本批调用Replacement收集它们。
六个模式的完整对象句子、有限五句理论证书、源ZF和原核推导见ObjectOrdinalRecursionSuccessor及STEP3_ORDINAL_RECURSION_SUCCESSOR_ACCEPTANCE.zh-CN.md。
下一项固定P(α):=Ord(α)→∃f Recursor(f,α)，在对象集合归纳进步步中对每个β∈α由归纳前提取得实际旧图，
以本批唯一后继图纤维和原Replacement收集精确图族C。每图的后继域β+1均包含于α，且每个β由其对应后继图覆盖，
所以相容图族并的实际精确域为α。还须逐输出消去族成员，证明原历史限制在全并图中仍精确，保留每个递推方程。
空α、后继α和极限α都由同一任意内部族路线覆盖；不得把外部标准α逐项检查当作全部内部序数存在定理。
此收集、合并、历史传输及全对象集合归纳装配尚未实现，最终内部Con与秩目标均未改变。

完整对象超限递归完成更新：OrdinalRecursionCollection对每个β∈α取得实际唯一后继图纤维，
以原Replacement构造精确像集合C，并逐β证明覆盖。OrdinalRecursionFamilyMembers消去每个C成员的实际β及后继域s，
证明s为原序数且s⊆α，OrdinalRecursionFamilyCompatibility从已证任意域递归图相容推出全族相容，未将相容写成结构假设。
GraphFamilyRestriction证明相容并图限制到某成员完整定义域即为该成员；OrdinalRecursionUnionFunction据精确像排除域外杂项，
据覆盖给每个内部β∈α实际输出，再由相容性得唯一，直接证明并图在精确α上完整functionOn。
OrdinalRecursionUnion消去每条输出所属的实际族成员，传输同一个历史见证并保留全部递推方程。
OrdinalRecursionExistence将此前驱步装配为P(α):=Ord(α)→RecursorExists(α)的对象全体集合归纳，
OrdinalRecursionUnique给每个内部原序数上的实际唯一图纤维。空、后继和极限域均由同一任意内部族证明覆盖。
ObjectTransfiniteRecursion有收集、并图、全存在、全唯一四个全参数闭句模式和源ZF/原核Derives；
ObjectTransfiniteRecursionIdentity实际消去Φ(x,h,y)=y=x的总性/单值性前提，提供无残留前提的全内部序数实例。
Context.Evidence仅包装五个既有原公理的Derives证书，类型/构造子/投影均审计；未包装递归存在或相容结论为假设。
实际验收见STEP3_TRANSFINITE_RECURSION_ACCEPTANCE.zh-CN.md。该收集辅助模式并非反向完整Collection公理证明。
下一项先实际构造完整图历史值的幂集像及其并，用原Replacement/PowerSet/Union给算子总单值，
再实例化本批完整递归构造实际Vα，证明层单调、传递及唯一性。秩覆盖还须以可定义序数性质的唯一最小元消除见证选择，
Replacement收集唯一界，再用实际序数族严格上界取得全族共同层界。不能先假定秩存在或预设Vα宇宙。

实际幂集并算子和递归层值完成更新：PowerSetSyntax逐字对应原PowerSet闭句，PowerSetLogic证明实际幂集唯一、相等传输及幂集单调性。
PowerValueLogic从原完整FunctionOn取得每个输入的实际输出，再由PowerSet取得实际幂集，证明唯一纤维；
PowerValueCollection用一个明确的原Replacement矩阵取得历史输出幂集的精确像集合C，不使用Collection或对象AC。
PowerUnionOperation以原Union取得y=∪C，精确像唯一与Union唯一给输出唯一。
ObjectPowerUnion在外延、幂集、并集和该Replacement实例的四句有限理论内证明对象Total/Deterministic；
HierarchyRecursion实际消去这两个前提，实例化全对象超限递归取得每个内部原序数上的唯一层序列。
HierarchyLayerSyntax以实际后继域上的递归图在α处的输出定义Layer(α,y)；HierarchyLayerExistence/Unique取得实际层值并证明不同域/图见证给同一个值。
PowerUnionEmpty/HierarchyLayerZero证明空索引的精确幂集像及其并为空，从而空索引层值为空，核对递归索引。
ObjectCumulativeHierarchy的存在、唯一、值相等和零层闭句均有源ZF/原核Derives；实际验收见STEP3_HIERARCHY_LAYERS_ACCEPTANCE.zh-CN.md。
本批尚未证明后继/极限层公式、层单调/传递或任意集合秩覆盖；实际递归层值不能代替这些后续目标。
下一步先对α上的完整递归图h证明：β∈α时，Edge(h,β,v)与Layer(β,v)严格对应；
正向需实际构造β后继及其限制递归图，反向以任意域递归图相容性和h的实际总输出相等传输。
再消去实际幂集像/并见证，取得Layer的成员递归公式，并据此推导层单调、传递和后继/极限方程。
秩覆盖仍须后续唯一最小序数模式与Replacement，最终内部Con目标未改变。

层成员递归及层代数完成更新：HierarchyHistory正向实际构造β后继域s和原Separation给出的限制图g，
验证完整Recursor(g,s)及β处原边，从而得到Layer(β,v)；反向以任意原序数域图相容和精确边传输回h。
HierarchyMemberSyntax的双存在式保留β∈α、实际层值v及z⊆v中的全部内部集合量词。
PowerUnionMembership消去实际像/并/幂集见证，证明Φ(α,h,y)的精确成员等价；反向调用原PowerSet取得实际幂集。
HierarchyMemberTransfer在成员存在式中双向替换历史输出和Layer，HierarchyMembership从实际递归历史及其限制图取得
Layer(α,y)→∀z[z∈y↔∃β∈α∃v(Layer(β,v)∧z⊆v)]。
HierarchyAlgebra对内部索引包含β⊆α证明相应层包含，证明β∈α时Vβ∈Vα，并由较早层包含得到Vα传递。
HierarchySuccessor把β∈α+1严格分成β∈α或β=α，以传递性处理旧位置、层唯一性和等词替换处理新位置，
取得后继层的原PowerOf公式。ObjectHierarchyAlgebra七个闭句均有源Replacement版ZF、句子像原核和nativeZF证书。
source_*证明没有Collection或对象AC输入；nativeZF回放仍按已记录底座证书基线审计。
实际验收见STEP3_HIERARCHY_ALGEBRA_ACCEPTANCE.zh-CN.md；该批不含极限并式或任意集合秩覆盖。
下一项对内部极限α证明Vα的成员恰来自某β∈α的实际层值，再推进可定义序数唯一最小元和秩覆盖；
不得把已证层传递性当作全体集合已经进入某层。反向完整Collection、两种AC及最终内部Con仍待实现。

极限层与序数最小元完成更新：HierarchyClosedInstances把已证层闭句实例化到任意对象上下文。
HierarchyLimitSyntax的limitIndex(α)明确表示Ord(α)且每个β∈α的实际后继仍在α中；该条件包含零，
不是只处理外部标准极限序数。HierarchyLimitMembership从实际后继及其实际层值，把z⊆Vβ转成z∈Vβ+1，
得到Vα的成员恰来自某个内部早层；反向用已证层包含单调性。
HierarchyFamilySyntax.matrix严格对应Layer(β,v)，唯一纤维严格对应layerFiber。
HierarchyLayerCollection用原Replacement实际构造全部早层的精确像C，并以Extensionality证明其唯一。
HierarchyFamilyUnion证明成员式与原UnionOf严格相接，ObjectHierarchyLimit有极限成员式、实际族存在/唯一、
给定精确族的UnionOf、实际族/并联合存在及零索引覆盖六条原核闭句。
OrdinalLeastSyntax对任意外部有限参数和任意正文p保留原参数，定义Ord(a)∧p(a)及全内部候选最小性。
OrdinalLeastLogic将对象全局成员极小元用原序数比较提升为全部内部候选中的最小元，
由序数不对称性证明唯一，并给包含界；OrdinalLeastExistence实际消去极小元见证。
ObjectOrdinalLeast为每个p提供存在、唯一纤维、最小值相等三个完整闭句模式及源ZF/原核证明。
没有新增对象类、宿主序数选择函数或内部统一真值断言；全参数模式索引属于外部接口，每个实例本身是对象证明。
验收见STEP3_LIMIT_AND_ORDINAL_LEAST_ACCEPTANCE.zh-CN.md。下一项按iv.a–iv.c在对象集合归纳内推进全体集合秩覆盖，
再处理反向完整Collection；内部ProofZF/U/Con及最终主句仍未完成。

全内部集合秩覆盖完成更新：LayerCoverSyntax以Contains(x,α):=∃v(Layer(α,v)∧x⊆v)定义包含层性质，
LayerRankSyntax以已证序数最小元模式定义最小包含层索引Rank(x,α)，并使唯一秩纤维、原Replacement关系及精确像逐式对应。
在对象集合归纳的进步步内，各y∈x已有实际层包含，从而有实际唯一秩；LayerRankCollection以原Replacement实际取得精确秩集合C并证明其成员均为原序数。
LayerRankBound对C取实际严格序数界δ和实际层值v。对每个y∈x消去其真实秩α及原Layer见证，
由α∈δ和层成员递归把y⊆Vα转成y∈v，故x⊆v，进步步得到x的真实包含层。
LayerCoverInduction用原对象全体集合归纳得到全部内部x的包含层；没有在输入假设中预设全局覆盖或内部秩。
LayerCoverMembership实际构造后继序数和其层值，以原后继PowerOf把x⊆Vα提升为x∈Vα+1。
ObjectRankCover六个闭句给全体集合包含覆盖、实际唯一秩、实际成员覆盖、成员秩精确集合、秩值相等及秩性质，均有源Replacement版ZF和原核证书。
源证明没有Collection或对象AC输入；未假定内部模型外部良基或ω标准。实际验收见STEP3_RANK_COVER_ACCEPTANCE.zh-CN.md。
下一项按3b.4.a–3b.4.c对任意原关系的见证取唯一最小秩，实际共同层给完整Collection覆盖，再接合ZF反向回放。
全局ω图及最小传递闭包仍是独立未完成辅助项，本批未将它们作为反向Collection的额外前置门。
两种AC等价、内部ProofZF/U/Con及最终内部Con蕴含的原核主句仍待实现。

完整Collection及ZF呈现互导完成更新：WitnessRankSyntax对任意原关系p及参数ρ定义
WitnessRank(x,α):=∃y(Rel_p(ρ,x,y)∧Rank(y,α))，原y仍在内部存在量词中，不要求唯一。
WitnessRankFibers从全体集合实际秩及已证最小序数模式取得唯一最小见证秩纤维；
WitnessRankCollection用一个明确原Replacement实例实际取得精确序数族C。
WitnessRankBounds对C取实际严格界δ和Layer(δ,v)，逐输入消去其最小见证秩和真实y，
用已证层成员递归取得y∈v，故满足原Collection的完整覆盖公式。
CollectionFromReplacement.source_collection对每个任意参数矩阵返回Source.Derives (ZF.at 0) (collection p)，
kernel_certificate回传原核，native_project_matrix覆盖任意原生Project.BinarySchema，未增加Collection输入或对象AC。
ReverseZFReplay逐原ZF九类公理回放，给任意自由上下文和局部假设下ZF及目标理论的双向实际原核推导；
闭句通过既有六构造/27逻辑模式反向编译器回到原19规则，保留一个未用外部变量环境。
该完成状态指对象公理逐模式互导与外部证书回放；不是任意内部Proof码的正确性，更不是内部Con主句。
实际验收见STEP3_FULL_ZF_EQUIVALENCE_ACCEPTANCE.zh-CN.md。下一项按3d.a–3d.d实现原图AC与不交族选择集AC的对象互导；
两端均固定原完整公式，不能把反向单射当满射截面或在宿主选一族内部见证。

图AC到原选择集AC正向完成更新：ChoiceSyntax严格保持原Source.choiceOn/AC及全部内部量词，
并展开原不交族选择集公式，包括逐成员唯一交点；选择集没有被额外要求包含于族并。
GraphRangeSyntax/Collection将完整functionOn的真实唯一输出纤维接到一个明确原Replacement实例，实际取得精确输出集合C。
ChoiceLogic在已知域内输入上用原valueAt取得输出唯一，无需追加Extensionality作为本步前提；
选择图的任意域内输出确实属于对应族成员。ChoiceSelectorPoints消去C成员的实际输入，
相交的不交族成员相等，转回同一输入后取得唯一输出，故C与每个族成员恰交一点。
ObjectGraphChoiceSelector给函数值域、给定选择图的选择集存在以及Source.AC→selectorAC三个闭句，
均有只含该Replacement实例的有限理论证书、源ZF和nativeZF回放；AC只作为对象蕴含前件。
ChoiceNativeBridge以decide +kernel严格核对原Axioms.choice的全AST，给原生图AC→原选择集AC的实际原核蕴含。
可信基变化单独记录：原ZF七个固定句子证书基线未改；引用原Axioms.choice激活其既有FreeClosed证书，
仅原公式桥接及原choice声明允许这第八项库证书，来源/原文件SHA见CHOICE_TRUST_BASELINE.json。
源核心三个有限理论原核证书仍仅有propext/Classical.choice/Quot.sound；没有新增对象AC公理或自定义axiom声明。
实际验收见STEP3_GRAPH_CHOICE_FORWARD_ACCEPTANCE.zh-CN.md。完整两种AC等价仍为False：下一项按3d.c–3d.d实际构造带标签不交族，
再把原选择集限制到该族实际并以构造完整选择图。内部Proof/Con及最终主句仍未完成。


AC反向及原公式等价完成更新（当前状态，取代上批的逆向待做说明）：
TaggedRowExistence先用Pairing/Extensionality和原Replacement实际取得每个x的精确标签行，并证明行唯一。
TaggedFamilyCollection用第二个原Replacement取得全部行的精确族；TaggedFamilyLogic证明该族逐项非空和两两不交。
SelectedPairFiber从原选择集及每个实际行的唯一交点推出每个输入的唯一标签对纤维，第三个原Replacement收集精确图。
此路线以精确像直接排除选择集杂项，不再要求另行构造族并并用Separation限制原选择集。
SelectedGraphLogic/Choice证明完整entriesOn、totalOn、所有输出唯一以及逐输入输出属于x，不把原选择集预设为图。
ObjectSelectorGraphChoice的有限背景仅Extensionality、Pairing和三个明确Replacement实例；AC只作为对象蕴含前件。
ChoiceNativeBridge现在给原nativeZF内两方向及原AC与原Axioms.choice的实际双条件；原choice闭性证书限域没有扩大。
本批验收见STEP3_CHOICE_EQUIVALENCE_ACCEPTANCE.zh-CN.md。下一主项为步骤4：ZF/U专用纯语言Proof/Con AST，
须核验原六规则、27逻辑模式及全Separation/Collection，随后步骤5内部表示任意内部证明码上的转换器。
内部Con主句和相对一致性最终定理仍未完成；继续以该主句作为全工程完成门。


第四步有限序列前置完成更新：内部SequenceSyntax.sequence保留完整原functionOn，另以全部内部输入/输出量词限制值域。
SequenceAppend实际取得唯一新图并记录旧图恰为旧域限制；SequencePrefix用原分离实际取得精确前缀及唯一性。
SequenceExistence在对象ω归纳中证明每个内部n∈ω有实际序列，没有改成外部Lean.Nat逐实例构造。
ObjectSequences的八个闭句有六句有限公理背景、源ZF和原nativeZF证书；Infinity不是这些条件于Omega(w)的闭句的额外输入。
CheckedSequence对任意参数纯公式给逐行条件；ObjectCheckedSequences为每个公式提供完整追加和前缀保持闭句与原核证书。
这些仅完成4a前置；完整专用ProofZF/U AST、全内部码正确性、内部编译器和Con主句仍未完成。
下一步按4b补内部自然数算术与原结构码，再按4c–4f装配原核检查；不得直接套用ZFC专用ReducedProofPresentation/PureProvability。
原IntrinsicQuotation的结构列表空码为1，叶0的树数值为2；不能与ProofCode的普通列表空码0或旧Hilbert化quotation混用。
实际验收见STEP4_INTERNAL_SEQUENCES_ACCEPTANCE.zh-CN.md。


内部自然递推前置完成更新：OmegaOrdinals以对象ω归纳证明全部内部自然数为原序数。
NaturalRecursionSyntax对任意参数关系p构造实际前驱/历史算子：有ω内前驱则读取该真实历史点并应用p；否则返回初值a。
NaturalRecursionTotal/Determinism实际证明任意有效历史上的总单值性，而非仅对已正确历史证明。
NaturalRecursion消去两项算子义务后调用已证对象超限递归，取得全内部原序数域上的真实唯一递归图。
NaturalEvaluation显式消去实际后继域、完整原递归图和末值；ObjectNaturalRecursion给每个内部n∈ω实际唯一末值的完整模式。
SuccessorRecursion实际证明原后继关系总单值，具体实例不保留外加R总性/单值性前提。
模式p仍为外部有限公式索引，每一实例覆盖全部内部索引；这不等于内部语法码或统一真值谓词已经实现。
基本加乘及ω闭包见4b.b.1，加法代数/不降界见4b.b.2a；下一步补乘法代数/次序差分/编码界，再推进原数值结构码；专用ZF/U检查器及内部Con主句未完成。
实际验收见STEP4_NATURAL_RECURSION_ACCEPTANCE.zh-CN.md。


4b.b.1更新：NaturalEvaluationRange对实际内部历史输出归纳求值范围；NaturalEvaluationStep实际限制后继图的前段，再由原唯一值定理对齐旧值。
自然后继步在ω外总化为空集，并已证明在内部自然输入上严格等于原Succ；所有步输出属于ω。
加法的递推初值为内部参数a∈ω；乘法存在量化实际Empty(e)零初值，使用已经证明的加法关系步进。
两个零见证的对齐通过原Extensionality和eqSubst完成，未固定宿主零对象。
ObjectNaturalAddition和ObjectNaturalMultiplication各有存在唯一、ω闭包、零点、双向后继和左零五个原nativeZF闭句。
中间的hAdd/hMul参数实际由先前NaturalRecursion.source_uniqueness闭句消去，不作为新背景假设。
算术代数/次序/编码界、ProofZF/U专用检查器、内部编译器及Con完成门不变。


4b.b.2a更新：加法左参数后继律、交换、结合、两侧抵消通过全部内部ω上的正式归纳证明。
结合律后继步实际取得两个旧和，右抵消后继步实际取得两个旧和并使用原后继单射；不以外部Nat归纳替代。
两加数不大于和值使用纯对象a=y∨a∈y表达；非零另一加数给实际严格成员界，和值为空精确等价于两加数为空。
ObjectNaturalAdditionAlgebra五句与ObjectNaturalAdditionOrder四句均有源ZF及原nativeZF证书。
所有分离/递归辅助参数在source_*端点从原ZF公理和已证闭句消去；内部ProofZF/U与Con仍未实现。


4b.b.2b.i–iv更新：三项/四项重排、两侧分配、左参数后继、乘法交换/结合和内部两侧单位元均已有完整原核闭句。
ZFContext只映射原ZF假设到当前上下文；ZFArithmetic通过此前已证闭句实际取得递归及算术证书。
分配后继步实际取得旧索引和、旧乘积及两旧积之和；结合后继步实际取得两个旧乘积并应用已证分配。
乘法单位元由Empty(z)及原Succ(e,z)指定，证明覆盖每个内部自然数。
加乘关系已满足半环律；尚未构造全ω二元运算图，也未完成自然次序差分、编码界或ProofZF/U。
下一项为4b.b.2b.v，再推进原Gödel配数和结构列表码。实际验收见STEP4_MULTIPLICATION_ALGEBRA_ACCEPTANCE.zh-CN.md。


4b.b.2b.v更新：自然差分在内部上界作ω归纳，逐后继实际取得自然差值及其原后继。
差值唯一性公式显式要求每个比较候选属于内部ω，不声称ω外索引也唯一。
严格次序以实际非零差分表达；加法保持和反映两侧严格/非严格顺序。
乘法弱单调包含公共乘数为零的情况，严格等价、反射和消去均显式要求非零公共乘数。
非零乘积经实际内部前驱/旧积证明；零因子、内部一的下界及平方基础界均有原核闭句。
二十六个新闭句见STEP4_NATURAL_ORDER_ACCEPTANCE.zh-CN.md；当前主项为4b.c原配数与结构码。
原InternalPairingRules只用于核对平方分支约定；本工程未调用其ZFC模型语义作为对象ZF证明。


2026-10-22原配数批次：4b.c.1–4b.c.2已完成，实际构造两个分支的全部自然中间值，
证明自然值总单值、分量界、平方区间和完整输入单射性。七个完整闭句均有源ZF和原nativeZF证书。
未导入原InternalPairingRules的ZFC模型语义证明；背景、原核和内部Con规格没有改变。
当前主项转到4b.c.3：全内部自然码的实际解码存在，再由已证输入单射性得到唯一性。
不能只计算外部标准码的平方根，也不能把存在编码值误当成每个内部码均可解码。
验收见STEP4_GODEL_PAIR_ACCEPTANCE.zh-CN.md；之后才是结构列表/树、全11构造语法和专用ProofZF/U。


2026-10-22全内部解码批次：4b.c.3已完成。对象编码值上的ω归纳实际处理零点和四种原多项式后继转移，
得到每个内部自然码的实际自然分量。原配数单射性给出双向精确纤维及有界唯一解码。
六个完整闭句均有源ZF及原nativeZF证书；不是宿主sqrt或标准码枚举。
当前主项转为4b.c.4a，再推进4b.c.4b–c、全部11构造语法及专用ProofZF/U。
验收见STEP4_GODEL_UNPAIR_ACCEPTANCE.zh-CN.md。结构码、检查器、内部编译器和最终Con仍未完成。


2026-10-22原始节点批次：4b.c.4a已完成。原raw_node严格保留实际后继配数定义，
全内部自然标签/载荷有实际唯一正编码值，两个分量严格属于节点码。
每个正内部自然码有实际唯一标签/载荷分解，且保留双向精确纤维和严格子码界；零码无分解。
九个完整闭句均有源ZF及原nativeZF证书，见STEP4_STRUCTURAL_NODE_ACCEPTANCE.zh-CN.md。
这尚未检查有效标签、字段或列表/树形。下一主项4b.c.4b按原0/1标签构造Nil/Cons，
之后4b.c.4c验证全部内部码的有效/无效分支，再推进完整语法、专用ProofZF/U与最终Con。


2026-10-22原Nil/Cons构造器批次：4b.c.4b已完成。原Nil精确等于实际内部单位，
全部内部自然head/tail有实际唯一Cons值；Cons输入单射、与Nil互斥且head/tail严格属于编码值。
实际零/单位及单位后继还给出Nil字段列和零叶raw封装的内部1/2值。
九个完整闭句均有源ZF及原nativeZF证书，见STEP4_STRUCTURAL_LIST_CONSTRUCTORS_ACCEPTANCE.zh-CN.md。
当前主项4b.c.4c先定义实际内部有限轨迹，再证明Nil种子、Cons追加、前缀反演与实际唯一字段解码。
既有SequenceAppend/Prefix只提供图及精确旧边；相邻递推保持需要新对象证明，不能省去。
递归列表/树有效性、专用ProofZF/U和最终Con仍未完成。


2026-10-22内部列表轨迹批次：4b.c.4c.i–iii已完成。Valid为实际内部有限序列轨迹的五重存在纯公式，
长度l∈w、域Succ(l)、完整functionOn与ω有界值、Nil种子和全部相邻Cons步均保持对象量词。
实际Nil轨迹、Cons追加与前缀限制给出Valid↔Nil∨存在有效尾及自然head的原Cons关系，
已知自然Cons值的有效性当且仅当尾有效；零码被对象推导排除。
十个完整闭句均有源ZF及原nativeZF证书，见STEP4_INTERNAL_LIST_TRACES_ACCEPTANCE.zh-CN.md。
上述为轨迹批次结束时的计划；精确前缀和长度唯一性现已按下述批次完成。
完整字段解码、树、专用ProofZF/U与最终Con仍未完成；不能把当前一步分解当成完整解码。


2026-10-22内部长度批次：4b.c.4c.iv.a已完成。hasLength保留四个实际内部迹见证，
exists_prefix_trace保留给定前驱长度p和实际域l，而非只返回Valid。已知Cons的尾等于实际前驱图值。
Nil的每条实际迹长度为空；Cons的每条实际迹长度为尾的某个实际长度的后继。
唯一性使用内部w上的成员归纳：对码n假设所有t∈w∩n的长度唯一；Cons严格尾码界给t∈n。
两条迹任意不同的零、Nil种子、域和图仍有相同长度；候选长度无外部标准性限制。
此路线取代旧计划中的长度归纳，直接使用已证严格子码界及原Foundation/Separation。
九个完整闭句均有原核Derives。完整验收438任务、3676审计、0警告、407份哈希差异0。
下一主项4b.c.4c.iv.b先证明原Cons的head/tail投影在全部内部集合上总单值，非Cons输入取实际空集，
再用已证自然递归从完整码向尾递推，按原字段顺序取得实际图。此路线避免先反转构造迹，
仍须实际证明与迹的逐步对应、在唯一长度处止于Nil和由Replacement取得完整字段图。
这些字段图、往返、树、专用ProofZF/U与最终Con尚未完成。


2026-10-22内部投影批次：4b.c.4c.iv.b.i完成。外部Bool仅选择head/tail两个纯公式模式。
Selected_h(w,x,y)存在自然分量a，原Cons分量顺序按模式选择；Step_h为该关系或无Cons时的Empty(y)。
已证所有内部集合输入的实际总性、单值性、ω值域、已知Cons的精确分量和Nil/非Cons的空值。
原自然递归的总性/单值性前提均已消去，获得实际唯一递归图及全内部自然索引的实际唯一求值。
零点返回原种子；后继求值满足原Step_h；自然种子下全部值属于ω。
11个完整闭句模式均有源ZF、sourceZF原核核心与原nativeZF证书，CheckStep4逐一检查两个方向共22实例。
完整验收442任务、3762审计、0警告、411份源码哈希差异0；Internal具名覆盖1447项。
下一主项4b.c.4c.iv.b.ii仍须证明尾递推与原构造迹逐步对应、终止点和实际完整字段图。
完整字段图/往返、树、专用ProofZF/U与最终内部Con仍未完成。


2026-10-22内部移位与Nil终端批次：4b.c.4c.iv.b.ii.a完成。Step_h(w,a,b)下，
对象ω归纳证明两条真实迭代在同一内部自然索引r上的输出u,v满足Step_h(w,u,v)。
因此r∈w、Succ(s,r)下，Iteration_h(w,a,s,y)与Iteration_h(w,b,r,y)有实际双向推导。
种子a,b可以是任意内部集合；不存在外部标准长度限制。
Cons尾的实际前驱长度与移位相接，再沿原严格尾码作内部成员归纳，
证明HasLength(w,n,l)及Iteration_tail(w,n,l,y)推出Nil(w,y)。
任意完整Trace(w,z,e,l,d,f,n)实际给Iteration_tail(w,n,l,e)，并使任意同位置真实求值等于e。
有效码有实际长度/求值/Nil端点见证；所有长度/求值端点对相等。
本批11模块86声明、九个闭句/模式和12个nativeZF实例全部验收：453任务、3848审计、0警告、422哈希差异0。
下一关用加法反向索引r+k=l及原相邻Cons行，对全部内部自然r作ω归纳，
逐位置对齐真实tail求值与原迹，而后由原Replacement构造完整有序head字段图。
端点恢复不替代全部位置对应，完整字段图、往返、树、专用ProofZF/U和最终Con均未完成。


2026-10-22全部位置批次：4b.c.4c.iv.b.ii.b完成。内部r+k=l下，原边edge(f,k,y)
与Iteration_tail(w,n,r,y)精确双向对应，且对所有输出对象y成立。
原Separation支持的ω归纳对全部内部r进行；零点由加法零律和末边单值性对齐，
后继步实际取得原迹相邻Cons行、真实加法前驱和下一个递归值，保持全部对象见证。
原完整函数图为反向方向实际取得k处的值，真实递归单值性给边值等词替换。
给任意k∈d，内部自然差实际构造r∈w、r+k=l和∀y(edge(f,k,y)↔Iteration_tail(w,n,r,y))，
不是把差存在性或仅外部标准位置留作前提。八个完整闭句/模式、九个原nativeZF实例已验收。
实际验收461任务、3916审计、0警告、430哈希差异0，Internal具名覆盖1601项。
下一主项ii.c定义Field(w,n,i,y):=∃t(Iteration_tail(w,n,i,t)∧Step_head(w,t,y))，
证明全内部自然i的实际总单值、Cons零/后继关系，再以原Replacement收集全部实际Kuratowski索引对。
利用精确像证明完整functionOn、无多余图元的全边式、ω值域与唯一性，然后接原顺序往返。
现有逐位置对应不替代实际字段图；字段图、往返、树、专用ProofZF/U与最终Con仍未完成。


2026-10-22实际完整字段图批次：4b.c.4c.iv.b.ii.c完成。Field为实际tail值后取head的内部存在关系，
在全部内部自然索引实际总单值，所有输出属于ω；原Cons的零点和后继递归式有精确双条件。
原Replacement收集实际Kuratowski索引对的精确像；原完整functionOn、ω值域、全边精确式及图唯一性均已证。
Valid(w,n)实际解码为内部长度和完整字段图；反向有效性及长度/图联合唯一性也有原核闭句。
原迹中给定Cons的实际head与相应字段读取直接对应。
15个完整闭句已验收：474任务、4057审计、0警告、443哈希差异0，Internal具名覆盖1742项。
下一项iv.c.i先补原Cons在指定后继长度上的HasLength构造，再固定原序列F及总长L，
对全部内部后缀长度r作ω归纳，性质量化所有偏移k且r+k=L，实际构造长度r的后缀码，
其第i字段对齐F在k+i位置的实际值。零点用Nil，后继用原Cons与已证字段零/后继双条件。
此路线保持F,L不变，以标量字段关系为不变量，避免把末尾追加误当作原Cons前置。
最后k=0、r=L给完整逆编码，再证同长度/同字段列表码唯一及双向往返。
任意序列逆编码、完整往返、树、专用ProofZF/U和最终内部Con仍未完成，相关标志保持False。


2026-10-22任意内部序列逆编码批次：4b.c.4c.iv.c.i完成。原Nil有给定实际零长度，
原Cons把尾的实际长度r构造为指定实际后继s；未仅给有效性。
固定原序列F和总长L，矩阵对全部内部r归纳，量化所有k∈w且r+k=L。
每个后缀实际取得自然码n、HasLength(w,n,r)和全部域内字段在源偏移k+i处的精确双条件。
后继步实际取得下一偏移、旧码、源head和新原Cons码；全部见证在对象存在消去内处理。
零偏移、全长度实例得到实际完整序列的原列表编码；原functionOn排除杂项，解码精确图像恰等于给定F。
编码所得码有效，任意实际解码恢复原长度L和原图F。13个闭句验收486任务、4159审计、0警告、455哈希差异0。
下一项iv.c.ii的矩阵比较任意n,m：同实际长度r，且∀i∈r∀y(Field(w,n,i,y)↔Field(w,m,i,y))时n=m。
对象ω归纳零点由实际零长度反演Nil；后继点反演两个Cons，用内部零字段对齐head、后继字段对齐tails，
尾的实际前驱长度由原内部后继单射性对齐，再用归纳假设及Cons输出唯一性取得原码相等。
随后由实际编码存在性取得唯一编码纤维和解码后重新编码的原码恢复。
本批未证明该码单射或完整双向往返；树、专用ProofZF/U和最终内部Con仍未完成。


2026-10-22原码单射及往返批次：4b.c.4c.iv.c.ii完成。对象ω归纳比较任意同实际长度的原码，
全部域内索引、任意输出对象的字段双条件推出原码相等。后继反演保留给定尾长度，
实际零/后继字段对齐头尾后，由前驱归纳假设和原Cons输出唯一性完成。
实际唯一编码纤维及每个有效码的长度、完整字段图、重编码值三重见证均已正式取得，重编码值等于原码。
结合已验收编码后图读回，完整双向往返完成。十个完整闭句有原nativeZF推导。
本批495任务、4243审计、0警告、464哈希差异0；见STEP4_INTERNAL_LIST_ROUNDTRIP_ACCEPTANCE.zh-CN.md。
下一主项4b.c.4c.v先构造实际递归列表检查轨迹并证明总单值和接受/拒绝对应，再接入树字段有效性。
专用ProofZF/U、任意内部证明码正确性及最终内部Con仍为False；背景与最终对象Derives规格保持不变。


2026-10-22全内部递归列表检查批次：4b.c.4c.v.a完成。检查使用真实tail递归的首个原Nil或空集终端，
定义不含Valid判定。严格尾码上的对象成员归纳证明实际终止，原Foundation/Separation取得首个索引。
任意两组首次停止索引及值均相等；对象ω归纳关闭停止前的原Valid保持/反射性质。
故全内部自然码接受当且仅当Valid、拒绝当且仅当其否定，分类完整互斥；原Nil/零边界及接受后实际解码均已证明。
16个原nativeZF完整闭句；全仓506任务、4397审计、0警告、475哈希差异0。
下一项v.b先证明全部域内字段值严格属于原列表码，再组合raw_node载荷界，推进树递归有效性/解码。
树、专用ProofZF/U和最终内部Con仍未完成；不得把列表接受结果升级为树有效性。


2026-10-22字段严格界及树算子实际递归批次：v.b.i–ii完成。
对象ω长度归纳覆盖全部内部字段；完整图边及raw载荷严格界组合为父码下的全部子字段界。
具体树Good实际取得标签/载荷/长度/完整字段图，H查询带严格子码界，并已在Shape下证明等价于原Marks。
算子总单值义务已实际消去，原对象超限递归给全部内部序数上的唯一完整图，Ω还取得真实零/单位标志。
四个字段及十个树闭句有原nativeZF推导；全仓515任务、4511审计、0警告、484哈希差异0。
下一项v.b.iii实际构造自然码的唯一求值，证明前段子码值一致及Good的完整递归刻画，完成树检查/解码。
当前完整树接受/拒绝、专用ProofZF/U及最终内部Con仍未完成；背景及对象Derives规格不变。

2026-10-22全部内部树检查/解码批次：4b.c.4c.v.b.iii完成。
真实后继域和完整图给出所有内部序数上的唯一求值；任意原序数前段边与该求值双向对应。
真实历史将Good精确化为Shape及每个实际字段的递归接受；实际零/单位下接受、拒绝和互斥分类均证明。
Valid/Invalid消去标志参数但保留自然守卫和实际见证；不同实际标志选择经对象等词对齐。
原核证明Recursive↔Valid及DecodedFiber↔Valid，覆盖任意内部候选对象；节点四个实际分量联合唯一。
14个新模块196项显式声明；20个完整闭句的source、sourceZF核及nativeZF核证书均通过。
全仓529任务、4707审计、0警告、498哈希差异0，累计219对核心/native证书精确核验。
验收见STEP4_INTERNAL_TREE_CHECK_ACCEPTANCE.zh-CN.md。下一主项4c.a–c仍须全部11构造、内部作用域及非单射替换。
通用结构树检查不能代替类型检查；ProofZF/U、内部编译器和最终对象Con主句仍未完成。

2026-10-22实际树构造/字段恢复批次：4b.c.4c.vi完成。
任意内部自然tag、长度及完整ω值序列实际取得唯一原树码；存在性先构造真实列表payload，再构造原raw节点。
同一原码的Shape四分量唯一不假定子树有效；任意实际解码恢复原tag、长度及完整原输入图。
解码后按同tag/长度/字段图重新构造所得码等于原码；构造有效性等价于全部输入字段Valid。
5个新模块60项声明；8个完整源ZF及原nativeZF闭句。全仓534任务、4767审计、0警告、503哈希差异0。
累计227对核心/native精确依赖通过；验收见STEP4_INTERNAL_TREE_ENCODE_ACCEPTANCE.zh-CN.md。
下一项4c.a保持全部11种原生公式构造、纯签名符号表及内部索引/作用域边界；尚未实现类型检查或ProofZF/U。

2026-10-22有限语法标签/字段/变量构造批次：4c.a.i完成。
数码是有限公式模式，候选标签/字段值为对象量词；scalar和bvar/fvar的索引覆盖全部内部自然数。
精确向量森林实际存在唯一并有真实数码长度；原节点/有限标签构造器实际存在唯一、异标签互斥及严格子码界。
scalar索引单射已证明；原bvar/fvar编码的存在唯一和两类互斥已证明，反向变量索引单射仍待完成。
11个新模块149项显式声明，18个完整源ZF/原nativeZF闭句模式及全部11标签/字段数构造实例通过。
全仓545任务、4916审计、0警告、514哈希差异0，累计245对核心/native精确足迹通过。
见STEP4_SYNTAX_CONSTRUCTORS_ACCEPTANCE.zh-CN.md。下一项4c.a.ii，再装配4c.a.iii和4c.b的全内部上下文类型状态。
量词体所需bound后继随节点变化；固定原始bound参数的单个二值树递归不能直接给完整类型检查。
可用实际P(P(ω))覆盖Kuratowski上下文对，按原Separation构造局部类型状态，再以原序数递归构造真实状态图；
该路线的集合覆盖、总单值性、全部前段对应及量词分支均仍须对象推导，尚未实现。
ProofZF/U、内部替换/编译器及最终Con目标不变，完成状态保持False。

2026-10-22反向变量解码及纯项作用域批次：4c.a.ii完成。
同码森林/节点/构造器反向恢复字段；不同有限字段数由实际数码长度及原长度唯一性排除。
同码变量索引相等、实际唯一索引纤维及识别双条件均有原核证书；候选索引遍历全部内部集合。
Term保留两个内部自然上下文长度和严格索引成员关系；已知变量码的Term↔Scope及合法索引实际项码构造完成。
实际唯一解码的bound/free分支互斥；空/错域、裸scalar和错字段数被排除。
函数标签2还有任意内部自然payload的完整拒绝句，覆盖内部非标准长度，不依赖固定外部字段向量。
11个新模块188项声明、27个闭句模式；全仓556任务、5104审计、0警告、525哈希差异0，累计272对精确足迹。
验收见STEP4_SYNTAX_TERM_SCOPE_ACCEPTANCE.zh-CN.md。下一项4c.a.iii.a固定membership编号0及原子式/等词局部项类型，
再做所有联结词和真实后继bound的量词局部分支；全部公式类型、上下文状态递归、替换、ProofZF/U及Con仍未完成。
任意内部未知标签的拒绝句也已证明：t∈ω、¬Num_0(t)、¬Num_1(t)下，任意自然payload的raw节点均非纯项；无外部标签数值上限。

2026-10-22原子局部类型与实际唯一解码批次：4c.a.iii.a完成。
10个模块200项显式声明；25个完整原核闭句模式；566任务、5304审计、0警告、535哈希差异0。
累计297对核心/native精确足迹通过；详见STEP4_SYNTAX_ATOM_TYPING_ACCEPTANCE.zh-CN.md。
关系编号0实际检查为原scalar叶，树值恰为内部2；两个项保持相同完整bound/free上下文。
合法输入实际构造自然码；同输入唯一、同码字段恢复和真实内部量词唯一解码双条件均已证明。
未知内部标签t的拒绝不使用外部标签界或外部字段长度界。

| 后续工作单元 | 实现输入与交付 | 对象层验收条件 | 当前状态 |
|---|---|---|---|
| 4c.a.iii.b.1 | neg/conj/disj/imp/iff的精确原字段AST与前段类型状态读取 | 全部子码严格界；同一(b,f)读取；字段数/标签和解码唯一性 | 本批完成 |
| 4c.a.iii.b.2 | forall/exists的原单字段及实际后继bound见证 | Succ(b',b)，读取(b',f)；free不变；禁止将原b直接传给量词体 | 本批完成 |
| 4c.b.1a | 实际构造三层幂集A/C/U及Kuratowski上下文对 | 三层幂集真实存在唯一；上下文对属于C；任意状态子集属于U | 本批完成；6个闭句模式 |
| 4c.b.1b | 组合11个局部判据，在实际C上Separation构造状态 | 排除非上下文对杂项；每对成员精确双条件；实际状态唯一且属于U | 完成；实际唯一状态及逐对成员双条件 |
| 4c.b.2 | 原子/逻辑/量词组合的上下文集合值算子 | 实际有效历史上的总单值性，含非自然输入默认值；不以宿主递归给状态 | 完成；总单值前提已实际消去 |
| 4c.b.3a | 实例化原递归并构造每个内部自然码状态值 | 完整图/真实后继域存在唯一；值属于实际载体 | 完成 |
| 4c.b.3b | 全部原序数前段图边、真实历史与Typed判断 | 边↔实际值；完整前段状态方程；自然子码Read↔Typed | 完成 |
| 4c.b.3c | 不含历史参数的11构造递归类型判据 | 原核Typed双条件；严格子码查询；量词体真实后继bound | 完成；全候选Typed双条件及实际系统存在 |
| 4c.b.3d.1 | 实际ω/载体唯一性及Typed参数传输 | FormulaCode与任意真实载体上的Typed等价；无额外载体前提的全候选递归式 | 完成；原核证书，不声称公式复杂度为Σ类 |
| 4c.b.3d.2 | 原11构造及全内部字段 | 已知原码的精确类型分支；合法输入实际构造；字段恢复及错码排除 | 精确类型、实际唯一带类型构造、完整根字段/往返及标签/字段数分类完成；递归TypedData分类待做 |
| 4c.b.3d.3 | 原纯签名编码与全部内部候选码 | 完整识别/构造正确性；保留非标准内部ω与真实量词scope，不只跑标准样本 | 待做 |
| 4c.c | 任意内部非单射rename/替换图与捕获规避 | 全部内部码及真实上下文下对象推导；不只检查标准宿主证书 | 待做 |

原子局部门禁通过不改变完整11公式类型/上下文递归/替换/ProofZF/U/内部Con的False状态。

2026-10-22逻辑局部分支与实际上下文载体批次：
4c.a.iii.b完成；Read查询实际历史的集合值，量词体明确在真实Succ(k,b)下查询(k,f)。
七种分支有精确原码类型双条件、实际码构造、严格子码界、唯一解码和所需状态缺失的拒绝。
4c.b.1a同时完成：三层幂集真实存在唯一；全部内部上下文对和状态子集有实际统一载体。
12个模块231项显式声明，33个新增完整闭句模式；578任务、5535审计、0警告、547哈希差异0。
累计330对核心/native精确足迹；见STEP4_SYNTAX_LOGICAL_CONTEXT_ACCEPTANCE.zh-CN.md。

下一项4c.b.1b先组合原子和七种逻辑分支，再对载体C上的上下文对执行实际Separation。
局部判据只读取严格较小子码的前段状态；量词体通过实际后继bound变化，不能固定初始上下文。
状态必须排除非上下文对杂项，保留两侧自然守卫，证明逐对成员双条件及属于U。
之后证明算子实际总单值性并实例化原对象递归，核验全部前段读取和11构造完整递归类型式。
未构造该状态/算子/递归图；完整类型、内部替换、ProofZF/U及最终Con完成门禁仍False。

2026-10-22实际Separation类型状态与原集合值递归批次：
4c.b.1b、4c.b.2、4c.b.3a–b完成。Local已组合全部11构造，真实状态总单值且排除杂项。
全部内部原序数域上有实际唯一完整递归图；内部自然码有实际唯一后继域状态值。
任意更长图边与该实际值双向对应，真实前段递归图满足当前State方程。
Typed为带根自然码/两侧上下文守卫的纯对象公式；实际值成员及自然域内Read均有精确对应。
17个模块243项显式声明；35个新增完整闭句模式；595任务、5778审计、0警告、564哈希差异0。
累计365对核心/native精确足迹；见STEP4_ACTUAL_TYPE_STATES_ACCEPTANCE.zh-CN.md。

下一项4c.b.3c定义不含历史h的11构造递归判据，在严格子码处用Read↔Typed逐分支迁移。
先保留真实原构造及全部字段，逐一证明否定/二元联结词与量词的实际类型双条件；
量词体在真实Succ(k,b)下读取(k,f)，不得将父式b原样传入。
4c.b.3d再核查原编码识别、构造及拒绝，不以当前状态递归存在直接替代完整正确性。
实际状态递归存在已完成；原完整11类型正确性/替换/ProofZF/U及Con门禁仍False。

2026-10-22全11历史无关类型递归与实际系统批次：
4c.b.3c完成。严格子码的所有Read/Advanced已逐字段迁移为Typed，两个量词覆盖全部真实后继见证。
原核对所有内部候选n,b,f证明Typed↔Criterion，包括根非自然分支；不是只检查标准码。
还实际构造ω、三层载体、完整状态递归及全称定律，给出无额外存在前提的闭句存在证书。
9模块96项显式声明；12个新增原核闭句模式；604任务、5874审计、0警告、573哈希差异0。
累计377对核心/native精确足迹；见STEP4_HISTORY_FREE_TYPE_RECURSION_ACCEPTANCE.zh-CN.md。
object_bound_free_context_type_recursion_proved现True；完整原编码类型识别关卡仍False。

下一主项4c.b.3d.1用已证载体/ω唯一性处理Typed参数传输，定义无额外载体参数的内部FormulaCode。
再完成每个原构造的精确类型分支、合法内部输入实际码构造、字段恢复和错误标签/字段/作用域拒绝。
原编码识别正确性必须覆盖全内部候选，而非仅宿主SyntaxEncode的外部标准样本。
之后4c.c保持任意内部非单射rename与捕获规避替换；ProofZF/U和最终Con目标不变。

2026-10-22无额外载体FormulaCode批次：
4c.b.3d.1完成；FormulaCode(w,n,b,f):=∃A∃C(Power(A,w)∧Power(C,A)∧Typed(w,C,n,b,f))。
实际载体唯一性和对象等词传输给出任意实际C上的精确等价，实际ω见证也可对象等词替换。
真实二层幂集存在消去载体前提；原核在Ω(w)下对全候选n,b,f证明FormulaCode↔CodeCriterion，
并证明其三重全称定律。该关系只是有限纯成员公式缩写，不主张未证明的Σ复杂度分类。

4c.b.3d.2已知码部分也已完成：全11原构造的精确FormulaCode类型双条件，
保留全部原字段、完整bound/free作用域和量词体真实后继；不同标签分支由原构造不交性排除。
未知标签拒绝量化任意内部t,p,n；t∈ω且排除内部0至10数码时，任意自然payload原raw节点都不是FormulaCode。
该拒绝不限制payload的外部长度或t的外部数值；全部候选仍包含非标准内部自然。

| 紧接工作单元 | 输入/实现 | 对象层验收 | 状态 |
|---|---|---|---|
| 4c.b.3d.2a | 全11已知码类型双条件、原实际构造纤维 | 对所有合法内部子码实际取得n，保留原Constructor、FormulaCode和对所有候选的唯一性 | 完成；membership实际构造编号0符号，无额外符号存在前提 |
| 4c.b.3d.2b | 原完整字段恢复、实际长度及同码唯一性 | 已接受FormulaCode的实际唯一标签/payload/完整字段图；重编码恢复原根码并保留类型 | 根数据、逐位置类型传输及正向TypedData完成；反向识别待做 |
| 4c.b.3d.2c | 标签、实际字段数和内部上下文守卫 | 完整错字段数/符号/作用域排除及可接受/拒绝分类 | 全内部标签/字段数配对分类及非匹配Shape拒绝完成；完整递归操作数/作用域分类待装配 |
| 4c.b.3d.3 | 以上全部对象证书 | 原编码完整识别/构造正确性，覆盖全部内部候选；再允许提升总关卡 | 待做 |
| 4c.c | 内部rename/捕获规避替换图 | 任意内部非单射映射/所有上下文的完整原核对象推导 | 待做 |

本批不提升object_all_eleven_formula_constructors_type_check_proved；
内部替换、ProofZF/U、全内部证明码正确性和最终Con蕴含仍未完成。
新增16模块216项显式声明、29个完整Source/sourceZF核/nativeZF核闭句模式。
实际机器验收和当前哈希数量见STEP4_FORMULA_CODE_CARRIER_ACCEPTANCE.zh-CN.md；
旧批次数字为历史记录，不作为当前运行证据。

2026-10-22实际带类型构造与接受根字段批次：
4c.b.3d.2a完成。typedFiber实际存在n∈ω、原精确Constructor和FormulaCode，
且任意原Constructor候选都等于n；不只声明合法输入下的条件双条件。
全部11原构造的类型定律均实际消去，输入只保留原完整合法类型条件。
membership从两个Term输入实际构造原zeroScalar符号及带类型码；不要求用户另给符号码存在前提。

接受码实际取得唯一tag/payload/内部长度/完整有序字段图。
Shape包含真实HasLength、完整functionOn/range/全边精确式；不是截取有限外部字段样本。
原n自身实际满足解码字段的Encoding；任意同字段重编码都等于n并保留FormulaCode。
原构造的任意内部长度候选恰满足对应实际数码，接受根的标签/长度必须属于原11个精确配对。
配对(标签,字段数)是(0,0)、(1,0)、(2,3)、(3,2)、(4,1)、(5,2)、(6,2)、(7,2)、(8,2)、(9,1)、(10,1)。
任意不满足该内部配对式的真实Shape均正式拒绝；长度候选没有外部标准性前提。

| 下一工作单元 | 负责实现的具体模块/接口 | 必须验收的对象结论 |
|---|---|---|
| 4c.b.3d.2b.i（完成） | SyntaxForestFields / SyntaxNodeFields / FormulaCodeTypedFields / FormulaCodeGraphTyping | 全内部i,y图边双条件、实际槽位及四类对象类型检查精确传输均已证明；已知原构造的父类型等价于实际字段图检查 |
| 4c.b.3d.2b.ii | FormulaCodeTreeValidity：类型码/纯项码到原StructuralTree.valid | 对全部内部n及所有bound/free上下文作对象成员归纳；含真实后继作用域；禁止宿主WellFounded替代 |
| 4c.b.3d.2c.i | FormulaCodeTypedDecode：原11标签下的内部完整字段类型分类 | 接受码实际唯一解码为完整TypedData；反向由完整数据回到FormulaCode；符号/项/递归操作数/作用域错误全部排除 |
| 4c.b.3d.3 | 汇总完整识别/构造正确性及原核闭句证书 | 上三项连同已完成构造/根字段证书实际通过后，才提升完整类型识别总关卡 |
| 4c.c | 任意内部rename图和捕获规避替换图 | 对象层全码/全上下文的原推导；不能用现有宿主语法重命名等式代替 |
| 5及后续 | 原六规则、27逻辑模式、全Separation/Collection的ProofZF/U；内部传输与解释 | 任意内部证明码正确性，最后原核Con_ZF→Con_target |

本批新增12模块259项显式声明、46个完整Source/sourceZF核/nativeZF核闭句模式。
全部构造和根字段结果是纯成员对象Derives；没有新增对象公理或更换推导核。
完整类型识别、内部替换、ProofZF/U、内部编译器及最终Con仍未完成。
本批实际验收见STEP4_FORMULA_CODE_CONSTRUCTION_ACCEPTANCE.zh-CN.md。


2026-10-22全内部位置及字段图类型批次：
4c.b.3d.2b.i完成。有限数码k的内部成员严格等价于Num_0至Num_(k-1)的对象析取；
对原forest及完整Fields，在全部内部i,y上证明Edge(g,i,y)↔Positions(k,xs,i,y)。
外部k和j只索引有限公式模式，内部i和y没有外部标准性前提。
同根Node/Constructor经原raw配数单射性恢复payload，继承完整图边定律，不假定payload或图相等。

真实槽位Slot(g,j,y):=∃i(Num_j(i)∧Edge(g,i,y))，实际存在且精确等价于y=xs_j。
任意外部纯公式矩阵P及其全部参数，均有对象Checked(P,g,j)↔P(xs_j)；
该外部模式的每个实例返回完整原核闭句，绝不引入内部真值谓词。
其FormulaCode、Term、实际后继bound的AdvancedCode和原ZeroScalar四个实例均已证明。
已知原构造及同根真实Shape下，membership/equal/negation/四种binary/两个量词的父FormulaCode
精确等价于实际字段图检查；两个量词另覆盖任意给定真实Succ(u,b)下的codeField(u,f)。
零元常量仍使用已证的完整Ctx双条件，无需读取不存在的字段。

| 后续优先级 | 实现输入 | 必须产生的对象证据 |
|---|---|---|
| 4c.b.3d.2b.ii（完成） | SyntaxTreeValidity / SyntaxTermTreeValidity / FormulaCodeTreeValidity | 纯项及所有内部FormulaCode蕴含原Tree.valid；Foundation+Separation关闭对象成员归纳，性质内部量化全部bound/free |
| 4c.b.3d.2c.i正向（完成） | FormulaCodeTypedDataSyntax / Cases / Forward | 接受码实际唯一解码为不含Constructor前提的完整TypedData，保留原字段、所有子树有效性、精确图检查及真实后继scope |
| 4c.b.3d.2c.i反向 | 实际槽位、完整函数图、全部带类型原构造唯一纤维和原编码唯一性 | 从TypedData重建原构造，消去当前已知Constructor前提，正式回到FormulaCode |
| 4c.b.3d.3 | 以上完整双向TypedData及原树有效性 | 完整识别/构造关卡实际验收后才可提升总门禁 |
| 4c.c及以后 | 任意内部rename/替换图；原六规则/27逻辑模式和全ZF公理模式 | 内部捕获规避替换、ProofZF/U和全内部证明码正确性；最终原核Con_ZF→Con_target |

本批新增12模块155项显式声明、22个完整Source/sourceZF核/nativeZF核闭句模式。
上述同根图类型定理仍带已知原Constructor前提，不把它们称作已经消去该前提的完整TypedData解码。
完整类型识别、原树递归有效性、内部替换、ProofZF/U及最终Con的未完成状态不变。
实际验收见STEP4_ALL_POSITION_TYPED_FIELDS_ACCEPTANCE.zh-CN.md。


2026-10-22原树有效性与实际TypedData正向解码批次：
4c.b.3d.2b.ii完成。原Node/Constructor在有效输入合取下树有效，任意内部scalar叶和bvar/fvar封装均树有效；
原完整Term通过真实分支存在见证得到原Tree.valid，不限制外部标准索引。
归纳性质P(w,n)为对象∀b∀f(FormulaCode(w,n,b,f)→Tree.valid(w,n))；
Earlier量化全部内部x∈ω且x∈n，量词分支在真实Succ(k,b)下对(k,f)调用对象归纳假设。
原Foundation和P否定矩阵的原Separation在内部ω上关闭成员归纳；最终Code→Tree.valid无剩余Earlier前提。
这里只证明单向蕴含，不能把任意结构树当作纯语言类型正确的公式。

4c.b.3d.2c.i正向也完成。TypedData是有限纯对象公式：
原NodeData（Shape及所有真实图边子树有效）、完整Ctx、原11标签/字段数及实际递归图字段检查。
Code在任意同根Shape上推出TypedData，并实际存在唯一tag/payload/内部长度/完整字段图的TypedFiber。
接口只假定Ω及FormulaCode，不假定任何Constructor存在；所有原字段见证通过正式存在规则消去。
失败同根Cases/TypedData正式推出¬FormulaCode。TypedData定义不直接包含父FormulaCode；
反向TypedData→FormulaCode仍未证明，完整双向总门禁保持False。

| 下一工作单元 | 输入/建议模块 | 必须验收的对象证据 |
|---|---|---|
| R1：由真实槽位恢复全图 | FieldsFromSlots：实际Fields、Num_k长度及每个有限原位置的对象Slot | ∀内部i,y的GraphLaw；使用原函数图单值性与数码唯一性，禁止从Prop抽取宿主字段数组 |
| R2：从实际字段图恢复原forest | ForestFromFields：实际forest构造、全图唯一性和原列表编解码唯一性 | 给定真实payload和全边对应，正式恢复原Forest；不能假定Constructor或只比较标准样本 |
| R3：逐标签反向识别 | FormulaCodeTypedDataReverse：11类TypedData、R1/R2及原精确构造/图类型双条件 | 对全部内部候选证明TypedData→FormulaCode；保留真实量词后继、原0符号和完整项作用域 |
| R4：完整识别/拒绝汇总 | TypedData/TypedFiber双向桥及已证实际正向唯一解码 | Code↔实际TypedFiber，给定Shape下Code↔TypedData；原核验收后才提升完整类型识别总关卡 |
| 4c.c及以后 | 任意内部rename/捕获规避替换图；ProofZF/U原六规则/27模式和全ZF模式 | 全内部证明码正确性及内部编译器，最终Derives nativeZF [] (Con_ZF→Con_target) |

新增12模块174项显式声明、28个完整Source/sourceZF核/nativeZF核闭句模式。
原树有效性和实际正向TypedData各有True门禁；反向识别、完整类型总关卡、替换、ProofZF/U及最终Con保持False。
实际验收见STEP4_TREE_VALIDITY_TYPED_DATA_FORWARD_ACCEPTANCE.zh-CN.md。


2026-10-22完整TypedData双向识别批次：
R1、R2、R3、R4的对象推导已实现，实际正式验收结果见STEP4_TYPED_DECODE_EQUIVALENCE_ACCEPTANCE.zh-CN.md。
新Slot合取只枚举原有限字段位置，内部图索引和值始终全部量化。
原functionOn给真实定义域和单值性，Num_k成员分类和数码唯一性恢复所有内部边的GraphLaw。
实际Forest存在及同长度真实完整图，再经图外延性和原列表码唯一性恢复同一个原payload；无Constructor前提。
所有RootCheck通过原exE取得真实字段，只为恢复构造器临时遗忘字段谓词，原完整类型检查在上下文中保留。
重建Constructor后对原类型双条件反向实例化，得到同根Code；没有用外部标准输入抽样替代全内部命题。
给定Shape下Code↔TypedData及Code↔Cases成立；任意候选上Code↔实际唯一TypedFiber成立，
并有否定双条件和正负完整分类。原11类类型识别/构造总关卡在本批原核验收通过后提升。
内部rename/替换、ProofZF/U、内部编译器与最终Con仍是待完成目标。

| 顺序与工作单元 | 对象输入/固定范围 | 必须产生的原推导及验收条件 |
|---|---|---|
| 4c.c.1 内部Rename合同 | 内部ω、原FormulaCode、bound/free上下文和两个实际完整索引映射图；允许非单射 | 定义有限纯成员RenameTerm/RenameFormula关系，绑定位置与自由位置分别变换；量词下真实Succ扩展bound映射并保持free映射 |
| 4c.c.2 Rename存在唯一与类型 | 所有内部合法码、长度和范围正确的完整映射图 | 原ZF推导每个候选的正确性及实际唯一输出纤维；原11类逐分支，原零符号保持；实际图相等、恒等与复合定律，不能只证明宿主AST等式 |
| 4c.c.3 内部Subst合同与实现 | 任意内部自由替换序列及所有合法源/目标作用域；保留bound/free分工 | 有限纯成员SubstTerm/SubstFormula；对象后继下提升替换项和bound重命名，明确捕获规避；允许非单射和重复/未用项 |
| 4c.c.4 内部替换完整验收 | 上述实际检查图、任意内部输入及上下文 | 原核存在唯一、类型保持、恒等/复合/rename兼容，并正式覆盖原free_substitution和free_strengthening所需关系 |
| 5a ProofZF/U完整AST | 原6规则、27逻辑模式、七固定ZF公理及全部Separation/Collection；精确PP/ACwo/notAC码 | 纯成员AxZF/AxU/ProofZF/ProofU；全ω有限序列/前驱和作用域检查，不限制外部标准证明码 |
| 5b 内部证明传输 | 既有外部源19规则/原核6规则双向传输的实际内部表示 | 内部编译器及全内部Proof正确性；所有语言/理论转换逐实例证明，不能仅引用外部Lean递归 |
| 6 解释与最终Con | B为原nativeZF，不额外加入AC、不可达或Con(B) | 内部解释所需集合构造及证明变换；最终FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，内部Con量化所有内部ω证明码 |

每个工作单元先冻结纯对象公式和全部参数，再实现原Source推导、TheoryTransport及ZFReplay原核闭句。
构建串行；每批运行scripts/verify.py，检查5个trust=0入口、全声明覆盖、精确原核足迹和源码哈希。
Source/sourceZF/nativeZF证书是中间公式的真实对象证明，但以上未完成工作仍不得由本批的完整类型识别代替。


2026-10-22内部纯项重命名批次：
已落实4c.c.1/4c.c.2的项分支；不是整个公式rename或替换关卡。
IndexMap(w,r,a,c):=Ctx(w,a,c)∧Sequence(r,a,c)，保留原完整functionOn及所有边的目标范围。
Maps分别记录bound与free实际图，内部长度、图、变量码和索引均为对象集合；不要求单射。
RenameTerm实际绑定源/目标索引并检查原bvar/fvar码、输入范围和真实图边，禁止跨类变换。
原ZF证明源/目标类型保持、每个合法内部输入实际唯一输出及实际唯一类型纤维，
并在给定原变量码时证明精确图边双条件。给定两个实际对角映射图，还证明原码不变及实际自重命名。
31个完整Source/sourceZF/nativeZF原核闭句模式；正式结果见STEP4_INTERNAL_TERM_RENAME_ACCEPTANCE.zh-CN.md。
这里只消费给定完整映射图；没有交付任意映射图的量词提升或组合图构造。

| 下一单元 | 固定对象合同/输入 | 必须证明的原核交付 |
|---|---|---|
| L1 关系图构造或直接LiftBound构造 | 原Replacement的任意参数矩阵，或给定实际IndexMap r:b→B | 实际输出完整函数图及全内部边双条件；拒绝杂项，存在唯一，不能只给AST |
| L2 量词下LiftBound | 原native VariableRenaming.lift：新槽here→here，旧there(i)→there(r(i)) | 在u=Succ(b)、U=Succ(B)上实际构造r↑；Edge(r↑,i,j)精确等价于(Zero(i)∧Zero(j))∨∃k,l(k∈b∧Edge(r,k,l)∧Succ(i,k)∧Succ(j,l))，free图原样保留 |
| L3 提升与项关系兼容 | 任意实际量词后继、原新/旧变量码和已验收RenameTerm | 新绑定变量固定，所有旧bound索引和目标索引同步后继；free原映射不变；全部内部范围保持 |
| F1 完整公式rename | 原11构造标签及全部内部码/作用域，L2/L3，已有原Code树有效和类型递归 | 在严格子码上定义实际对象递归；量词分支必须使用正确提升；存在唯一、类型保持及所有原构造精确式 |
| F2 映射恒等/复合及原核规则接入 | 完整实际图，允许非单射；所有bound/free参数 | 公式rename的对象恒等/复合、free_strengthening兼容；每模式真实原核闭句 |
| S及以后 | 捕获规避替换、专用ProofZF/U、内部编译器 | 保留上表4c.c.3至6的完整交付目标；最终原核内部Con蕴含仍未完成 |

LiftBound的0/后继索引约定已核对固定依赖原Logic/Syntax.lean中VariableRenaming.lift。
外部Source的末变量绑定翻译不能改变原native头槽绑定约定。
内部非标准自然数及所有完整图仍在上述量化范围内；外部Bool只索引两个固定模式。


2026-10-22实际量词映射提升批次：
L1、L2、L3已验收。任意参数功能关系在任意内部域集合上实际存在唯一完整Kuratowski图，
保留无杂项、完整functionOn、全内部边双条件和给定目标范围。
具体Value提升矩阵已关闭总性、单值性及目标范围，原Replacement实际给出唯一完整提升图。
图边在所有内部候选上恰为零→零或旧边的同步后继；原0和实际后继点有精确双条件。
只给原IndexMap及Ω，也实际联合取得两个后继上下文和唯一提升图。
新bound固定、旧bound同步后继及free原图保持均有实际RenameTerm推导。
新增15模块236项显式声明、35个完整Source/sourceZF/nativeZF闭句模式；
实际验收见STEP4_INTERNAL_INDEX_LIFT_ACCEPTANCE.zh-CN.md。
完整FormulaRename、捕获规避替换、ProofZF/U和最终Con仍未完成。

最新批次已验收 F1e.1、F1e.2；实际对象证据见
[判断与递归验收](STEP4_RENAME_JUDGMENT_RECURSION_ACCEPTANCE.zh-CN.md)。
12 模块、150 项显式声明、21 个原核闭句模式；732 构建任务、7944 审计、0 警告，701 份哈希独立回读一致。
完整递归判据不等于合法输入的实际唯一公式输出；完整 FormulaRename 总关卡仍未完成。

| 单元与状态 | 实际输入/模块 | 原对象证据及验收条件 |
|---|---|---|
| F1a/F1b 已验收 | 原自然 MapCode、CodedLift 和原 Forest(7) 状态 | 实际唯一映射码/图恢复、给定真实后继的唯一编码提升、实际状态构造和内部七字段唯一解码；目标范围另存 |
| F1c/F1d 已验收 | 实际查询、11类矩阵、原 Separation 和超限递归 | 实际唯一 ω 状态集合，精确成员/真实幂集范围；总单值前提消去，全内部递归图/值、真实前段及联合存在 |
| F1e.1 已验收 | SyntaxRenameJudgmentSyntax/State/Judgment | 内部 n∈ω 守卫与实际 Evaluation/Contains；任意原序数前段的域内 Read↔判断；实际值上的精确状态成员双条件 |
| F1e.2 已验收 | SyntaxRenameRecursiveSyntax、Read/Fields/Case/LocalTransfer、Recursive、SystemSyntax/System | 全11类消去历史，实际 CodedLift 和严格子码保持；全部内部候选的递归双条件和两端类型；八个内部全称参数的统一定律及实际系统 |
| F1e.3a 下一项：输出合同和量词对齐 | 建议 SyntaxRenameOutputSyntax、SyntaxRenameAdvancedKnown；合法输入为源 FormulaCode 与两个 MapCode | 冻结实际 ∃!q 输出纤维及量化全部六个映射码/作用域参数的归纳性质；给定实际 CodedLift(u,v,L)，AdvancedRename↔对应固定提升参数的子判断，所有候选提升见证通过真实后继/码唯一性对齐 |
| F1e.3b 待完成：原子实际唯一输出 | 原 Code 实际解码、原项重命名和原构造纤维 | 四类原子实际构造目标码；membership 保留原零符号；对全部候选输出用项唯一性和原构造单射证明唯一，不能假定 Constructor 存在 |
| F1e.3c 待完成：逻辑归纳步骤 | 原严格子码及完整递归双条件、全内部归纳假设 | 否定/四类双字段构造实际唯一输出；量词在真实提升后的全部参数上实例化同一归纳假设，保留 free 码 |
| F1e.3d 待完成：关闭内部归纳 | 原 Foundation/Separation 成员归纳，性质量化所有内部映射码及作用域 | 全内部合法源输入实际取得唯一目标码，允许非单射和内部非标准长度；无剩余 Earlier/归纳假设或递归存在前提 |
| F1e.4 待完成：完整重命名验收 | 上述判断和实际唯一输出，原11类构造及全部候选 | 原核源/目标类型、原零符号、单构造精确律、真实作用域和实际唯一输出全部验收后，才提升完整 FormulaRename 门禁 |
| F2 待完成 | 原实际恒等/复合完整图、全部上下文 | 原核公式恒等、复合、free_strengthening 兼容，保留全内部量化 |
| S 及以后待完成 | 捕获规避替换、六规则/27模式、全 Separation/Collection、内部编译器与解释 | 完整 ProofZF/U、任意内部证明码正确性，最终原核 Con_ZF→Con_target |

每单元先固定有限纯对象公式和全部参数，再给 Source.Derives、TheoryTransport 和 ZFReplay 闭句。
不使用宿主递归、仅标准码定理或类大小历史代替对象推导。
当前判断/历史消去/递归双条件/类型保持/实际统一系统门禁为 True；
实际唯一公式输出、完整重命名、替换、ProofZF/U 和最终 Con 门禁均为 False。

工程注意：Read 的源码位置早于映射参数，RenameFormula 的源码位置在四个作用域之后；
迁移不能只改函数名。以实际原核双条件和显式字段排列检查验证，不能只验收 AST rename 等式。
大型上下文用公式等式只转换结论；构建串行，每批 scripts/verify.py 并独立核对哈希、七份锁和精确依赖。


2026-10-22 F1e.3a/两个空原子批次：实际验收见[报告](STEP4_RENAME_OUTPUT_NULLARY_ACCEPTANCE.zh-CN.md)。
输出 Fiber 为实际 ∃q(Rename∧∀t(Rename→t=q))；Property 内部量化 R,S,a,b,c,d，Earlier 保留 x∈ω 且 x∈n。
任意实际提升候选通过两个原后继唯一性与输出码唯一性对齐；给定 CodedLift 下 AdvancedRename↔固定提升后的子判断。
全部11类在四个原子标签下可精确筛选；假/真两个空原子实际自重命名且输出唯一，六参数 Property 亦有原核闭句。
合同和筛选不能替代另外两个原子与七个逻辑模式的实际输出证明。
本批10模块123项显式声明、17个闭句模式；742构建任务、8067项审计、0警告，711份哈希独立一致。

| 下一工作单元 | 输入与实现方向 | 原核验收条件 |
|---|---|---|
| F1e.3b.2 | 原 membership/equality 及实际解码图；复用原项重命名、同码字段恢复与新 atomicFilter | 实际目标原子构造及唯一 Fiber；保留同一个原零符号，对齐任意候选解码图，不能只验类型 |
| F1e.3c.1 | Earlier 和 negation/四二元原构造；输入子码严格小于父码 | 每个内部子码实例化同一六参数 Property，实际构造并唯一化目标逻辑码 |
| F1e.3c.2 | Earlier 和两个量词原构造；真实后继与 CodedLift | 实际取得提升码；使用本批 at_lift 对齐子判断；free 码及作用域不变；两个量词实际 Fiber |
| F1e.4 | 全11类已证推进、Foundation、否定矩阵 Separation | 内部成员归纳关闭，所有合法输入实际 ∃!；单构造精确律逐个验收后提升完整 FormulaRename 总门禁 |
| F2/S/5/6 | 前表固定全部对象合同 | 映射代数、捕获规避替换、ProofZF/U、全内部编译和解释，最终内部 Con 原核推导 |

完整 FormulaRename、内部替换、ProofZF/U 与最终 Con 仍为 False；构建串行，不新增对象公理或恢复退役反射实现。


2026-10-22 F1e.3b 四类原子完整基础情形：见[实际验收](STEP4_RENAME_ATOMIC_OUTPUT_ACCEPTANCE.zh-CN.md)。
给定完整实际图，HistoryFreeLocal↔同图 Cases；所有候选解码图先由原码/完整图唯一性对齐，再作对象等词替换。
成员式和等式实际取得两个目标项，原构造器生成目标原子；成员式直接保留源 ZeroScalar 码。
同码源字段恢复、项唯一性及原目标构造唯一性关闭全候选唯一性。
实际 ∃! Fiber 消去全部 MapCode 图见证，四类 Atomic 已推出完整内部六参数 Property，无 Earlier 前提。
7模块134项显式声明、25个闭句模式；749构建任务、8201项审计、0警告，718份哈希独立一致。

| 下一工作单元 | 对象输入/实现职责 | 必须产生的实际原核证据 |
|---|---|---|
| F1e.3c.0 | 已知原逻辑标签4–10及完整11类 Cases | 精确筛选对应逻辑分支，排除异标签并恢复同码源子式字段；不把筛选当输出存在 |
| F1e.3c.1 | Earlier、否定/四二元原构造、严格子码成员界 | 在每个内部子码上实例化同一六参数 Property，实际取得唯一目标子式并构造唯一逻辑码 |
| F1e.3c.2 | Earlier、两个量词构造、真实后继及 CodedLift | 实际取得提升码并更换作用域，使用已证 at_lift 对齐任意候选；free码及范围保持；两个量词实际 Fiber |
| F1e.4 | 全11类推进、Foundation和否定矩阵 Separation | 内部ω成员归纳关闭，消去 Earlier；全部合法内部输入实际∃!和单构造精确律 |
| F2/S/5/6 | 前表固定全部对象合同 | 公式映射代数、捕获规避替换、专用 ProofZF/U、全内部编译和解释，最终原核内部 Con 蕴含 |

本批四类原子基础已通过；完整 FormulaRename、内部替换、ProofZF/U 和最终 Con 的 False 状态保持。
后续继续串行构建和精确足迹审计，不新增对象公理，不恢复退役反射实现。


2026-10-22 F1e.3c/F1e.4a：全内部公式实际唯一输出已验收，见[报告](STEP4_RENAME_TOTAL_OUTPUT_ACCEPTANCE.zh-CN.md)。
11标签筛选与内部Property唯一性组合，给出七类逻辑实际唯一输出。量词先取得源/目标后继和实际提升码，再按提升作用域实例化同一六参数性质。
原FormulaCode完整分类组合全部11类；原Foundation和Property否定矩阵的Separation关闭内部ω成员归纳。
原Below的双蕴含守卫显式转换为Earlier的合取守卫。最终Input→实际∃!、ExistsOutput↔Input和Fiber↔Input均无Earlier、解码图或历史存在前提。
14模块222项显式声明、40个闭句模式；763构建任务、8423项审计、0警告，732份哈希独立一致。

| 下一工作单元 | 输入/实现职责 | 原核验收条件 |
|---|---|---|
| F1e.4b | 给定两端原构造字段、完整递归双条件及同码字段单射 | 各类规范子判断的精确双条件，显式对齐源码和目标码字段 |
| F2 | 全部实际完整索引图和码，允许非单射 | 公式恒等/复合及量词提升兼容，不从编码单独推断目标范围 |
| S | 内部替换序列及全部bound/free作用域 | 捕获规避替换的实际存在唯一、类型和代数，覆盖原free_substitution/free_strengthening |
| 5–6 | 原六规则/27模式、全ZF模式及精确目标公理码 | ProofZF/U、任意内部证明码正确性、编译/解释和最终原核内部Con |

实际全输入唯一输出及对象成员归纳关闭为True；精确单构造律、映射代数、完整FormulaRename总门禁、替换、ProofZF/U和最终Con仍为False。
所有构建串行；每批核查完整脚本、五个trust=0入口、精确足迹和哈希，不新增对象公理或恢复退役反射实现。


2026-10-22 F1e.4b：原11构造精确端点律已验收，见[报告](STEP4_RENAME_EXACT_FIELDS_ACCEPTANCE.zh-CN.md)。
两端字段由原同码单射恢复，规范子判断恢复真实源Input；最终端点双条件没有额外Input前提。
成员式显式保留ZeroScalar及两端符号相等。逻辑律消去两幅实际图；给定任意实际CodedLift，量词精确转为提升后的体判断，原free参数保持。
10模块139项显式声明、26个闭句模式；773构建任务、8562项审计、0警告，742份哈希独立一致。

| 下一单元 | 实现职责 | 对象验收门 |
|---|---|---|
| F2.1 | 完整恒等图/码及binder提升恒等；复用已有项恒等 | 实际图/码存在、全边式、真实后继下的提升恒等；独立目标范围不由列表码推断 |
| F2.2 | 精确11构造律、恒等码及内部成员归纳 | 全部合法内部公式实际自重命名，任意输出恰为原码 |
| F2.3 | 实际完整图复合、编码、项关系和提升兼容 | 图/码、项及公式复合的对象定理，允许非单射；全内部边和作用域保持 |
| S/5/6 | 内部替换序列、原六规则/27模式及全ZF模式 | 捕获规避替换、ProofZF/U、全内部编译/解释和最终原核内部Con |

精确单构造门禁已True；映射代数、完整FormulaRename总门禁、替换、ProofZF/U与最终Con保持False。
继续串行构建、五个trust=0入口、全声明精确足迹与哈希验收，不新增对象公理或恢复退役反射实现。


2026-10-22 F2.1–F2.2：实际恒等码、提升恒等与全内部公式恒等已验收，见[报告](STEP4_RENAME_IDENTITY_ACCEPTANCE.zh-CN.md)。
原 Replacement 实际产生任意域的完整恒等图；Ω 及内部自然长度取得原列表码，任意同码解码图有对角性。
真实 CodedLift 的两个后继相等且输出码保持恒等。全 11 构造推进四参数内部 Property，原 Foundation/Separation 关闭成员归纳。
在 Ω 与两个 IdCode 下，所有内部候选满足 RenameFormula(n,q) ↔ (FormulaCode(n) ∧ n=q)，没有 Earlier 前提。
10 模块 131 项显式声明、16 个闭句模式；783 构建任务、8693 项审计、0 警告，752 份哈希独立一致。

| 当前单元 | 输入与实现职责 | 对象验收门 | 状态 |
|---|---|---|---|
| F2.1 | 完整恒等图、原自然码及实际提升 | 实际存在、全边式、任意同码解码对角、任意后继提升恒等 | 完成 |
| F2.2 | 全 11 构造及四内部参数成员归纳 | 所有内部公式自重命名，任意候选输出精确双条件 | 完成 |
| F2.3a | 可复合的两幅完整实际图、三个明确作用域 | 实际唯一复合图和原自然码，全内部边复合双条件 | 待完成 |
| F2.3b | 原项关系、实际复合图及两个真实提升 | 项复合及提升与复合相容，允许非单射并保留独立范围 | 待完成 |
| F2.3c | 精确构造律和全内部参数归纳 | 无 Earlier 的公式复合与原核规则兼容 | 待完成 |
| S | 内部替换序列及全部 bound/free 参数 | 捕获规避替换存在唯一、类型和代数，覆盖原替换/加强规则 | 待完成 |
| 5–6 | 原六规则/27 模式及完整 ZF/目标公理码 | ProofZF/U、全内部编译/解释及最终 Con 原核推导 | 待完成 |

恒等专门门禁为 True；恒等与复合联合门禁、完整 FormulaRename、替换、ProofZF/U 及最终 Con 保持 False。
下一单元先实际构造复合完整图，不以宿主函数复合或外部 AST 复合等式替代；不从列表码推断独立目标范围。
继续串行构建、五个 trust=0、逐声明精确足迹和哈希验收，不新增对象公理或恢复退役反射实现。


2026-10-22 F2.3a/F2.3b.1：实际图/自然码复合与项复合已验收，见[报告](STEP4_COMPOSITION_MAP_TERM_ACCEPTANCE.zh-CN.md)。
复合关系 Value(r,t,i,j)=∃k(Edge(r,i,k)∧Edge(t,k,j)) 的总单值已在对象核证明；原 Replacement 实际构造唯一完整图。
合法输入实际取得唯一原自然复合码，任意同码实际解码恢复 Composed；三个范围独立显式保留。
全部内部候选的项复合，精确等价于存在实际中间项码的两阶段关系，bound/free 不混合。
11 模块 171 项显式声明、28 个闭句模式；794 构建任务、8864 项审计、0 警告，763 份哈希独立一致。

| 当前单元 | 输入与实现职责 | 原核验收门 | 状态 |
|---|---|---|---|
| F2.3a | 两个可复合完整图、三个范围、原自然码 | 实际唯一结果图/码、全边双条件、任意实际解码识别和精确输入判据 | 完成 |
| F2.3b.1 | 原 bound/free 项关系及实际复合图 | 正向项复合与存在内部中间项码的完整双条件 | 完成 |
| F2.3b.2 | 实际 Composed(r,t,g) 和三组真实 Lifted，共享内部后继 A,C,E | 提升输入图的复合恰为提升结果图；随后以实际 Encoded 图取得 CodedCompose 相容 | 待完成 |
| F2.3c | 全 11 构造精确律、提升相容、全部内部参数 | 原 Foundation/Separation 关闭公式复合归纳；输出总性/唯一性给反向两阶段双条件 | 待完成 |
| S | 全内部替换序列及 bound/free 范围 | 捕获规避替换存在唯一、类型与代数，覆盖原替换/加强规则 | 待完成 |
| 5–6 | 原六规则/27 模式及完整理论公理码 | ProofZF/U、全内部编译/解释及最终内部 Con 原核推导 | 待完成 |

下一单元逐真实零/后继边证明提升相容；中间后继实际构造，不同候选由原后继唯一性对齐。
不以宿主函数复合、Nat.succ 或外部标准 AST 归纳替代。原自然列表码不决定独立目标范围。
图/码复合及项复合门禁为 True；提升相容、公式复合和联合总门禁、替换、ProofZF/U 与最终 Con 仍为 False。
继续串行构建、五个 trust=0、逐声明精确足迹及哈希验收，不新增对象公理或恢复退役反射实现。


2026-10-22 F2.3b.2：真实 binder 提升与实际图/自然码复合已验收，见[报告](STEP4_BINDER_COMPOSITION_ACCEPTANCE.zh-CN.md)。
原零/后继边实际构造中间后继；原完整同域函数图相等把逐边包含升级为完整 Composed。
实际 Lifted 与提升图的 Composed、实际 CodedLift 与提升码的 CodedCompose 均有任意候选识别双条件。
独立中间后继 C,D 用原 Insert 唯一性对齐，显式等词传输第二提升的源范围。
5 模块 87 项显式声明、17 个闭句模式；799 构建任务、8951 项审计、0 警告，768 份哈希独立一致。

| 当前单元 | 实现职责 | 原核验收门 | 状态 |
|---|---|---|---|
| F2.3b.2 | 真实零/后继、完整同域图相等及三组实际提升码 | 提升与图/码复合相容，任意候选识别、独立中间后继相等 | 完成 |
| F2.3c.1 | 已知源构造下实际目标字段存在及精确端点律 | 两阶段字段在对象量词内取得，原子/逻辑子判断精确恢复 | 待完成 |
| F2.3c.2 | 四原子与项复合 | 原零符号、bound/free 和全部作用域保持，原子复合推进 | 待完成 |
| F2.3c.3 | 14 内部参数 Property、七逻辑构造及当前 mixedMiddle | 量词实际中间后继对齐并提升 bound 复合，free 码和范围保持 | 待完成 |
| F2.3c.4 | 原 Foundation/Separation、输出总性及唯一性 | 无 Earlier 的全内部公式复合与存在中间码双条件 | 待完成 |
| F2/S | 原核加强/替换规则和全部内部范围 | free_strengthening 兼容、捕获规避替换存在唯一、类型与代数 | 待完成 |
| 5–6 | 原六规则/27 模式及完整理论公理码 | ProofZF/U、全内部编译/解释及最终内部 Con 原核推导 | 待完成 |

Property 内部量化六映射码、六作用域和中间/最终公式码 q,v；在两组 CodedCompose 与两次 RenameFormula 下证明结果。
已知源/目标构造的精确律负责内部字段对齐，不在 Lean 中抽取内部字段数组；不得限制外部标准码。
提升相容门禁为 True；公式复合、联合总门禁、完整 FormulaRename、替换、ProofZF/U 和最终 Con 保持 False。
继续串行构建、五个 trust=0、逐声明精确足迹与哈希验收，不新增对象公理或恢复退役反射实现。


2026-10-22 F2.3c：全内部公式复合已验收，见[报告](STEP4_FORMULA_COMPOSITION_ACCEPTANCE.zh-CN.md)。
已知源构造实际取得中间/最终字段，精确端点律恢复两阶段子判断；成员式保留原零符号及符号相等传输。
14参数Property在对象语言内部量化六码、六作用域及q,v；量词用真实后继对齐和实际提升复合，free参数保持。
原Foundation及Property否定矩阵的完整Separation关闭归纳；输出总性/唯一性给存在内部中间公式码的完整双条件。
14模块221项显式声明、35个闭句模式；813构建任务、9172项审计、0警告，782份哈希独立一致。

| 当前单元 | 实现职责 | 原核验收门 | 状态 |
|---|---|---|---|
| F2.3c | 全11构造、14内部参数归纳及输出分解 | 无Earlier的复合、实际中间码双条件 | 完成 |
| F2.4a | 原free头槽位移的实际图/原自然码，b→Succ(b) | 全内部边i↦Succ(i)、实际唯一图/码，覆盖空源域b=0 | 待完成 |
| F2.4b | bound恒等、free位移与全11构造/真实binder | 纯WeakenFree关系、存在唯一及原核free_strengthening兼容 | 待完成 |
| S | 内部替换序列和全部bound/free范围 | 捕获规避替换存在唯一、类型和代数，覆盖原替换/绑定规则 | 待完成 |
| 5 | 原六规则/27模式及完整ZF/目标公理码 | ProofZF/U纯AST、全内部证明码正确性及编译传输 | 待完成 |
| 6 | 全内部解释及固定内部Con | 最终原nativeZF内Con蕴含的真实Derives | 待完成 |

原Core.free_strengthening的方向是由新增free头槽后的formula.weakenFree推回原formula；先用上行free位移链接编码该语法操作。
全公式复合和恒等/复合联合门禁已True；完整FormulaRename总门禁保留False，原核加强规则兼容及后续关卡未完成。
全内部量化和原规则精确方向保持；继续串行构建、五个trust=0、逐声明精确足迹与哈希验收，不新增对象公理或恢复退役反射实现。


2026-10-22 F2.4a：原free头槽的实际完整位移图/原自然列表码已验收，见[报告](STEP4_FREE_SHIFT_ACCEPTANCE.zh-CN.md)。
原Replacement构造Succ关系完整图；内部序数成员界证明目标为实际Succ(b)，全部边恰为i∈b且Succ(j,i)。
图/码存在唯一、任意实际解码识别、合法输入双条件和无后继存在前提的实际状态均已证明。
fresh零头槽无入边；空源域实际图为空，Ω和Empty本身取得其实际唯一位移码状态。
5模块144项显式声明、23个原核闭句；818构建任务、9316项审计、0警告，787份哈希独立一致。

| 当前单元 | 实现职责 | 原核验收门 | 状态 |
|---|---|---|---|
| F2.4a | 实际free位移图/自然码、任意候选和空域 | 全边、存在唯一、解码识别、精确输入、零槽排除 | 完成 |
| F2.4b.1 | bound恒等和free位移实际码，纯WeakenFree | 全合法内部输入实际唯一弱化输出与精确参数识别 | 待完成 |
| F2.4b.2 | 全11构造及真实binder | bound恒等提升、free位移不变、精确构造律与类型 | 待完成 |
| F2.4b.3 | 原weakenFree和free_strengthening | 原语法链接及内部六规则检查接口中的正式兼容 | 待完成 |
| S | 内部替换序列和所有范围 | 捕获规避替换存在唯一、类型与代数，覆盖替换/绑定规则 | 待完成 |
| 5–6 | 原规则/模式、完整理论、内部解释 | 专用ProofZF/U、全内部证明码正确性/编译及最终Con | 待完成 |

原规则方向保持为由weakenFree前提删除未用fresh free头槽；上行位移不需要也不能改成整个后继域的下行全映射。
原free_strengthening兼容及完整FormulaRename总门禁继续False；本批四个位移细分门禁为True。
串行构建、五个trust=0、逐声明精确足迹和哈希验收继续；原对象背景与最终Con量化范围保持。


2026-10-22 F2.4b.1–b.2：全内部公式弱化已验收，见[报告](STEP4_FORMULA_WEAKENING_ACCEPTANCE.zh-CN.md)。
纯Weak在合法输入上实际存在唯一；任意实际恒等/位移码给精确Rename双条件。
全11构造已知端点律及真实bound提升、free后继项规律已证明；逻辑律的码见证完全在对象量词内处理。
10模块184声明、30闭句模式；828构建任务、9500项审计、0警告；797份哈希独立一致。

| 单元 | 实现输入与职责 | 交付与原核验收门 | 状态 |
|---|---|---|---|
| F2.4a | 原 free 头槽的实际完整图和原自然列表码 | 全内部边、唯一图码、精确输入、空源域与零槽排除 | 已完成 |
| F2.4b.1 | 恒等码、位移码、全内部 RenameFormula | 纯 WeakenFree；实际唯一输出、精确输入双条件和无后继存在前提的实际状态 | 本批完成 |
| F2.4b.2 | 原11构造端点、真实 bound 提升、free位移 | 全11已知端点律；逻辑律的所有码见证在对象量词内消去 | 本批完成 |
| F2.4b.3 | 原 Formula.weakenFree 与原数值语法编码 | 原操作的准确编码对应；外部标准实例对应只是中间证据 | 待完成 |
| S1 | 纯集合语言的原 free_substitution 项码列表字段 | 全内部 open-term/fvar 索引对应、原列表与实际索引图转换，不擅改原规则格式 | 待完成 |
| S2 | 跨 bound/free 的实例化、抽象及真实 binder | 全内部捕获规避操作的存在唯一、类型、精确构造律与代数 | 待完成 |
| 5a | 原六规则/27模式、完整 Separation/Collection 和目标附加公理 | 专用 ProofZF/U 纯 AST；加强规则从弱化前提回到原结论，覆盖所有内部证明码 | 待完成 |
| 5b | 原源/目标证书转换和内部编码关系 | 全内部编译器及检查正确性；不能仅对标准宿主树归纳 | 待完成 |
| 6 | 固定内部 Con 与内部解释 | 原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target) | 待完成 |

原规则兼容和最终Con门禁不随Weak辅助定理自动开启；明确区分标准语法对应、全内部码正确性和最终对象主句。
所有实现保持原纯语言、nativeZF背景和全部内部ω量化；源证明必须能回放为原FirstOrder.Derives。
角色分工：实现agent负责独立模块；只读审阅agent核对公式范围和推导层；主agent独占串行构建及最终精确足迹验收。


2026-10-22 S1：原free替换项列表/索引码的双向实际唯一转换已验收，见[报告](STEP4_FREE_SUBSTITUTION_CODEC_ACCEPTANCE.zh-CN.md)。
原列表参数保留；完整字段图和完整索引图在对象量词内相连，全部内部候选都有精确边/字段双条件。
12模块230声明、33个原核闭句；840构建任务、9730项审计、0警告；809份源哈希独立一致。

| 单元 | 实现职责及输入 | 对象交付与实际验收门 | 状态 |
|---|---|---|---|
| F2.4b.1–b.2 | 原恒等/位移码和全部内部公式 | Weak实际唯一输出、全11端点律、真实binder提升 | 已完成 |
| F2.4b.3 | 原weakenFree与数值语法编码 | 准确编码对应；随后连接全部内部证明码的加强规则检查 | 待完成 |
| S1 | 纯OpenTerm、原项码列表、实际完整字段图/索引图 | 双向实际唯一码、精确输入双条件、任意实际解码和全候选字段对应 | 本批完成 |
| S2 | S1的原项列表L与MapCode S、bound恒等码及RenameFormula | 原项列表参数化的全公式free替换，存在唯一、类型、11构造律和量词下相容 | 待完成 |
| S3 | 混合bound/free项像和真实binder提升 | InstantiateTop/AbstractFreeTop及捕获规避替换的全内部正确性；两类项像的bound部分均需提升 | 待完成 |
| 5a | 原六规则/27模式及完整ZF/目标公理码 | 专用ProofZF/U纯AST、准确原参数字段、所有内部证明码的规则核验 | 待完成 |
| 5b | 原源/目标转换器与内部检查关系 | 全内部编译器和检查正确性，包含完整Separation/Collection | 待完成 |
| 6 | 内部解释、固定Con_ZF和Con_target | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

S1的转换证明不等于S2的全公式替换，也不等于专用原核rule-5检查器兼容。
完整捕获规避替换与最终Con继续False；保持原背景、独立源/目标范围和全部内部ω量化。
实现与审阅保持明确文件范围；主agent独占串行构建，逐声明审计和独立回读均须通过。


2026-10-22 S2.1–S2.3：原项码列表参数的全公式free替换已验收，见[报告](STEP4_FORMULA_FREE_SUBSTITUTION_ACCEPTANCE.zh-CN.md)。
实际唯一输出、准确类型/输入双条件、11构造端点律、原列表字段项律和真实binder提升已证明。
8模块150声明、25原核闭句；848构建任务、9880项审计、0警告；817份哈希独立一致。

| 单元 | 实现职责及输入 | 对象交付和原核验收门 | 状态 |
|---|---|---|---|
| S1 | 原项码列表、完整字段图和索引MapCode | 双向实际唯一码、准确输入和任意实际字段对应 | 已完成 |
| S2.1 | FormulaCode、TermList、实际恒等/转换码 | 纯全公式free替换，实际唯一输出、准确类型和输入双条件 | 本批完成 |
| S2.2 | 原11构造和实际原列表字段 | 精确端点律；bound保持，free目标码就是原列表字段 | 本批完成 |
| S2.3 | 实际后继bound域及恒等提升 | 量词保持原free列表；逻辑律的R/S/K见证在对象量词内取得和消去 | 本批完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree语法及数值编码 | 准确原编码对应，并连接原规则5/4的全内部检查；标准宿主实例仅是中间证据 | 待完成 |
| S3 | 混合bound/free项像与真实binder提升 | InstantiateTop/AbstractFreeTop及一般捕获规避替换的全内部存在唯一、类型和代数 | 待完成 |
| 5a | 原六规则/27模式、完整Separation/Collection及目标公理 | 专用ProofZF/U纯AST和准确字段检查，覆盖全部内部证明码 | 待完成 |
| 5b | 内部证书转换器和检查关系 | 任意内部证明码的编译及检查正确性 | 待完成 |
| 6 | 内部解释与固定内部Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

S2.4的原编码/规则检查对应和S3的混合替换仍必须完成；本批操作不能代表一般跨bound/free替换。
最终Con目标、原六规则/27模式、完整Separation/Collection及全部内部ω量化保持。
主agent独占串行构建；每批审阅准确公式范围、实际原核接口、逐声明依赖和独立哈希。


2026-10-23 S3.1/S3.2a：混合项替换及实际项像表逐值变换已验收，见[报告](STEP4_MIXED_TERM_IMAGES_ACCEPTANCE.zh-CN.md)。
14模块188声明、21个原核闭句；862构建任务、10068项审计、0警告；831份独立哈希一致。
以下为最新工程流程，历史表中的S3整体未完成状态不代表本批细分单元未实现。

| 单元 | 输入及依赖 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S2.1–S2.3 | 原TermList、实际IdCode/转换码 | 全公式free替换的唯一输出、准确输入、11端点律和真实恒等binder提升 | 已验收 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree及数值码 | 精确原编码对应，再接原规则5/4的任意内部证明码检查 | 待完成 |
| S3.1 | 实际两张完整项像表 | 跨bound/free项替换唯一输出、准确类型/输入及已知源码字段律 | 本批验收 |
| S3.2a | 目标重命名与S3.1 | 两表逐值变换的实际唯一图、精确边及实际bound后移状态 | 本批验收 |
| S3.2b | S3.2a和真实源/目标后继域 | 新bound0→目标bvar0；旧bound源索引后移；free源索引保持；两表bound像均后移；实际唯一完整提升 | 下一步 |
| S3.3 | S3.2b、原11构造、全部内部公式码 | 一般混合公式替换实际总唯一、准确类型和全部构造端点律 | 待完成 |
| S3.4 | S3.3及实际首槽表 | InstantiateTop/AbstractFreeTop实际总唯一、嵌套binder保护、准确原字段/数值编码对应 | 待完成 |
| 5a | 原六规则/27模式、完整ZF及目标公理 | 专用ProofZF/U纯AST、全部原字段及任意内部码的检查正确性 | 待完成 |
| 5b | 内部源/目标证书转换器 | 全内部证明码编译及正确性，包含完整Separation/Collection | 待完成 |
| 6 | 内部解释及固定Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |


完整混合binder提升及最终Con保持待完成；后继目标范围前提尚未消去。主agent独占串行构建和最终验收。
