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
| 4b | 全内部序列、自然数递归和原Gödel/结构列表约定 | Internal/NaturalArithmetic、GodelPairing、StructuralCode | 全内部数值运算实际存在唯一、编码/解码/界性质及原核Derives；紧凑quotation避免展开巨大一元数值 | 全内部递推、加乘半环关系律、自然差分/顺序及基本平方界完成；原配数与结构码待做 |
| 4b.a.1 | Foundation、一个序数正文Separation及对象ω归纳 | Internal/OmegaOrdinals | 每个内部ω成员满足原完整ordinal定义；有限两句背景及原核闭句 | 完成 |
| 4b.a.2 | 任意参数总单值步进关系、实际自然前驱与完整历史图 | Internal/NaturalRecursionSyntax/Total/Determinism、NaturalRecursion | 对任意有效历史实际证明算子总单值；原超限递归给实际存在唯一递归图；四个完整原核模式 | 完成；不假定历史已经符合递推 |
| 4b.a.3 | 上项真实递归图、后继域及图唯一性 | Internal/NaturalEvaluationSyntax/Existence/Uniqueness/Fiber、ObjectNaturalRecursion、NaturalRecursionLaws | 每个内部n∈ω有实际唯一末值；算子零点/后继方程和求值零点律；保留所有对象量词和公式参数 | 完成；步进公式是外部模式索引，每个实例有原核闭句 |
| 4b.a.4 | 原Pairing/Union/Extensionality的后继总单值证明 | Internal/SuccessorRecursion | 具体原后继关系消去所有算子前提，给全内部自然长度唯一后继迭代及零点求值方程 | 完成；不据此声称完整自然数加法/乘法或ω值域闭包 |
| 4b.b.1 | 通用递推、实际前段限制及ω归纳 | Internal/NaturalEvaluationRange/Step、NaturalSuccessorStep、NaturalAddition*、NaturalMultiplication*、ObjectNaturalAddition/Multiplication | 全部内部自然索引上的加乘实际自然值存在唯一、ω闭包、零点和双向后继方程、左零律；十个完整原核闭句 | 完成；见STEP4_BASIC_ARITHMETIC_ACCEPTANCE.zh-CN.md |
| 4b.b.2a | 基本加法、原后继单射、对象ω归纳与明确Separation实例 | Internal/NaturalAdditionShift/Commutative/Associative/Cancellation/Bounds、ObjectNaturalAdditionAlgebra/Order | 双向左后继、交换、双向结合、两侧抵消、两加数不降界、正加数严格成员界及和值为零刻画；九个完整原核闭句 | 完成；见STEP4_ADDITION_ALGEBRA_ACCEPTANCE.zh-CN.md |
| 4b.b.2b | 上项加法代数与基本乘法、内部ω归纳及原自然顺序 | Internal/NaturalMultiplicationAlgebra/Order、NaturalDifference | 乘法交换/结合/分配、自然次序差分及Gödel配数所需界；每项有原核闭句 | 乘法代数、自然差分/单调和基本平方界完成；原配数专门界及编码待做 |
| 4b.b.2b.i | 已证加法交换/结合及实际和存在唯一 | Internal/NaturalAdditionReassociation | 用原关系Add逐见证证明四项重排/重新结合；每次中间和实际存在于ω | 完成；实际中间和、三项/四项重排原核闭句 |
| 4b.b.2b.ii | 基本乘法后继式、上项加法重排及对象ω归纳 | Internal/NaturalMultiplicationDistributive | 从Add(b,c,d)、Mul(a,b,p)、Mul(a,c,q)、Add(p,q,r)推出Mul(a,d,r)，保留全部内部自然数与见证 | 完成；双向分配闭句，见STEP4_MULTIPLICATION_ALGEBRA_ACCEPTANCE.zh-CN.md |
| 4b.b.2b.iii | 实际乘积/和及分配、加法左右后继 | Internal/NaturalMultiplicationShift/Commutative | 左参数后继乘积方程及Mul(a,b,p)↔Mul(b,a,p)，全内部ω归纳 | 完成；左后继双向式及交换闭句 |
| 4b.b.2b.iv | 已证分配与基本乘法递推、完整原核图和值 | Internal/NaturalMultiplicationAssociative | 以实际中间乘积见证给出双向结合式，所有原递归辅助证书由ZF消去 | 完成；双向结合闭句 |
| 4b.b.2b.iv.a | 实际Empty(z)、Succ(e,z)、乘法零点及后继式 | Internal/NaturalMultiplicationAlgebraLaws | 内部e作为乘法两侧单位元的双向值刻画；不固定宿主1 | 完成；两侧单位元一个完整闭句 |
| 4b.b.2b.v | 加乘半环关系律、加法抵消/基本顺序界、内部前驱分解与ω归纳 | Internal/NaturalDifference/Order | 实际自然差分、严格非零差分、加乘单调/反射及基本平方界 | 完成；原配数专门界在4b.c实际验收 |
| 4b.b.2b.v.a | 原内部序数比较、实际自然后继和值、对象ω归纳 | NaturalOrderBasic、NaturalDifferenceSyntax/Step/Positive、NaturalDifference | 全序/后继刻画；次序↔实际自然差分，严格次序↔非零差分；仅在内部ω候选内唯一 | 完成；八个闭句，见STEP4_NATURAL_ORDER_ACCEPTANCE.zh-CN.md |
| 4b.b.2b.v.b | 上项实际差分及加乘分配/抵消 | NaturalAdditionMonotone、NaturalMultiplicationPositive/Monotone/OrderLaws | 两侧加法顺序等价；零因子刻画、含零乘数弱单调及非零乘数的严格等价/反射/消去 | 完成；十三个闭句，零乘数边界保持 |
| 4b.b.2b.v.c | 实际内部空集/后继单位、上项单调与原序数传递 | NaturalArithmeticBounds、ObjectNaturalNumericBounds | 非零数至少为内部一，非零因子乘积下界，平方下界/严格单调/单射 | 完成；五个闭句，不据此声称已完成配数 |
| 4b.c | 内部算术、全部内部有限序列及原编码约定 | Internal/GodelPairing、StructuralCode | 配数/结构列表的实际内部存在唯一、解码/界与正确性；区分树数值和字节传输码 | 待做 |
| 4b.c.1 | 固定原配数/结构列表数值约定、全部已证自然算术关系 | Internal/GodelPairSyntax | 严格a∈b时p=b*b+a，否则p=(a*a+a)+b；实际自然中间值与纯ℒ分支AST | 待做；AST只是输入，下一关须有真实Derives |
| 4b.c.2 | 上项分支、实际加乘总单值、平方与顺序界 | Internal/GodelPairExistence/Unique/Bounds | 全内部a,b的实际唯一配数，分量界、分支区间不交及配数单射；原ZF闭句 | 待做；不套用ZFC模型语义或外部标准码 |
| 4b.c.3 | 配数区间/唯一性、内部有界搜索或ω归纳 | Internal/GodelUnpair | 全内部自然码的实际唯一解码、正反配数对应及严格所需界；含非标准码 | 待做 |
| 4b.c.4 | 原structural_list_code/节点后继约定及配数对象证明 | Internal/StructuralCode | 内部结构列表、节点与字段的实际编码/解码、子码界和递归正确性 | 待做；保留空结构列1、叶0数值2约定 |
| 4c | 上项数值编码、纯语言唯一关系编号0及无函数符号 | Internal/SyntaxCode、SyntaxTransform | 全11公式构造、bound/free长度及全部非单射替换的内部关系和正确性；不得只覆盖标准码 | 待做 |
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
