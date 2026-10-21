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
| 3b | 源Replacement版ZF与原Collection版ZF | ZFEquivalence | 七固定公理及任意参数的两种全模式，两个方向的实际Derives | 七固定公理/全分离双向及Collection→源Replacement完成；源ZF全正向回放完成；反向Collection待做 |
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
| 3b.3 | 3b.1–3b.2及全Replacement | Ordinals、Recursion、Rank、CumulativeHierarchy | 内部序数比较/极小秩、秩覆盖与Vα存在性；原推导核全参数证明 | 集合归纳/极小元、原序数基础和任意两序数比较完成；内部族并集/递归/秩待做，不使用宿主WellFounded |
| 3b.3a | 实际传递覆盖、有界成员归纳、Foundation及相应完整Separation实例 | SetInductionSyntax/Logic、SetInduction、GlobalMinimalSyntax、GlobalMinimal | 每个任意参数公式有全体集合归纳与无界成员极小元的完整对象闭句；源ZF和原核Derives；不引入统一真值谓词 | 完成 |
| 3b.3b | 原Source.ordinal、Foundation/EmptySet/Pairing/Union | OrdinalSyntax/Foundation/Transitivity/Restriction/Empty/Successor、ObjectOrdinalBasic | 原定义严格rfl；全内部子集极小元、不自属、成员闭包、实际空/后继序数；源ZF与原核Derives | 完成 |
| 3b.3c | 原序数基础、Extensionality、Foundation及正文x∉b的一个Separation | OrdinalDifference、OrdinalInitialSegment、OrdinalComparison/Trichotomy、ObjectOrdinalComparison | 内部传递子集为初段或相等；任意两个原序数三歧比较及两两排斥，保留全部对象序数量词；六条原核闭句 | 完成 |
| 3b.3d | 原序数比较、Union、Foundation及完整函数图/模式设施 | OrdinalUnion、OrdinalRecursion、Rank | 任意内部序数集合的并仍是序数并为最小上界；内部递归的存在唯一、秩覆盖；每项须原核全量化Derives | 下一项，尚未实现 |
| 3b.4 | 对象秩与累积层 | CollectionFromReplacement | 对每个输入x取唯一最小见证秩，Replacement收集秩，Vα统一容纳见证 | 待做；必须导出完整原Collection句子 |
| 3c | 原六规则Hilbert证书与源19规则 | ReverseDerivation | 全27逻辑模式/6构造→原源演绎；任意局部假设、非单射变量环境；闭句在一个未用变量中回译 | 完成，外部证书传输；内部码表示归步骤5 |
| 3d | 源图选择与原生不交族选择集 | ChoiceEquivalence | 原ZF内双向对象推导，内部集合图、全量词、无外加AC | 待做 |
| 4 | 固定原核六规则及ZF/U公理识别 | Internal/ProofZF、ProofTarget、ConFormula | 完整纯ℒ公式AST；任意内部ω中的Proof/Con正确性；不得套用ZFC专用检查器 | 待做 |
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
