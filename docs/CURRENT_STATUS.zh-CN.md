# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

`ForcingAtomicDenseTemplate.outer_order_query` 从原稠密性编译和实际外层提升表，导出同一顺序守卫输出的直接替换推导。该推导保留外层提升后的自由项表，并从同一次提升读取绑定的零号条件项。该直接推导已用于比较共同表上的外层顺序守卫，码等式由同一个零号绑定项和两张提升表上的自由项对应推出。[外层顺序守卫码等式验收](../verification/forcing-atomic-density-outer-equality-acceptance.json) [本地验收](../verification/forcing-atomic-density-outer-order-acceptance.json)

`ForcingAtomicDenseTemplate.compare_shell_members` 比较两份实际查询中的两个成员守卫。原条件表的载体项经共同表路由保留。两个绑定各自从实际提升表读取零号条件项，构造器唯一性给出同一对象码。完整前提码还差两个顺序守卫和原子见证体的等式。[本地验收](../verification/forcing-atomic-density-members-acceptance.json)

`ForcingDensityInstantiation.with_mixed_shell` 从原密度前提的实际替换中读取两层提升表及五个子查询。`ForcingAtomicDenseTemplate.with_quoted_shell` 从原子稠密性证明的实际模板码取得同样的六个构造步骤。`raw_shell_eq` 用五个实际叶码的对象相等式推出完整前提码相等。两个成员守卫的结果见上文。[本地验收](../verification/forcing-atomic-density-shell-acceptance.json)

`ForcingDensityCode.with_atomic_rebound` 消费统一密度编译的实际见证体记录。在第一层绑定替换中，用实际名字项像和恒等自由项表重组原子编译。在第二层用同一运行记录的条件替换表，把最终见证体码读成对原成员／相等模板的直接查询。下一步是证明统一密度查询与已有原子稠密性证明在共同表上的完整前提码相等。[本地验收](../verification/forcing-atomic-density-rebound-acceptance.json)

`ForcingDensityGuards.kernel_certificate` 将当前条件实例的两个实际守卫码与同一条件、同一张表上的原守卫查询对齐。在给定两条守卫的内部证明时，它用原规则消去两层蕴含，得到同一个存在式尾部的证明。`member_from_proof` 已能将同一条件和载体的成员性证明传输到这个实例的成员守卫。新验收的 ForcingDensityGuards.tail_from_row 从同一背景 G 提取预序和所选条件成员性，沿原表更新保留载体字段。给定原自反性正文及两个原生子查询，它构造实际自反性实例，消去两个守卫并得到 G → 同一个存在式尾部。ForcingDensityGuards.with_reflexive_instances 已从原预序的实际编译记录取出同一自反性正文及两个子查询，并在所选条件处生成两项原生实例。ForcingDensityGuards.reflexive_member_agrees 已证明成员性实例码与实际密度成员守卫码相等。两者使用同一所选条件，且原条件槽更新保留载体字段。ForcingDensityGuards.reflexive_order_agrees 也已证明顺序实例码与实际密度顺序守卫码相等。ForcingDensityGuards.tail_from_compilers 从原编译记录构造两个守卫的证明并消去它们，得到 G → 同一个存在式尾部的内部证明。ForcingDensityGuards.falsum_from_density_records 从同一选定条件的编译及实例记录，把 G → 同一存在式尾部的内部证明变换成 G → 原 ⊥ 码的内部证明。该证明复用原绑定转换、全称化、第 24 条逻辑公理与 MP。整条原密度归纳及最终 Con 尚待装配。见[假常元见证消去验收](../verification/forcing-falsum-acceptance.json)。合取分支中，ForcingDensityCode.with_conjunct_compiler 从同一父代入记录取得两个子码，用原载体和顺序守卫构造所选子公式的密度编译记录。ForcingDensityGuards.conjunction_exists_from_witness 用实际开绑定和子式实例，将父存在式的见证传给左或右子公式。ForcingDensityGuards.conjunction_exists_from_compiler_shells 已从父、子实际编译记录的存在式尾部生成开绑定，用同一张弱化代入表证明两份前缀代入表相等，再用原见证和两个相同守卫构造父存在式到所选子存在式的内部证明。ForcingDensityGuards.with_conjunct_density_proof 已将外层全称稠密性前提传至任一实际子式，同时产生子式的原编译记录、同表代入结果和同一背景下的内部证明。ForcingSourceDensity.conjunction_step 从真实编译历史读取两个较小的源码，实例化两条对象归纳假设并用原合取规则生成同一背景下的结论。封闭推导已在 nativeZF 原核重放。见[源码合取归纳步验收](../verification/forcing-source-density-conjunction-acceptance.json)。见[外层全称传输验收](../verification/forcing-conjunction-outer-acceptance.json)、[实际存在式开绑定验收](../verification/forcing-conjunction-openings-acceptance.json)和[合取见证验收](../verification/forcing-conjunction-witness-acceptance.json)。见[顺序守卫及消去验收](../verification/forcing-reflexive-order-acceptance.json)。见[成员守卫验收](../verification/forcing-reflexive-member-acceptance.json)。见[自反性实例验收](../verification/forcing-reflexive-instances-acceptance.json)。见[本批验收](../verification/forcing-density-tail-acceptance.json)。见[守卫验收](../verification/forcing-density-guards-acceptance.json)。

`ForcingDensityInstantiation.kernel_certificate` 读取原稠密性公式的实际全称码，用同一张替换表的指定条件槽作为实例项。它生成 `G → 实例` 的原内部证明，并保留该实例中两个守卫和存在式尾部的精确查询。Windows 整仓验收已通过。两个守卫的原查询对应见上述证书。见[当前条件实例验收](../verification/forcing-density-instantiation-acceptance.json)。

`ForcingSourceDensityConstant.truth_kernel_certificate` 在普通 nativeZF 原核内，从原编译及实际混合查询取得真常元的内部 `G → 输出` 证明，允许任意内部自由作用域。`false_from_compiler` 在实际假常元查询上保留同一 `⊥` 码和原稠密性见证记录。ForcingSourceDensity.falsum_step 现已从同一原稠密性编译查询生成并接入这些记录。ForcingSourceDensity.falsum_step_from_runtime 已从现有运行记录读取同一预序的自反性查询和原表的载体字段，在实际条件消去两条守卫和存在式并推出准确的 ⊥ 输出。封闭推导已在 nativeZF 原核重放。见[假常元运行记录验收](../verification/forcing-source-density-falsum-runtime-acceptance.json)。ForcingSourceDensity.truth_step 也已接入同一对象归纳谓词。见[源码常元归纳步验收](../verification/forcing-source-density-constants-acceptance.json)。两项已通过 Windows 整仓验收。见[常元验收](../verification/forcing-constant-density-acceptance.json)。

`ForcingDensityCode.kernel_certificate` 在 nativeZF 原核中为任意内部强迫公式码构造原 `force_of_dense` 的稠密性前提。它插入两层条件绑定，只在见证正文中替换指定条件槽。`ForcingDensityCode.from_tables` 使用同一份实际替换表生成该前提的查询码。两项已随主入口通过 Windows 整仓验收。全内部公式码的稠密性推导尚未闭合。见[稠密性前提验收](../verification/forcing-density-code-acceptance.json)。

`ForcingSourceMonoInduction.kernel_certificate` 已通过模块级 `--trust=0`。它在原运行记录下，用对象 ω 成员归纳覆盖全部内部公式码，沿用原编译器各分支和两份实际替换。`ForcingAtomicDenseTemplate.kernel_certificate` 也已通过同一检查，覆盖成员与相等的稠密性分支，在对象层生成较旧条件查询和实际稠密性码，并推出当前条件的原子结果。两项均已通过 Windows 整仓验收，共 3,375 项构建任务、40,030 项声明，零警告。见[本批验收](../verification/forcing-source-mono-and-atomic-density-acceptance.json)。

`ForcingSourceMono.atomic_kernel_certificate` 在 nativeZF 原推导核中覆盖成员与相等分支。原递归编译器的同一实际输出分别在两张条件覆写表上查询。证明从原预序行读出 `Pre`、`q ∈ P`、`q ≤ p`，与两份原子查询共用一张项像表，再在 `oldCtx 3` 下消去四层蕴含。见[原子分支验收](../verification/forcing-atomic-source-induction-acceptance.json)。

`NativeProofQuotation.from_derives` 已把固定的 nativeZF 原推导按六条 Hilbert 规则回放到原证明码。成员和相等的单调性复用 `ForcingAtomicBasic` 的既有证明。实际混合替换给出同一内部项像表与输出码时，`atomic_monotone_kernel_certificate` 在 nativeZF 中产生该输出的原证明节点，并在自由作用域为空时给出 `Root`。见[验收报告](../verification/native-proof-quotation-acceptance.json)。

负式与存在式的原构造码已推出 `ForcingSourceMono.atSource`。两支调用原编译总性和 `ForcingCodeUnary.unary`，并从同一 `ForcingGlobalWeakening` 输入生成弱化布局和两份覆写记录。预序行保留其空绑定表，父式在任意内部作用域生成绑定列，两者共用原来的自由底表。源条件的两份替换判断仍是输入。见[源构造分支验收](../verification/forcing-modal-source-induction-acceptance.json)。

## 已完成，必须复用

`InternalAxiomProof.from_native_quotation` 已覆盖七条固定公理及每个标准外部索引的分离和收集实例。`InternalProofTemplates.from_logical_quotation` 已覆盖 27 类逻辑公理。`ForcingAtomCode.member_output/equal_output` 已从原分派记录恢复同一字段的实际原子编译记录。

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. 将已验收的成员与相等分支接到统一实际密度查询，接完原 `ForcingTruth.force_of_dense` 的负式和存在式分支，并在全部内部公式码上闭合归纳。复用已通过原核检查的原子稠密性证书和单调性归纳。
2. 按原源依赖完成 neg／imp 内部证明生成和实际规范化强迫MP；已有固定公式数学与模式证书继续复用，不能用宿主实例代替全部内部码。
3. 接通全部内部／非标准ZF/U公理实例与完整六规则Proof保真，证明同一矛盾码的InternalConsistency.reduction，再取得goal。外部固定正文quotation模式不能替代此门。
4. 所有最终对象主句、量词、依赖及固定源对应验收满足后进入原第11阶段终验。

## 当前可核验材料

- [已验收裸R／完整canonical Global与实际forall消费](../verification/forcing-global-weakening-acceptance.json)：39719项声明，零警告，九命令及五项trust=0通过。
- [上一批全内部项像／公式比较](../verification/forcing-reindexed-images-acceptance.json)及[首槽相消](../verification/forcing-fresh-background-acceptance.json)。
- [Linux CI实际完成回执](../verification/ci-proof-universal-remote-acceptance.json)：远端613a6f0，39573项声明、零警告；后续提交CI以实际作业终态为准。

- [原源码合取单调性归纳分支](../verification/forcing-conjunction-mono-acceptance.json)：39728项声明，零警告；子公式归纳假设未消去，整体mono／Con未证明。

- [源公式码常元基例及合取步骤](../verification/forcing-source-mono-acceptance.json)：39739项声明，零警告；指定运行框架上的源子归纳假设保留，整体mono／Con未证明。

- [原字面双守卫与实际mode3／forall消费](../verification/forcing-nested-guard-acceptance.json)：39751项声明，零警告；完整新父公式查询匹配仍未证明。

- [新鲜三操作逆向及实际嵌套Root消费](../verification/forcing-fresh-opening-inverse-acceptance.json)：39774项声明，零警告；完整raw父查询到所需实例化记录仍未完成。
