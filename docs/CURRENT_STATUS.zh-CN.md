# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

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

1. 接完原 `ForcingTruth.force_of_dense` 的常元、合取、负式和存在式分支，并在全部内部公式码上闭合归纳。复用已通过原核检查的原子稠密性证书和单调性归纳。
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
