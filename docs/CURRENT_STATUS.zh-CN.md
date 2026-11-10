# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

ForcingConjunctionMono.source_step 已消费原 CodeBinary.input 的父／两个子公式独立编译记录，取得实际父 AND 构造。transfer 将两个查询输出及子归纳假设保留为对象全称公式；derive 实际调用原 binary_output 两次，在对象层产生消去四个子输出，以原投影／chain／同背景 join 构造 SAME G 下的原 Root 条件证明。已有 join 仅去掉 private，正文原样；其余2886份旧证明Git正文、39719项旧依赖足迹全部保持。完整九命令／五项trust=0通过，39728项声明、零警告；16项兼容性测试及3个固定库／75哈希通过，见[原合取归纳分支验收](../verification/forcing-conjunction-mono-acceptance.json)。这是原 force_mono 的必要合取归纳分支；子归纳假设尚未由全内部归纳消去，不是整体单调性或最终Con。此前 SAME canonical Global 弱化及原 guarded forall 消费已完成，不再列为缺口。

## 已完成，必须复用

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. SAME canonical Global 弱化、Extra、裸R、q/p、四AND及原 guarded forall 消费现已完成；不要重做，也不再要求另造整个Global的双原查询路线。原 force_mono 的实际合取分支已接通；继续将其余必要分支和现有原子／neg／ex消费者接成全内部公式归纳，再接原 ForcingTruth.force_of_dense（60行）的Root证明生成；再依原源由 dense 导出 exists_force_neg（84行），由 neg／mono 导出 forceFormula_imp（121行）。复用现成公式码归纳、原子数学和证明操作，不增加新的归纳后端；随后规范化强迫MP、全内部ZF/U公理／六规则Proof、精确reduction及finalgoal。
2. 按原源依赖完成 neg／imp 内部证明生成和实际规范化强迫MP；已有固定公式数学与模式证书继续复用，不能用宿主实例代替全部内部码。
3. 接通全部内部／非标准ZF/U公理实例与完整六规则Proof保真，证明同一矛盾码的InternalConsistency.reduction，再取得goal。外部固定正文quotation模式不能替代此门。
4. 所有最终对象主句、量词、依赖及固定源对应验收满足后进入原第11阶段终验。

## 当前可核验材料

- [已验收裸R／完整canonical Global与实际forall消费](../verification/forcing-global-weakening-acceptance.json)：39719项声明，零警告，九命令及五项trust=0通过。
- [上一批全内部项像／公式比较](../verification/forcing-reindexed-images-acceptance.json)及[首槽相消](../verification/forcing-fresh-background-acceptance.json)。
- [Linux CI实际完成回执](../verification/ci-proof-universal-remote-acceptance.json)：远端613a6f0，39573项声明、零警告；后续提交CI以实际作业终态为准。

- [原源码合取单调性归纳分支](../verification/forcing-conjunction-mono-acceptance.json)：39728项声明，零警告；子公式归纳假设未消去，整体mono／Con未证明。
