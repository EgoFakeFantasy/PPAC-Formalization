# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

ForcingNestedGuardProof 已把 canonical 上下文中的 Global AND(M AND O) 实际 Tail 证明恢复为原编译器字面 M→(O→Tail)。复用原 and_exists 内部产生消去两个重排 AND 码，原投影／join／chain 导出新上下文证明，并实际调用现成 Curry.twice 产生两个嵌套正文码。随后实际消费 FreshBackground.derive、原 mode3 存在和 unchanged generalize_body／guarded forall，三个正文／抽象输出见证保留在对象EX3内。from_global 直接读取同一 Global.data 的实际弱化、元数据和旧Global类型；无需另给弱化或抽象答案，也不再要求此前单Local正文的mode3记录。输入还保留实际Context.resultData和Tail类型元数据，不假定守卫为真。两个普通 nativeZF 闭句及完整九命令／五项trust=0通过，39751项声明、零警告；39739项旧足迹及2888份其他旧证明Git正文保持，原and_exists仅去掉private、正文精确保留；16项兼容性测试与3个固定库／75哈希通过，见[字面双守卫验收](../verification/forcing-nested-guard-acceptance.json)。原第10阶段继续：完整新父公式实际查询与生成全称码的最终识别、原子模板的内部Root实例化与全内部源归纳、dense／neg／imp、全部公理／Proof／reduction／最终Con尚未证明；未宣称整个neg／ex单调性完成。源常元无IH基例及内部产生两个子编译结果的源合取步骤此前已验收，不重做。

## 已完成，必须复用

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. SAME canonical Global 弱化、Extra、裸R、q/p、四AND及原 guarded forall 消费现已完成；不要重做，也不再要求另造整个Global的双原查询路线。原 force_mono 的假／真常元基例与源合取步骤已接通，两个子编译结果由原总性内部产生；字面双守卫的实际mode3／forall生产现也完成；继续识别完整新父公式的实际查询，接通原子模板的内部Root实例化与实际源消费者，完成全内部公式归纳，再接原 ForcingTruth.force_of_dense（60行）的Root证明生成；再依原源由 dense 导出 exists_force_neg（84行），由 neg／mono 导出 forceFormula_imp（121行）。复用现成公式码归纳、原子数学和证明操作，不增加新的归纳后端；随后规范化强迫MP、全内部ZF/U公理／六规则Proof、精确reduction及finalgoal。
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
