# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

ForcingMemberRows.produce 已实际消去两侧原 LeafTarget.instances 的6／10／5／3层存在块，分别调用现成 MemberWeakening.from_rows 取得 q1、p2 的原成员叶 weakened；两份完整实际叶记录及全部48个原见证在同一对象存在输出中保留。输入为已经产生的原实例记录、原项像及实际 q/p 项重命名，未给定叶记录、载体字段、成员码或弱化答案，也不要求 fresh r 相同。原 LeafTarget 只开放三个既有正文定义，所有证明正文原样。普通 nativeZF 原核闭句、九命令及五项trust=0通过，39699项声明、零警告；原39678项依赖及2883份其他旧证明Git源码保持，见[验收回执](../verification/forcing-member-rows-acceptance.json)。裸R／Extra／完整canonical Global和最终Con仍未完成。

## 已完成，必须复用

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. 两侧实际原存在叶记录的 q/p 成员比较已由 ForcingMemberRows.produce 完成，48个见证及两份完整原行保留；native到叶展开、fresh实际接线、成员比较不再列为待办。下一步读取裸R(q,p)的实际 H4 查询，优先复用 ForcingRelationRawFormula.from_prefix（leaf1／raw14）、原 ForcingRelationSource／ForcingRelationImages 生产器及已完成的 WeakenedOverwrite.from_double_queries；随后处理 Extra 与四AND 的 SAME canonical Global，接入现成 ProofContext／FreshBackground／ProofUniversal。
2. 完成原force_mono／force_of_dense／exists_force_neg／forceFormula_imp联合内部码归纳及规范化强迫MP；普通字面蕴含组合或外层实例不能替代此门。
3. 接通全部内部／非标准ZF/U公理实例与完整六规则Proof保真，证明同一矛盾码的InternalConsistency.reduction，再取得goal。外部固定正文quotation模式不能替代此门。
4. 所有最终对象主句、量词、依赖及固定源对应验收满足后进入原第11阶段终验。

## 当前可核验材料

- [本批源弱化与实际forall消费](../verification/forcing-weakened-images-acceptance.json)：39632项声明，零警告，九命令及五项trust=0通过。
- [上一批全内部项像／公式比较](../verification/forcing-reindexed-images-acceptance.json)及[首槽相消](../verification/forcing-fresh-background-acceptance.json)。
- [Linux CI实际完成回执](../verification/ci-proof-universal-remote-acceptance.json)：远端613a6f0，39573项声明、零警告；后续提交CI以实际作业终态为准。

本批成员叶实际源记录传输已完整验收：见[验收回执](../verification/forcing-member-weakening-acceptance.json)。39668项声明、零警告，九命令及五项trust=0通过；原39658项依赖和2882份旧证明Git正文保持。最终内部Con仍未证明。
