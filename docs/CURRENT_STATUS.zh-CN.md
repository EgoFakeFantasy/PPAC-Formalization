# 当前工作入口（2026-11-11）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

存在分支的实际 fresh 父开口现已接到原 Root 消费者。ForcingRawModalBody 读取原编译外层两条蕴含，在同一预序记录上生成载体并证明成员对应 H0、关系 R(r,q) 对应 H3；用已有 raw 尾部比较定理将实际尾部和旧执行对齐，再由原构造唯一性转移嵌套证明。普通 nativeZF 原核闭句通过全仓验收，39868 项声明、零 Lean 警告。该闭句仍需要旧执行的尾部查询与规范嵌套证明、原编译字段和共享预序记录。负式已读出三条实际查询，尾部对齐待做。见[实际存在父开口 Root 验收](../verification/forcing-raw-modal-body-acceptance.json)。

## 已完成，必须复用

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. 存在分支已将实际新父开口的三个叶子接到原 Root。下一步将旧尾部查询与规范嵌套证明接入同一编译记录，完成存在步骤装配；负式复用现有条件重绑定和原字段定理完成实际尾部对齐，然后合并两支和已验证基例、合取及原子端点，完成全部内部码的 force_mono。 后续按原 ForcingTruth.force_of_dense、exists_force_neg、forceFormula_imp 的依赖顺序推进。
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
