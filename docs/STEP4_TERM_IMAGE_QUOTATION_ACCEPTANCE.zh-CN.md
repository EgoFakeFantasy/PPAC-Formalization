# 原项像quotation、实际环境与项操作验收

2026-10-23；S3.4c.2b.1。基点 d6c900ca686fc397971af3edb355d13e294171ab。
结论：本批项像环境、混合项替换及weakenBound逐模式数值对应已验收。
最终内部Con蕴含尚未证明；本报告只验收下述对象模式。

## 对象合同与实际结论

对象语言、背景和推导关系保持原约定：纯等词/成员语言ℒ，原nativeZF（完整Collection），
原YesMetaZFC FirstOrder.Derives。目标仍为ZF+PP+ACwo+¬AC，
最终要求 Derives nativeZF [] (Formula.imp Con_ZF Con_target)。
Con_T仍为¬∃p(p∈ω∧Proof_T(p,code⊥))，遍历全部内部ω证明码，保留六规则、27模式及完整Separation/Collection。

本批的外部模式参数是有限Tree、纯类型项及其有限列表、合法位置Fin和对应长度。
所有实际列表码、索引numeral的对象值、源项码与候选输出码都保留在对象语言中；
外部有限模式不覆盖模型中任意非标准公式AST或证明码，不能替代最终内部检查器正确性。

设Q_t(w,n)为原IntrinsicQuotation结构数值格式的项quotation，
Images(xs,w,L)为对应termTree森林的原quotation；不使用NatPacket字节码或旧quote_hilbert格式。
本批实际证明：

1. 原quotation森林在长度numeral下有原HasLength；在每个合法位置numeral下，原Field精确等价于对应子quotation。
2. 项像列表码实际存在、属于内部ω且唯一；其原长度和全域位置上的原Term类型均有对象推导。
   typedFields含全部内部i与候选q量词。以内部长度numeral的成员刻画消去有限位置分支，不从Lean模型中选择对象值。
3. 两份列表实际组成环境
   Env(bs,fs,w,a,b,c,d,R,S) = (Images(bs,w,R) ∧ Images(fs,w,S)) ∧ TermLists(w,a,b,c,d,R,S)。
   在准确源/目标长度numeral守卫下，∃R∃S Env以及实际唯一码对纤维均可推导；见证在对象∃E/∃I中构造、消去。
4. 对任意合法源变量模式及每个内部候选q，实际Env下的原混合项替换，
   精确等价于所选目标项像的Q_t(w,q)。源变量类别不限制像项的bound/free类别。
5. 在实际后继索引图U(c→C)与实际恒等图V(d→d)下，
   Renamed(w,U,V,c,d,C,d,n,q) ↔ Q_(t.weakenBound set)(w,q)。
   bound像索引取真实后继，free像索引由对角边保持；两种目标项均覆盖。
   反向使用原项重命名的实际总性、原quotation唯一性及对象等词传输，实际输出见证已消去。

未把Env存在性加强为目标长度守卫的双条件：合法项也可能适配更大的目标上下文，
所以本批只在指定长度下证明实际存在，不声称该长度守卫是必要条件。
空项像列表、空上下文保留原递归基例；合法位置Fin为空时不存在外部索引实例。
未引入外部ω标准性、外部良基、深度上界、模型假设或宿主集合见证选择。

## 文件与证书

| 单元 | 文件 | 已验收结果 |
|---|---|---|
| 原quotation字段 | OriginalQuotationValue、OriginalQuotationForestRead、OriginalQuotationForestLength | 输出等词、精确字段、实际长度 |
| 项像列表 | TermImageQuotationSyntax、TermImageQuotationFields、TermImageQuotationTyping | 原森林码、存在唯一、TermLists与全内部字段类型 |
| 实际双表环境 | TermQuotationEnvironmentSyntax、TermQuotationEnvironment | 实际存在、唯一码对及纤维 |
| 混合项替换 | TermQuotationSubstitution | 有/无显式源索引见证的精确quotation双条件 |
| 绑定变量提升 | TermQuotationShiftFields、TermQuotationShift | 两类项像的实际图边推导与weakenBound双条件 |
| 原核封装 | ObjectTermImageQuotation | 19组Source闭句、sourceZF证书、nativeZF证书 |

上述文件均位于PPAC/Migration/Internal/。新增12模块、120个显式声明。
封装路径固定为source闭句→TheoryTransport.sentence→ZFReplay.replay；
返回原FirstOrder.Derives nativeZF []，没有另建推导核、模型语义或完备性捷径。
例如native_environmentFiber、native_mixedTerm、native_shiftTerm分别是环境、替换和提升的原核入口。

## 实际验收

执行 C:\Python314\python.exe -X utf8 scripts/verify.py，退出0。
独立执行.local/verify-term-image-readback.py，退出0；本地证据为verification/term-image-readback.json。

| 验收项 | 实际结果 |
|---|---|
| 串行严格全仓构建 | lake --wfail build；1105任务通过；LEAN_NUM_THREADS=1 |
| 声明依赖审计 | 12322项，329无公理依赖、11993符合记录依赖，0警告 |
| 命令与原核检查 | 9命令全部退出0，其中5个--trust=0入口全部退出0 |
| 新闭句精确依赖 | 19组core=std3、native=std3+原7证书，逐项相等 |
| 累计闭句精确依赖 | 1312对逐项核验 |
| Internal显式声明覆盖 | 9978项全部进入审计 |
| 源码/脚本独立回读 | 1003份SHA256全部一致 |
| 七锁文件 | 相对本批基点全部不变 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，工作区干净 |
| 禁用缺口/新公理审查 | 活动源码无sorry/admit/axiom/unsafe/native_decide；未关闭linter |

std3={propext,Classical.choice,Quot.sound}，原7证书的精确基线见TRUST_BASELINE.json。
没有扩大已有独立Choice桥依赖范围；Prop中的经典等式证书不等于对象ZF加入AC。
未运行原OpenAI全构建或Comparator，未推送或创建PR；verification和.local是本地证据，不作为发布材料。

## 后续工程与尚未完成范围

| 顺序 | 输入与实现动作 | 必须交付与验收 | 当前状态 |
|---|---|---|---|
| S3.4c.2b.1 | 本批实际项像码、原字段及两类图 | 混合项quotation、两类weakenBound、原核闭句与全审计 | 已验收 |
| S3.4c.2b.2a | 实际CodedMixedBinder与本批项提升 | 实际提升双表的quotation对应，内部取得并消去U/V/head；源bound零槽和后继槽、源free槽均精确 | 待完成 |
| S3.4c.2b.2b | 真实双表binder、原全11公式端点 | 完整混合公式与首槽操作的原quotation对应，嵌套量词保持两类像；实际消去子码见证 | 待完成 |
| S3.4c.2b.2c | 原数值递归规格与合法输入判断 | 任意内部有效AST上的原操作统一正确性，准确拒绝无效候选；不以标准quotation模式代替 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 六规则中规则5/4的任意内部码检查兼容 | 待完成 |
| 5a/5b | 六规则、27模式、全ZF/U公理 | 专用ProofZF/U有限纯AST、全内部ω检查/编译正确性 | 待完成 |
| 6a | 原数学解释路线与对象递归 | 完整内部解释及目标ZF、PP、ACwo、¬AC的原核推导 | 待完成 |
| 6b | 内部解释、检查器与内部Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

上述后续总门在verify.py中继续为False；本批四个细门仅表示报告中的具体对象模式已证明。
