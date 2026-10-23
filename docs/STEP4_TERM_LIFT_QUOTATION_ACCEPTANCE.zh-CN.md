# 原混合binder与整张提升项像quotation验收

2026-10-23；S3.4c.2b.2a。基点bb4454b5f0f765bb4ddffe77b90eab46233ca302。
本批完成实际提升双表的对象quotation对应、双向刻画及实际联合唯一纤维。
最终内部Con蕴含仍未证明；本报告不把逐外部模式结论提升为任意内部AST统一操作正确性。

## 固定对象合同

对象签名仍为原YesMetaZFC的纯等词/成员语言ℒ；背景为原nativeZF（完整Collection）。
推导固定原FirstOrder.Derives，封装产生原Hilbert推导证书，没有新核、模型前提或完备性捷径。
最终目标仍是 Derives nativeZF [] (Formula.imp Con_ZF Con_target)，target=ZF+PP+ACwo+¬AC。
内部Con仍要求¬∃p(p∈ω∧Proof_T(p,code⊥))，遍历全部内部ω证明码，保留六规则、27模式及完整Separation/Collection。
本批没有新增或改变对象公理，也没有恢复退役反射实现。

## 已证明的对象结论

bs、fs是目标上下文(bound,free)中的外部有限纯项像列表。
shifted(xs)=xs.map(t↦t.weakenBound set)，newBound(bs)=bvar0::shifted(bs)。
这两份列表只是对象模式索引；每个列表码和所有候选输出仍是内部对象变量。

设Env为前批已实际构造的原项像quotation环境，Lifted为原CodedMixedBinder.lifted。
在如下对象守卫下：

- Omega(w)；Num(|bs|,a)、Num(|fs|,b)、Num(|bound|,c)、Num(|free|,d)；
- Env(bs,fs,w,a,b,c,d,R,S)；Succ(A,a)、Succ(C,c)；

对每个内部输出码对K,H，原核证明精确双条件：

Lifted(w,R,S,a,b,c,d,A,C,K,H)
↔ Env(newBound(bs),shifted(fs),w,A,b,C,d,K,H)。

最终双条件不残留后继图U、恒等图V、新头部零/项码、旧像项码或前驱索引的存在/正确性假设。
这些见证在对象∃E/∃I中实际取得、消去，未从Lean模型抽取集合值。
中间at_witnesses/at_maps仅为分层证明入口；最终environmentAtLifted和liftedIffEnvironment已消去相应辅助前提。

同时实际构造同一对内部K,H，联合满足Lifted和上述整表Env，并证明：
∀U∀V(Lifted(w,R,S,a,b,c,d,A,C,U,V)→K=U∧H=V)。
唯一性比较所有内部原lifted候选，不仅比较额外满足quotation的候选。
原提升后环境自身也取得实际唯一码对纤维。

## 证明中已消去的具体义务

| 单元 | 实际对象推导 | 边界 |
|---|---|---|
| 全字段读取模式 | 每个外部合法位置j对应∀i∀q(Num(j,i)→(Field↔Qterm))，再取有限纯合取readings | 模式有限；i、q为全部内部候选 |
| 整表恢复 | HasLength、长度numeral和readings推出全内部字段agree，与实际存在的原quotation表比较，以原列表码单射性恢复整表quotation | 不假设列表码外部标准或用宿主解码 |
| 新零头 | 对齐实际空集索引与候选Num0索引，原bvar0码给出精确头部quotation | 索引相等在对象Extensionality内证明 |
| bound后继槽 | 内部解包后继numeral，实际取得旧像项码，由源Field接到原Renamed及前批weakenBound quotation | 旧项码和前驱索引均消去 |
| free槽 | 源free索引保持，旧目标项像的bound分量仍提升；精确目标quotation由原Renamed给出 | 不把free源误认为只能映到free目标 |
| 全表输出 | 原输出TermLists提供真实HasLength，所有位置字段读取及内部长度恢复K/H两张quotation | 空列表/空上下文保留原基例 |
| 实际辅助设施 | 原ZF核取得完整后继图、恒等图、实际bvar0头并消去四个对象见证 | 最终环境对应无U/V/head前提 |
| 反向对应 | 原binder实际存在输出→正向得到其Env→原Env唯一码对→对象等词传输 | 不假定待证明反向存在性 |
| 实际联合纤维 | 同一K/H满足原binder、整表quotation和针对全部lifted候选的唯一性 | 无未来总性/字段对应假设 |

外部Fin只指定有限模式中的位置，不选择内部对象值；没有ω外部标准性、外部良基或深度上界假设。
数值格式保持原IntrinsicQuotation结构树/森林，未混用NatPacket字节传输或旧quote_hilbert格式。

## 文件及原核入口

新增文件均位于PPAC/Migration/Internal/，共11模块125显式声明。

| 模块 | 职责 |
|---|---|
| TermImageReadingSyntax、TermImageReading | 有限全称字段AST、实例读取、完整内部字段一致性与整表quotation恢复 |
| TermQuotationBinderFields、TermQuotationBinderValues | 零/后继/free精确字段，消去实际旧项码及前驱索引 |
| TermQuotationLiftSyntax、TermQuotationLiftReading | 纯项提升列表模式与整表读取证明 |
| TermQuotationLiftEnvironment | 有见证、有图、无辅助见证三层整表环境证明 |
| TermQuotationLiftCorrespondence | 对象等词输出传输、反向对应、双条件、实际环境唯一纤维 |
| TermQuotationLiftJointSyntax、TermQuotationLiftJoint | 实际联合状态AST及联合唯一纤维 |
| ObjectTermLiftQuotation | 20组Source闭句、原sourceZF证书及原nativeZF证书 |

主要原核入口为native_environmentAtLifted、native_liftedIffEnvironment、native_jointFiber。
证书路线为source闭句→TheoryTransport.sentence→ZFReplay.replay，返回原FirstOrder.Derives nativeZF []。

## 实际验收

执行 C:\Python314\python.exe -X utf8 scripts/verify.py，退出0。
独立执行.local/verify-term-lift-readback.py，退出0；本地证据为verification/term-lift-readback.json。

| 验收项 | 实际结果 |
|---|---|
| 串行严格全仓构建 | lake --wfail build，1116任务通过，LEAN_NUM_THREADS=1 |
| 声明依赖审计 | 12447项；333无公理依赖、12114符合记录依赖；0警告 |
| 命令与原核检查 | 九命令全部退出0，其中五个--trust=0入口全部退出0 |
| 新闭句精确依赖 | 20对core=std3、native=std3+原7证书，逐项相等 |
| 累计闭句精确依赖 | 1332对逐项核验 |
| Internal显式声明覆盖 | 10103项全部审计 |
| 独立源码/脚本SHA256回读 | 1014份全部匹配 |
| 七锁文件 | 相对本批基点全部不变 |
| YesMetaZFC固定底座 | 039c8e132cc19671d73a3933c66b4799d2599dd6；依赖工作区干净 |
| 缺口及额外公理审查 | 活动源码无sorry/admit/axiom/unsafe/native_decide；未关闭linter |

std3={propext,Classical.choice,Quot.sound}；原7证书精确基线见TRUST_BASELINE.json。
独立Choice桥保持原范围；宿主Prop经典等式证书不表示对象ZF加入AC。
新源码统一LF；旧基点文件保留既有换行，哈希指工作区精确字节，提交blob换行差异另作本地记录。
没有推送/PR；未运行原OpenAI全构建或Comparator。verification与.local证据保持本地。

## 后续工程流程

| 顺序 | 下一步输入与动作 | 必须交付与验收 | 状态 |
|---|---|---|---|
| S3.4c.2b.2a | 本批原binder与项像整表 | 精确双条件、内部消去U/V/head、实际联合唯一纤维及原核闭句 | 本批已验收 |
| S3.4c.2b.2b | 原11公式端点、本批提升Env、纯类型变量替换 | 全11构造的混合公式quotation；量词下递归到实际提升表；首槽实例化/抽象对应 | 待完成 |
| S3.4c.2b.2c | 原数值程序/递归规格与合法AST判断 | 任意内部有效AST统一操作正确性及准确无效候选处理，不以标准quotation实例代替 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 规则5/4在任意内部码上的精确检查兼容 | 待完成 |
| 5a/5b | 六规则、27模式及全ZF/U公理 | 专用ProofZF/U有限纯AST、全部内部ω上的检查/编译正确性 | 待完成 |
| 6a | 原数学解释路线与对象递归 | 完整内部解释及目标ZF、PP、ACwo、¬AC的原核推导 | 待完成 |
| 6b | 内部解释、检查器、锁定Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

verify.py仅新增三个精确细门；全内部原操作、完整公式/首槽、专用检查器与最终Con总门继续为False。
