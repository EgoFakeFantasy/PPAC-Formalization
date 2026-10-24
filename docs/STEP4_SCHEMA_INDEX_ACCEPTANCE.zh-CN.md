# 三处schema指标嵌入、实际码表及全内部公式重命名验收（2026-10-25）

本批完成T1.2b：原Separation／Collection所需三处指标嵌入具有实际对象图、准确作用域、完整自然列表码和全内部纯公式的唯一重命名输出。13个新模块、155项显式声明、15组闭句经原sourceZF推导传入原nativeZF。本批完整验收数据见下文。

Project十二构造正文到纯十一构造的内部转换、完整schema公理测试、专用Proof_T、内部解释与最终Con仍未证明。

## 对象语言、背景与最终目标

对象语言为纯等号／成员；背景保持Contract.nativeZF及其完整Separation／Collection模式；推导关系保持YesMetaZFC.Logic.FirstOrder.Derives。最终规格仍为：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式及完整理论公理模式。以上仍是最终规格；实际完整Proof_T及最终蕴含尚未构造并证明。编译成功和宿主编码元数据不替代对象推导。

## 实际三处图

n为对象槽，四个作用域a1至a4满足真实对象后继链Succ(a1,n)、Succ(a2,a1)、Succ(a3,a2)、Succ(a4,a3)。没有把n改成外部Nat或只处理外部标准码。

| site | 原BoundEmbedding | 源／目标作用域 | 内部图构造 | 保留首槽／参数尾部 |
|---|---|---|---|---|
| 0 | unaryUnderTwo | a1→a3 | Shift2的单次binder提升 | 0固定；i+1映到i+3 |
| 1 | binaryUnderOne | a2→a3 | Shift1的两次binder提升 | 0、1固定；i+2映到i+3 |
| 2 | binaryUnderTwo | a2→a4 | Shift2的两次binder提升 | 0、1固定；i+2映到i+4 |

Shift1来自原完整后继图；Shift2由两张实际Shift1图及完整原复合图构造。所有中间图在对象EX内取得并消去。每次binder提升使用独立、真实的源／目标后继，而非仅修改宿主Fin函数。

首槽规律对全部候选输出成立：Empty(z)时Edge(g,z,y)↔Empty(y)；两处Collection另有Num1(p)时Edge(g,p,y)↔y=p。第二首槽唯一性由实际完整图的functionOn取得。

尾部规律中的i∈n、i/u/I和j/v/J均为对象槽及真实Succ关系：Separation把一次前移后的尾部边精确归约到Shift2；Collection把两次前移后的尾部边精确归约到Shift1／Shift2。它们覆盖任意内部参数指标，不要求它来自外部AST quotation。

SchemaIndexSites中另逐项核对原三个BoundEmbedding及其作用域算术。这些是宿主元数据对应；对象正确性由上述完整图及首槽／尾部原推导承担。

## 真实码表和最终接口

~~~text
state(site,w,n,a,g) = Chain(n,a) ∧ Graph(site,w,n,a,g)
codedState = state ∧ Encoded(w,g,sourceScope(site,a),targetScope(site,a),R)
Law = ∀A (FormulaCode(w,A,sourceScope(site,a),z) →
          ∃!B Renamed(w,R,S,sourceScope(site,a),z,targetScope(site,a),z,A,B))
System = codedState ∧ IdentityCode(w,z,S) ∧ Law
ExistsSystem(site,w,n,z) = ∃a1,a2,a3,a4,g,R,S System
~~~

Encoded使用原完整自然列表码；IdentityCode为实际自由码表。Renamed是原全十一构造判断，包含输出FormulaCode类型，不是新设的正确性前提。输入A及所有候选输出B在对象量词内，合法输入包括全部内部码。

核心出口：

~~~text
nativeZF ⊢ close(Ω(w) → n∈w → Empty(z) → ExistsSystem(site,w,n,z))
~~~

site:Fin3只选择三种有限公式模式；n、作用域、图、列表码和公式码均是对象数据。最终出口仅有Ω、内部参数个数和Empty三项前提。四个作用域、最终图、bound码、free码都在结论EX内；不存在假定图、码表、IH、Promise或模型可靠性的残留前提。

本批的15组源闭句均先通过TheoryTransport.sentence取得sourceZF原核证书，再由ZFReplay.replay传至原nativeZF。它们是schema正文翻译所需的辅助定理，尚未形成完整公理测试。

## 模块和审核范围

| 模块 | 已证明内容 |
|---|---|
| SchemaDoubleShiftSyntax／Point／Graph | 两次位移、实际复合、完整边律、图唯一及存在 |
| SchemaIndexSyntax／GraphExistence | 三处真实binder图、各源／目标作用域及图存在 |
| SchemaIndexFacts／Tail／Head | 完整indexMap、首两槽及任意内部参数尾部规律 |
| SchemaIndexScopes／Coded | 四次对象后继见证、完整图和原自然列表码存在 |
| SchemaIndexRenameSystem | 全内部公式唯一重命名；实际free身份码；最终EX7系统 |
| SchemaIndexSites | 对照原BoundEmbedding的有限元数据 |
| ObjectSchemaIndex | 15组source／sourceZF原核／nativeZF闭句 |

新增显式声明逐一#print axioms并接入全仓覆盖。新15组core精确依赖propext、Classical.choice、Quot.sound；native精确再继承既定七项固定公理证书。没有继承Choice固定证书或加入新公理；Lean的Classical.choice是既定宿主证明依赖，不能据此把对象ZF改为ZFC。

## 实际验收

- 全仓2007构建任务通过，零警告；九命令及五个--trust=0入口全部退出0。
- 21824项声明审计：433项无公理、21391项仅有记录中的允许依赖。155项新增显式声明全部覆盖。
- 1790份文件SHA256独立回读一致；累计2446对闭句core／native精确足迹一致；19480项Internal显式声明全覆盖。
- 七份锁定文件保持原值；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净。
- 既有PPAC证明及AST保持原Git字节；完整schema测试、Proof／解释及最终Con门禁保持false。


此前跟踪的PPAC证明及AST保持Git字节。本批仅13个新模块、4个接入文件及6份文档。验收前基点7ac1bb773061bc1f21707b0cca2562735e3747ca；本地证据verification/{summary.json,commands.json,build.log,audit.log,schema-index-readback.json}。复验命令：C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

## 清理回读

完整编译前确认无残留Lean／Lake进程，停止失效进程0。只删除4份已被成功定向编译替代的失败日志，逐项记录SHA256并删除回读：逻辑删除14711字节；盘面实测增加344064字节，该测量含系统并发活动，不能等同于日志占用。有效源码、构建缓存、有用生成与回读脚本均保留。收据.local/workspace-cleanup-schema-index-result.json。

## 修订后的agent工程表

| 单元 | 精确输入／动作 | 必须交付的对象接口和验收 | 状态 |
|---|---|---|---|
| T1.2a | 任意内部次数、原tag9构造及ω递归 | 真实forallClosure、n+b→b准确类型、唯一闭输出 | 已验收，前批 |
| T1.2b | 三处原BoundEmbedding、真实后继和完整图／列表码 | 三图首槽／尾部、准确作用域、EX7实际系统及全内部公式唯一重命名；原nativeZF闭句 | 本批验收 |
| T1.2c | 原Project十二构造正文及实际数值证书码 | 内部12→11编译关系；mem补原关系标签，原等号保持primitive equal，subset展开∀／→／∈并准确提升bound；归纳消去IH与全部见证 | 下一步 |
| T1.2d | T1.2a闭合、T1.2b重命名、T1.2c正文 | 原Separation／Collection完整模板及实际原Horn条件双向对应；准确行／包码；全部内部schema测试 | 未完成，门禁false |
| T1.3 | 固定7+3部分测试和完整schema测试 | ZF／目标理论共享准确内部公理测试与实际Bool方程；排除Choice误入ZF | 未完成 |
| T2 | 原证明树方程、全六规则／27模式及T1.3 | 专用Proof_ZF／Proof_target、全部内部证明码正确性及编译传输 | 未完成 |
| T3 | 目标数学解释、相对一致性路线和T2 | 原nativeZF内解释正确性、最终内部Con蕴含；全量验收及公理审计 | 未完成 |

每个单元先固定对象AST和最终前提，再写原核推导；独立核对完整量词、全部内部候选、准确原规则和公理足迹。Lean／Lake串行；保留其他脏改动；完整检查通过后才提交该单元。禁止用外部标准quotation实例、语义模型结论或成功构建替代下一单元的内部证明。
