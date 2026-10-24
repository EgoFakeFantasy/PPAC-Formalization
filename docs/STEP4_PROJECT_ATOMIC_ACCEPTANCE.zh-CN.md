# Project原子正文内部编译、subset展开及绑定项提升验收（2026-10-25）

本批完成T1.2c.1：原Project成员／等号／subset三类原子从结构树源码到纯十一构造码的内部转换。全部内部绑定索引、作用域、项码、输入和候选输出保持对象量词；15组闭句返回原nativeZF。16个新模块、147项显式声明。

完整十二构造正文编译、递归公式IH消去、所有schema证书的NatPacket字节包／结构树桥、完整schema公理测试、专用Proof、内部解释及最终Con均未完成。三原子出口不能替代它们。

## 背景和最终验收口径

对象语言仍是纯等号／成员ℒ；背景仍为Contract.nativeZF及完整Separation／Collection；使用原YesMetaZFC.Logic.FirstOrder.Derives。最终目标未缩小：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

完整Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式及完整公理模式。上述主句仍待实际构造和推导；宿主数据、语义结论及本批编译成功均不代替它。

## 绑定项提升

~~~text
Shift(w,x,y) = ∃i,j (BoundCode(w,i,x) ∧ Succ(j,i) ∧ BoundCode(w,j,y))
~~~

内部解码给出真实自然索引；Ω给出真实后继，再构造提升项码。源索引、后继和码见证全部取得并消去。

- Ω及BranchBound(w,b,x)推出存在唯一自然y满足Shift(w,x,y)。
- 对全部内部候选y、q，Shift(w,x,y)与Shift(w,x,q)推出y=q；没有预设输出自然守卫。
- 若b、f∈w且Succ(B,b)，则BranchBound(w,b,x)与Shift(w,x,y)推出Term(w,B,f,y)。B是实际对象后继，b没有换成外部Nat。

唯一性链为原变量索引解码唯一性、实际后继外延唯一性、实际变量编码唯一性；相等传输使用原eqSubst规则。

## 原三类源码及输出

~~~text
SourceAt(kind,w,b,x,y,n) =
 b∈w ∧ BranchBound(w,b,x) ∧ BranchBound(w,b,y) ∧
 Constructor(2,SourceTag(kind),w,[x,y],n)
SourceTag(0)=2; SourceTag(1)=3; SourceTag(2)=11
Compiled = SourceAt ∧ Result
~~~

SourceAt是独立的三原子源码形状与范围条件，不是把目标类型或编译成功改名为输入合法性。kind:Fin3只选择有限公式模式；所有码值及作用域都是对象槽。

| 原Project原子 | 源结构树 | 纯输出结构树 | 实际已证 |
|---|---|---|---|
| mem | tag2，[x,y] | tag2，[关系scalar0,x,y] | 关系叶和三字段码实际构造，唯一且准确类型 |
| extensionalEq | tag3，[x,y] | tag3，[x,y] | primitive equal；输出q与源n对象相等 |
| subset | tag11，[x,y] | forall9(imp7(mem2(0,bound0,shift(x)),mem2(0,bound0,shift(y)))) | 实际提升、所有中间码、准确量词作用域及唯一输出 |

关系scalar0是原编码叶，不是对象集合零；二者没有混用。ProjectAtomicData.source_encoding另外逐项核对原ZFC.ProjectEncode的源标签及两字段顺序；这是外部有限元数据，不是完整内部Project AST编译正确性证明。

## subset的真实构造

Expanded关系在对象EX8内保存B、X、Y、V、S、L、R、P：

~~~text
Succ(B,b) ∧ Shift(w,x,X) ∧ Shift(w,y,Y) ∧ BoundCode(w,z,V) ∧ ZeroScalar(w,S)
 ∧ MemberCode(w,S,V,X,L) ∧ MemberCode(w,S,V,Y,R)
 ∧ BinaryCode(imp,w,L,R,P) ∧ SingleCode(forall,w,P,q)
~~~

Empty(z)提供真正对象零，V是实际bound0项码，S为关系scalar0。实际B与两张Shift保证提升后项处于B；原Member类型律、Imp类型律及精确量词后继类型律给出FormulaCode(w,q,b,z)。候选输出的唯一性先比较提升项和叶，再沿两个Member、Imp、Forall构造传播相等，覆盖全部内部候选。

B、X、Y、V、S及L、R、P、q分别在实际存在性推导内构造；原EX规则消去全部见证。没有保留假定码、IH、Promise、宿主可解码或模型可靠性前提。

固定槽位装配独立为ProjectSubsetAssembly；准备和四个输出构造用命名接口连接。原先大项在Fin槽位推断时触发elaboration预算，现已结构化解决；最终源码没有增加maxHeartbeats或关闭linter／内核检查。

## 最终对象出口

~~~text
nativeZF ⊢ close(Ω(w) → Empty(z) →
  ∀b,x,y,n (SourceAt(kind,w,b,x,y,n) →
    ∃q (q∈w ∧ Compiled(kind,w,b,z,x,y,n,q) ∧ FormulaCode(w,q,b,z)
        ∧ ∀r (Compiled(kind,w,b,z,x,y,n,r) → r=q))))
~~~

实际fiber的合取括号见ProjectAtomicSyntax。这里只量化三类原子，不能宣称完整十二构造正文已经完成。输入及输出不必是外部AST的标准quotation。

15组闭句依次通过TheoryTransport.sentence及ZFReplay.replay取得原sourceZF／nativeZF证书。新core精确依赖既定propext、Classical.choice、Quot.sound；native精确再继承原七项固定证书，没有加入对象Choice证书或新增公理。

## 实际验收

- 全仓2023构建任务通过；九命令及五个--trust=0入口均退出0，零警告。
- 21971项声明审计：436项无公理、21535项仅有记录中的允许依赖；147项新增显式声明全部覆盖。
- 1806份文件SHA256独立回读一致；累计2461对闭句core／native精确公理足迹一致；19627项Internal显式声明全覆盖。
- 七份锁定文件未变；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净。
- 既有PPAC证明及AST保持原Git字节；全十二构造编译、完整schema测试、Proof／解释及最终Con门禁均保持false。

此前跟踪的PPAC证明及AST保持Git字节。本批仅16个新模块、4个接入文件及6份文档。验收前基点47287ecf1d4061178893f50401f7f3075f24b562；本地证据verification/{summary.json,commands.json,build.log,audit.log,project-atomic-readback.json}。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

## 清理

完整验收前确认无残留Lean／Lake进程，停止失效进程0。按单文件白名单删除7份失效日志、2份已退役性能探针文件和1份无用空生成脚本，共10项、逻辑删除29347字节；盘面实测差额-32768字节，包含系统并发活动。逐项保存SHA256并删除回读；有效源码、构建缓存及有用生成／回读脚本保留。收据.local/workspace-cleanup-project-atomic-result.json。清理后才启动完整串行验收。

## 后续agent工程表

| 单元 | 输入和工作 | 对象交付／验收 | 状态 |
|---|---|---|---|
| T1.2a | 原内部tag9及真实ω递归 | 任意内部次数全称闭合、n+b→b准确类型及唯一闭输出 | 前批已验收 |
| T1.2b | 三处原BoundEmbedding | 实际完整图／列表码、首槽／尾部及EX7全内部重命名系统 | 前批已验收 |
| T1.2c.1 | 原成员、primitive equal、subset源码结构 | 实际bound项提升；三原子唯一准确类型输出；对象ALL4及原nativeZF闭句 | 本批验收 |
| T1.2c.2 | 原完整Project十二构造及独立源语法判断 | 常量及逻辑／量词子式递归、准确binder作用域；内部集合递归存在唯一及完整源类型／输出类型对应；消去全部内部IH | 下一步，未完成 |
| T1.2c.3 | 原ProjectEncode及其实际数值证书载荷 | 结构码编译与实际NatPacket字节包、原Horn查询精确对应，覆盖全部内部候选 | 未完成 |
| T1.2d | 正文、三处重命名、内部次数闭合 | 完整Separation／Collection模板、实际原条件双向对应及准确公理测试 | 门禁false |
| T1.3／T2 | 固定7+3部分测试及T1.2d、原六规则／27模式 | 共享实际Bool与专用Proof_ZF／Proof_target；全内部证明码编译传输 | 未完成 |
| T3 | T2及完整数学解释 | 原nativeZF内解释正确性及内部Con蕴含，全量验收 | 未完成 |

继续实现完整正文编译，不能用本批三个固定模式、源码元数据、标准quotation实例或类型结论替代全十二构造统一对象推导。每批串行构建、精确审计与独立回读；完整目标门禁继续为false。
