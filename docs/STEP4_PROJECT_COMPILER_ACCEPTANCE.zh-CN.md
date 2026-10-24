# Project实际编译器递归系统、父证书及基分支执行验收（2026-10-25）

本批构造独立于目标类型正确性假设的实际十二分支编译关系，证明真实分离状态／原递归图存在唯一，并将两个常量和三类原子接入实际产出关系。27个新模块、268项显式声明、20组闭句返回原nativeZF。

完整输入到唯一准确类型输出的内部归纳尚未完成。递归状态／求值集合唯一不等于每个源公式只有一个目标码；本批不能据此宣称全十二构造编译正确、完整schema测试、Proof／解释或最终Con完成。

## 背景与完整目标

纯等号／成员ℒ，背景仍是Contract.nativeZF及完整Separation／Collection；推导仍为原YesMetaZFC.Logic.FirstOrder.Derives。最终规格保持：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式及完整理论公理模式。完整Proof_T／内部解释及最终蕴含仍待实际构造和推导。本批结构树编译也尚未与全部原NatPacket字节包和Horn查询对应。

## 实际十二分支与历史查询

源／目标构造使用原精确Constructor关系，没有将目标FormulaCode或完整源判断当作编译分支成功的前提。输入n、bound深度b、目标码q、子码及全部历史查询都在对象层。

~~~text
Read(h,x,b,Q) = ∃V (Edge(h,x,V) ∧ Edge(V,b,Q))
Query(h,n,x,b,Q) = x∈n ∧ Read(h,x,b,Q)
AdvanceQuery = ∃B (Succ(B,b) ∧ Query(h,n,x,B,Q))
~~~

| 分支 | 源构造／输入 | 实际产出约束 |
|---|---|---|
| falsum／truth | 零字段tag0／1 | q=n |
| mem／equal／subset | 原两字段tag2／3／11，含实际bound项范围 | 前批已证的原子转换关系；mem补真实关系叶，equal保留primitive equal，subset真实展开 |
| neg | 单字段tag4[x] | Query取得子输出X，再构造tag4[X] |
| conj／disj／imp／iff | 双字段tag5／6／7／8[x,y] | 同一实际历史取得X、Y，再构造同标签[X,Y] |
| forall／exists | 单字段tag9／10[x] | AdvanceQuery以真实Succ(B,b)读取子输出X，再构造同标签[X] |

P:Formula(k+3)只索引有限对象查询模板；实际程序固定实例化为Read。它不是外部可解码函数或对内部复杂度的有限截断。子码严格界是对象成员关系，所有量词后继均为真实对象见证。

## 真实分离状态和Compiler关系

~~~text
LocalStep(w,b,q,h,n) = n∈w ∧ b∈w ∧ q∈w
                      ∧ ∃z (Empty(z) ∧ Cases(Read,h,w,b,z,n,q))
State(w,C,n,h,V) = {p∈C | ∃b,q (Ordered(p,b,q) ∧ LocalStep(w,b,q,h,n))}
~~~

这里上下文对载体的第二坐标是目标码q，不是free变量长度。谓词guard只要求输入／输出为自然码；目标FormulaCode不参与编译器成功定义。对象零在每次局部关系内EX，不抽取宿主选择函数。

原Separation实际构造状态，Extensionality证明状态唯一。总单值义务已消去，再实例化原ObjectTransfiniteRecursion.source_uniqueness，得到全部内部序数域上的实际递归图及其兼容历史。对自然n，实际后继域、完整图和值V均存在；这些值是集合，尚不是选定的目标标量码。

~~~text
Carrier(w,A,C) = Power(A,w) ∧ Power(C,A)
AtCarrier(w,C,n,b,q) = n∈w ∧ b∈w ∧ q∈w
                      ∧ ∃V (Evaluation(w,C,n,V) ∧ Edge(V,b,q))
Compiled(w,n,b,q) = ∃A,C (Carrier(w,A,C) ∧ AtCarrier(w,C,n,b,q))
~~~

载体实际存在且外延唯一；对象等词传输消去外部载体参数，Compiled与任意真实载体上的AtCarrier精确对应。非法自然输入和坐标被拒绝，实际ω对象间的关系不变性已证明。

## 产出码的实际父证书

对Ω(w)及Compiled(w,n,b,q)，已在对象EX4中取得A、C、V、h，证明：

~~~text
Carrier(w,A,C) ∧ Evaluation(w,C,n,V) ∧ Edge(V,b,q)
 ∧ Graph(w,C,h,n) ∧ State(w,C,n,h,V) ∧ LocalStep(w,b,q,h,n)
~~~

这个证书包含真实父历史、当前分离状态、值边和完整局部程序。它为后续检查递归分支及内部Foundation归纳提供实际数据，不预设输出类型或全编译器正确性。

另一个通用辅助引理证明：若对象ALL h LocalStep(w,b,q,h,n)且Ω、n∈w，则q属于实际编译关系。该ALL前提显式保留；只用于不读取子历史的基分支，不把它伪称为已消去的完整递归IH。

## 实际基分支执行

两个常量已证明：Ω、b∈w及原tag0／1构造码n推出Compiled(w,n,b,n)。对象零由Ω实际取得并消去，没有外部零见证前提。

三类原子已证明：原子局部Compiled_atomic及Ω／Empty推出实际Compiled，而不是仅有一个旁置模板结果。更强的存在性出口是：

~~~text
nativeZF ⊢ close(Ω(w) → Empty(z) → SourceAt(kind,w,b,x,y,n) →
                 ∃q (Compiled(w,n,b,q) ∧ FormulaCode(w,q,b,z)))
~~~

kind:Fin3只选择三类固定原子，所有范围、输入及输出码都是内部对象。前批实际原子输出见证与类型经本批真实状态／递归图接入；没有假定产出关系已成立。

## 唯一性的精确边界

| 命题 | 本批状态 |
|---|---|
| 同参数、同历史的分离状态V唯一 | 已证 |
| 同自然索引的递归求值集合V唯一 | 已证 |
| 常量、三类原子确有实际产出；原子有目标类型 | 已证 |
| 任意合法源公式都取得目标产出 | 未证 |
| Compiled(w,n,b,q)与Compiled(w,n,b,r)推出q=r | 完整一般情形未证 |
| 每个合法源公式的实际输出均为准确类型FormulaCode | 完整一般情形未证 |

原先的原子模板唯一性仍有效，但不能自动替代全Compiled关系的标量功能性。本批完整编译正确性门禁保持false。

## 实现与审计

ProjectCompilerCaseSyntax／LocalSyntax给出实际十二分支和真实查询；18份原对象递归推导重新实例化到这个不同的算子，并逐文件去注释严格比较。第二坐标和谓词名称均改为编译产出语义，没有把源判断换个名字当成编译器。

ProjectCompilerRoot*给出实际父证书，Independent将显式对象ALL局部条件接入真正求值，CaseIntro／Base证明实际基分支执行。ObjectProjectCompiler提供20组source／sourceZF原核／nativeZF闭句。

新增显式声明逐一#print axioms；20组core精确依赖既定propext、Classical.choice、Quot.sound，native精确再继承原七项固定证书。没有新增公理、对象Choice证书或目标类型oracle；没有增加elaboration预算或关闭linter／内核检查。

## 实际验收

- 全仓2083构建任务通过；九命令及五个--trust=0入口均退出0，零警告。
- 22521项声明审计：446项无公理、22075项仅有记录中的允许依赖；268项新增显式声明全部覆盖。
- 1866份文件SHA256独立回读一致；累计2497对闭句core／native精确公理足迹一致；20177项Internal显式声明全覆盖。
- 18份递归推导重新实例化逐文件严格比较通过；七份锁定文件不变，既有PPAC证明及AST保持原Git字节。
- YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净。
- 一般输入的输出存在／准确类型／标量唯一、完整十二构造正确性、完整schema测试、Proof／解释及最终Con门禁保持false。

此前跟踪的PPAC证明及AST保持Git字节。本批仅27个新模块、4个接入文件及6份文档；验收前基点48a152d190d009fa9a4e56db7760bd217463d00d。证据verification/{summary.json,commands.json,build.log,audit.log,project-compiler-readback.json}及.local/project-compiler-native-directed.log。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

完整验收前确认无残留Lean／Lake进程，停止失效进程0；按单文件白名单删除3份被成功运行替代的失败日志，逐项保存SHA256并删除回读。逻辑删除12642字节，盘面实测差额16384字节，包含系统并发活动。有效源码、构建缓存及有用生成／回读脚本保留；收据.local/workspace-cleanup-project-compiler-result.json。确认后才启动完整串行编译。

## 后续agent工程表

| 单元 | 工作 | 必须交付及实际验收 | 状态 |
|---|---|---|---|
| T1.2a／b | 内部次数闭合、三处指标嵌入 | 原tag9准确类型、EX7实际重命名系统 | 前批已验收 |
| T1.2c.1 | 原子正文和bound提升 | 原子实际唯一准确类型模板 | 前批已验收 |
| T1.2c.2 源判断 | 独立十二构造源语法 | 对象ALL3完整源递归方程 | 前批已验收 |
| T1.2c.2 编译构造与基步 | 实际十二分支、分离状态及原递归图 | 实际Compiler、父证书、常量／原子真实执行；明确状态与标量唯一性差别 | 本批验收 |
| T1.2c.2 查询迁移 | 真实父历史、严格子码界、实际载体 | 子Read与子Compiled精确双向对应；将实际局部程序迁移为完整Compiler递归方程，消去历史／载体前提 | 下一步 |
| T1.2c.2 完整正确性 | 上一行、源递归方程、准确构造器及类型律 | 原Foundation归纳消去完整内部IH；全部合法源的实际产出存在、准确类型、标量唯一 | 未完成，门禁false |
| T1.2c.3／d | 原字节包、Horn、正文、重命名和闭合 | 所有内部schema的准确载荷／模板／公理测试对应 | 未完成 |
| T1.3／T2 | 完整公理测试及原六规则／27模式 | 共享实际Bool、Proof_ZF／Proof_target及全内部证明编译传输 | 未完成 |
| T3 | 完整数学解释和T2 | 原nativeZF内解释正确性及最终内部Con蕴含 | 未完成 |

保留完整目标与量词；当前不能把状态唯一、五个基分支执行、外部quotation实例或成功构建计作全Compiler／Proof／Con已经完成。
