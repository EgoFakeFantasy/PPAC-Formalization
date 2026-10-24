# Project十二构造独立源语法与内部递归方程验收（2026-10-25）

本批完成完整正文编译所需的独立源判断及其原核递归方程。五类原子（两个常量、成员、primitive equal、subset）和七类逻辑／量词构造均进入真实集合递归；最终ALL3双条件覆盖全部内部根码、bound长度及ambient上下文。33个新模块、282项显式声明、16组原nativeZF闭句。

这不是完整十二构造目标编译器的正确性证明。本批源判断还没有与原schema的NatPacket字节包及Horn判定建立完整内部对应；全编译器、完整schema测试、Proof／内部解释及最终Con仍未证明。

## 对象语言、背景和最终目标

纯等号／成员ℒ；背景保持Contract.nativeZF及完整Separation／Collection；推导仍为原YesMetaZFC.Logic.FirstOrder.Derives。最终规格仍为：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式及完整公理模式。最终主句尚未实际构造并证明；本批递归方程不能替代它。

## 独立源语法

原三原子SourceAt的项条件只使用BranchBound，不使用目标FormulaCode或Compiled。成员／primitive equal／subset分别是两字段的tag2／3／11。两个常量是tag0／1的零字段码。

| 构造 | 源码条件 | 子判断作用域 |
|---|---|---|
| falsum／truth | 原零字段tag0／1 | 无子项 |
| mem／equal／subset | 原两字段tag2／3／11；两项均为实际bound项码 | 两项索引均在内部b内 |
| neg | 原单字段tag4及真实严格子码界 | 同b |
| conj／disj／imp／iff | 原双字段tag5／6／7／8及真实严格子码界 | 两子式同b |
| forall／exists | 原单字段tag9／10及真实严格子码界 | 实际对象后继B，Succ(B,b) |

沿用通用上下文状态中的第二槽f，要求f∈ω；它不开放Project自由项分支。闭源正文入口使用对象零z及Empty(z)，与后续编译接口对接。所有出现的b、f、根码及子码都是对象槽，没有把内部长度或码换成外部Nat索引。

## 实际Separation状态与原超限递归

对固定对象参数w和上下文对载体C，当前索引n及实际前段图h决定状态V：

~~~text
Row(w,n,h,p) = ∃b,f (Ordered(p,b,f) ∧ SourceLocal(w,b,f,h,n))
State(w,C,n,h,V) = {p∈C | Row(w,n,h,p)}
~~~

一个原Separation实例构造状态，原Extensionality证明唯一性。状态逐对成员精确等价于完整SourceLocal，非法上下文、杂项和非自然根被对象推导排除。

随后将这个具体算子实例化到原ObjectTransfiniteRecursion.source_uniqueness。总单值义务由实际Separation／Extensionality消去，得到每个内部序数域上的真实递归图及唯一性；没有保留假设存在的图、外部递归器、模型或语义可靠性接口。后继域、实际历史限制和求值边均在对象EX中取得。原递归兼容性证明所有域及历史选择所得值一致。

## 消去载体的SourceCode

~~~text
Carrier(w,A,C) = Power(A,w) ∧ Power(C,A)
TypedSource(w,C,n,b,f) = n∈w ∧ Contexts(w,b,f)
                       ∧ ∃V (SourceEvaluation(w,C,n,V) ∧ Edge(V,b,f))
SourceCode(w,n,b,f) = ∃A,C (Carrier(w,A,C) ∧ TypedSource(w,C,n,b,f))
~~~

幂集载体实际存在，原Extensionality证明同一个w的真实载体唯一；原eqSubst传输TypedSource。最终SourceCode没有外部载体参数，和任意真实载体上的TypedSource精确等价。

历史读取与子SourceCode双向对应；真实子码界和源参数守卫保持。完整递归式是：

~~~text
Criterion(w,n,b,f) = n∈w ∧ SourceCases(w,n,b,f)
nativeZF ⊢ close(Ω(w) → ∀n,b,f (SourceCode(w,n,b,f) ↔ Criterion(w,n,b,f)))
~~~

SourceCases为上表全部十二构造；量词分支在对象EX中保留实际后继。这个双条件覆盖自然根、非自然候选及所有上下文，不要求它们是外部AST的quotation。最终ALL3入口只保留Ω，没有图、载体、求值见证、IH、Promise或标准性假设。

另已证明SourceCode的自然根及上下文守卫、相应拒绝式，以及任意两个实际ω对象之间的判断不变性。

## 实现与审计

| 模块族 | 工作 |
|---|---|
| ProjectSourceAtomSyntax／Atoms | 独立五原子源码条件、上下文及自然码范围 |
| ProjectSourceLocalSyntax／Local | 十二构造的完整局部源判断及真实范围 |
| ProjectSourceTypeState* | 原Separation状态、存在唯一、精确逐对成员 |
| ProjectSourceTypeRecursion*／Recursors | 具体算子总单值及真实原递归图 |
| ProjectSourceTypeEvaluation*／GraphValues／History | 实际后继域求值、唯一性、跨域兼容及历史限制 |
| ProjectSourceTypeJudgment*／*Transfer／Recursive* | 实际类型判断、子码读取及完整递归双条件 |
| ProjectSourceCode* | 载体EX、原等词传输、自然守卫及全内部ALL3递归方程 |
| ObjectProjectSourceCode | 16组source／sourceZF原核／nativeZF闭句 |

30份已有对象递归推导按命名空间重新实例化到这套不同的源语法，保持原推导步骤；原实现不变。验收器逐文件去注释后重建并严格比较全部替换结果，另外单独审核新增原子语法和全部十二构造分支。它们不是把目标判断重命名为源判断：源原子有tag11和两字段成员结构，且不允许自由项；没有引用目标FormulaCode或编译成功作为源合法性。

每项新增显式声明独立#print axioms；16组core精确为既定propext、Classical.choice、Quot.sound，native精确再继承原七项固定公理证书。没有新增公理或对象Choice证书，没有关闭linter／内核检查或增加elaboration预算。

## 实际验收

- 全仓2056构建任务通过；九命令及五个--trust=0入口均退出0，零警告。
- 22253项声明审计：439项无公理、21814项仅有记录中的允许依赖；282项新增显式声明全部覆盖。
- 1839份文件SHA256独立回读一致；累计2477对闭句core／native精确公理足迹一致；19909项Internal显式声明全覆盖。
- 30份对象推导重新实例化逐文件严格比较通过；七份锁定文件未变，既有PPAC证明及AST保持原Git字节。
- YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净。
- 完整十二构造目标编译、原字节包／Horn对应、完整schema测试、Proof／解释及最终Con门禁保持false。

此前跟踪的PPAC证明及AST保持Git字节。本批仅33个新模块、4个接入文件及6份文档；验收前基点cce56f9da26b3723a0d85754f943786a8444fe26。证据verification/{summary.json,commands.json,build.log,audit.log,project-source-readback.json}及.local/project-source-native-directed.log。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

完整验收前实测无残留Lean／Lake进程，也未发现本批失效日志或无用脚本，停止进程0、删除文件0。有用源码、缓存、定向验收和生成／回读脚本均保留；收据.local/workspace-cleanup-project-source-result.json。检查后才启动完整串行编译。

## 后续agent工程表

| 单元 | 工作 | 必须交付及验收 | 状态 |
|---|---|---|---|
| T1.2a／b | 内部次数闭合、三处真实指标嵌入 | 原tag9类型律、EX7重命名系统 | 前批已验收 |
| T1.2c.1 | 三类原子正文及bound项提升 | 源两字段成员／primitive equal／subset的实际唯一准确类型输出 | 前批已验收 |
| T1.2c.2 源判断部分 | 独立全十二源语法、Separation状态和原递归图 | 无外部载体／历史前提的ALL3完整源递归方程 | 本批验收 |
| T1.2c.2 编译部分 | 原子出口、逻辑／量词局部编译及实际输出状态递归 | 独立内部Compiler；准确binder作用域；对每个SourceCode取得唯一FormulaCode；原Foundation消去完整内部IH | 下一步，未完成 |
| T1.2c.3 | 原ProjectEncode、证书载荷及原查询 | 所有内部schema的NatPacket字节包／结构树与原Horn精确对应 | 未完成 |
| T1.2d／T1.3 | 完整正文、重命名、闭合与固定7+3测试 | Separation／Collection完整模板和ZF／目标理论准确公理测试，实际共享Bool | 门禁false |
| T2 | 完整公理测试、原六规则／27模式 | 专用Proof_ZF／Proof_target及全内部证明码编译传输 | 未完成 |
| T3 | T2及完整数学解释 | 原nativeZF内解释正确性及最终内部Con蕴含 | 未完成 |

继续建设实际目标编译器及其全部内部码正确性。禁止把本批源递归方程、外部quotation模式或成功构建当作目标Compiler／原schema测试／最终Con已经完成。
