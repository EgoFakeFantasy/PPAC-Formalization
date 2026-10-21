# 对象秩前置：全参数有界极小元与成员归纳模式
日期：2026-10-21；基点e2a932bcc6e462a585314c0329c236e8a8f00be9。
分支migration/yesmeta-step3；原核、源19规则、源ZF九类公理与固定依赖未修改。
本批完成3b.1；Replacement→Collection及最终内部Con对象主句仍未完成。

## 对象语言、背景与精确结论
语言仍为纯成员/等词ℒ，正式结论仍为原FirstOrder.Derives。
对任意外部模式索引p : Source.Formula (n+1)，分别构造并证明完整闭句：

1. BoundedMinimal.sentence p：
   ∀参数 ∀A [(∃x (x∈A ∧ p(x))) →
     ∃x (x∈A ∧ p(x) ∧ ∀y ((y∈A ∧ p(y)) → y∉x))]。
2. BoundedInduction.sentence p：
   ∀参数 ∀A [(∀x (x∈A → ((∀y (y∈A → (y∈x → p(y)))) → p(x)))) →
     ∀x (x∈A → p(x))]。

这里的“极小”只禁止满足者作为见证的成员，不声称任意关系下的最小/唯一见证。
所有参数、见证和界集合均在对象公式内量化；p可任意复杂、可含任意交错量词。
外部模式索引保留，不引入内部统一真值断言或对象AC。
两模式都有源Replacement版ZF的Source.Derives证书和原nativeZF的实际Derives证书。
更强的是，各自有只以Foundation与一个Separation实例为理论输入的kernel_certificate：
极小元使用分离矩阵p；归纳使用反例矩阵p.neg。未调用Replacement或Collection。

## 推导内容与模块
| 模块 | 实际证明 |
|---|---|
| MinimalPredicates | 谓词参数代入、满足者、分离集、有界极小元；全重命名与量词特化 |
| MinimalLogic | 原19规则证明满足者分离集非空；正则极小元满足原谓词且排除所有界内前驱 |
| MinimalInstances | 原始Foundation和完整Separation句子的严格AST对应及任意参数实例化；core对应均为rfl |
| BoundedMinimal | 分离出C，正则公理在C中取极小元，回放成原谓词的极小元；全参数闭合与原核证书 |
| BoundedInduction | 假定反例，取成员极小反例，由进步性导出矛盾；全参数闭合与原核证书 |

存在见证通过原exE/exI的对象变量槽处理；没有抽取Type层选择函数。
归纳的经典反证只使用原19规则中的classical，不引入外部WellFounded。
source_ZF_minimal/source_ZF_induction直接将两公理包含到源ZF；没有先借用未证的ZF等价。
native_minimal/native_induction将同一两公理证书用原theory_cut回放到实际nativeZF。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0；其8条命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，94个任务。
源19规则及源ZF九类构造/SHA核对通过；Check、CheckStep2、CheckStep3与Audit均以--trust=0通过。
335个列举审计声明：22个无公理依赖、313个有已记录依赖；0条Lean警告。
新增52个审计声明，其中3个无依赖；两模式kernel_certificate仅依赖标准
propext/Classical.choice/Quot.sound，不继承原底座7个句子闭合native_decide证书。
实际nativeZF接口仍继承既有7证书基线；未把整个工程称作只含标准公理。
检查包含任意n/p总接口、两个精确的两公理证书、源ZF无Collection证明接口、
多个参数且内嵌交错量词的实际模式实例。没有sorry/admit或新增自定义公理。
verification/记录实际命令、日志和当前源文件哈希；未运行OpenAI原库/Comparator，未推送远端。

## 未完成义务与下一工作
本批只在任意给定集合A内归纳，不是无界集合归纳，也不说明外部模型成员关系良基。
尚未构造对象内部传递闭包、ω迭代、递归图、秩函数或累积层，更未完成Collection。
下一工作按流程3b.2–3b.4推进：
- 纯对象Kuratowski对/函数图、内部ω与全部内部自然数上的有限迭代，构造传递覆盖集。
- 在对象ZF内证明递归图存在唯一性、序数比较与秩/累积层覆盖。
- 用唯一最小见证秩及Replacement收集秩，以共同层容纳关系见证，输出完整原Collection句子。
两种AC、内部ProofZF/U和编译器表示、对称强迫及内部Con主句仍是全目标的必要义务。
