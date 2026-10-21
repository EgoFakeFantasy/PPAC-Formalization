# 一般对象图的新点扩展：存在、精确边关系和唯一性
日期：2026-10-21；基点e92135643c8fa9bb41986f654f09312e47723fd0。
分支migration/yesmeta-step3；原推导核、源19规则、源ZF九类公理和固定依赖均未修改。
本批完成3b.2b.2a；内部ω迭代与最终内部Con对象主句仍未完成。

## 背景、语言与精确对象结果
语言仍为纯成员/等词ℒ。K为原Kuratowski编码，E与Fun为完整原edge/functionOn。
ObjectGraphInsert.assumptions只含原Pairing、Union、Extensionality三个闭公理。
五个闭句均有该三公理理论上的kernel_certificate、源Replacement版ZF内的Source.Derives，
以及实际原FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。

1. insertSentence：∀A∀x ∃B ∀z (z∈B ↔ (z∈A ∨ z=x))。
2. successorSentence：∀A ∃B Source.SetLanguage.successor(B,A)。
   InsertSyntax.successor_original以rfl核对B=A∪{A}的原定义。
3. extensionSentence：∀f∀d∀x∀y [Fun(f,d) → (x∉d → ∃p∃e∃g W(g,e,p;f,d,x,y))]，其中
   W同时断言K(p,x,y)、e=d∪{x}、g=f∪{p}、完整Fun(g,e)以及全部边的等价：
   ∀a∀b (E(g,a,b) ↔ (E(f,a,b) ∨ (a=x ∧ b=y)))。
4. edgeLawSentence：对任意g/f/p/x/y，只要g=f∪{p}且K(p,x,y)，
   就有上述全部边等价；这一项本身不要求原图是函数或输入新鲜。
5. uniquenessSentence：对相同f/d/x/y的任意两组W见证，
   编码p、扩展域e、扩展图g分别相等。原型为全10变量的实际对象闭句。

扩展存在的输入前提x∉d完整保留在对象句子内；没有把此条件变成隐藏背景公理。
原图可以是任意集合图；未限制为有限图。输出y可等于x或任意旧对象。
存在与唯一性均为对象推导，不从存在命题抽取宿主选择函数。
本批没有使用Replacement、Collection、Infinity、Foundation或对象AC。

## 数学推导与模块
| 模块 | 实际推导 |
|---|---|
| InsertSyntax | 并集/插入对象AST、全rename/参数实例化、原successor的严格对应 |
| InsertLogic | 从s={x}、p={A,s}、B=∪p证明精确插入成员关系；旧/新成员、外延唯一性及等词替换 |
| InsertExistence | 原两次Pairing与一次Union实际构造任意A∪{x} |
| GraphInsertEdges | 旧边保留、新边引入、全部边的双向刻画 |
| GraphInsertEntries | 新图每个成员都是扩展定义域内的有序对，保留完整无杂项条件 |
| GraphInsertValues | 旧域点保留唯一取值；新点的旧边分支由x∉d排除；新点得到唯一值y |
| GraphInsertFunction | 域内任意点按旧/新分支处理，恢复完整原Fun(g,e) |
| GraphInsertSyntax | 完整结果W、全边闭合、三见证引入及对象唯一性 |
| GraphInsertExistence | 依次构造p=<x,y>、e=d∪{x}、g=f∪{p}，实际取得W的三个存在见证 |
| ObjectGraphInsert | 五个全量词闭句、三公理证书及源ZF/原nativeZF回放 |

所有见证只经过原exI/exE。新域的每个点确有唯一输出，原Fun的两个合取均被证明。
唯一性由有序对编码唯一、插入集合外延唯一取得；可供后续内部递归的功能性步骤使用。
这里没有把Type层数据递归或任意模型中的语义良基性当作对象推导。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0；8条实际验收命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，117个任务。
原19规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
545个列举审计声明：50个无公理依赖、495个有已记录依赖；0条Lean警告。
新增74个审计声明，其中8个无依赖；五个kernel_certificate只依赖标准
propext/Classical.choice/Quot.sound，不继承原底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；无新增自定义公理、无sorry/admit。
检查包含五个原核闭句、源ZF/三公理证书、原successor定义、直接返回原完整Source.functionOn
的开放接口，以及输出等于输入x=y的新点扩展闭句实例。
verification/保存实际命令、日志、依赖和当前源码SHA；未推送远端。

## 下一工作与剩余义务
下一项3b.2b.2b：图限制、相容图集合族合并及精确定义域/求值。
随后构造内部ω及其全部内部成员上的迭代图、传递覆盖集，推进对象递归、秩与累积层。
本批是一般对象图的单步新点扩展，不是ω迭代或传递闭包的证明。
仍需源Replacement证明原Collection、两种AC、完整内部ProofZF/U/Con与编译器表示、
对象解释/对称强迫和最终Derives nativeZF [] (Con_ZF → Con_target)。
OpenAI原4.34.1工程和Comparator仍未运行；没有宣称PP/AC相对一致性已证明。
