# 对象函数图：原始edge/functionOn与单点图构造
日期：2026-10-21；基点a70296095e03708baed1d22b7444cd3efe356d0d。
分支migration/yesmeta-step3；原核、源19规则、源ZF九类公理与固定依赖均未改动。
本批完成3b.2b.1；一般图扩展、内部ω/传递闭包及内部Con主句仍待完成。

## 对象语言与精确交付
语言仍为纯成员/等词ℒ；正式结论为原FirstOrder.Derives nativeZF [] 闭句。
GraphSyntax.edge_original/functionOn_original证明与源PP/AC原定义严格相等。
原functionOn的两个合取都保留：
- 每个图成员必须是定义域内对象与某输出的Kuratowski对；排除杂项及域外项。
- 定义域每点必须存在输出，且同输入所有输出与该输出相等。
并未只保留单值性，也未把对象图换成Lean函数。
原函数公式的直接整体rfl归约曾达到200000 heartbeats；最终证明先核对固定二变量公式，
再应用已证rename交换取得严格AST等式，没有增加maxHeartbeats或假设。

记K为原Kuratowski关系，E为原edge，Fun为原functionOn。
ObjectGraphs构造并证明以下完整闭句，均量化所有对象：
1. singletonSentence：
   ∀x∀y ∃d∃f∃p [d={x} ∧ f={p} ∧ K(p,x,y) ∧ Fun(f,d)]。
2. evaluationSentence：
   ∀f∀p∀x∀y∀a∀b [f={p} → (K(p,x,y) → (E(f,a,b) ↔ (a=x ∧ b=y)))]。
3. domainSentence：∀f∀d∀x∀y [Fun(f,d) → (E(f,x,y) → x∈d)]。
4. totalSentence：∀f∀d∀x [Fun(f,d) → (x∈d → ∃y E(f,x,y))]。
5. singleValuedSentence：
   ∀f∀d∀x∀y∀z [Fun(f,d) → (E(f,x,y) → (E(f,x,z) → y=z))]。

每个闭句都有原源Replacement版ZF内的Source.Derives和实际nativeZF内的Derives。
更小的输入理论直接复用ObjectPairs.assumptions，只含原Pairing与Extensionality。
五个对应kernel_certificate在该两公理理论像中证明同一完整闭句。
没有使用Replacement、Collection、Foundation或对象AC来构造单点函数图。
任意图的后三项没有限定有限图；只有具体存在构造选取单点图作为后续迭代的基础。

## 证明模块
| 模块 | 实际证明 |
|---|---|
| GraphSyntax | 完整原edge/functionOn严格对应；成员、定义域、总性、唯一值的AST及全rename/量词特化 |
| GraphLogic | 边/图成员引入消去、对象等词替换；规则只由原19规则派生 |
| GraphProperties | 任意图边的输入属于域；域内存在输出；同输入两输出相等 |
| SingletonGraphLogic | 单点图全部边的双向刻画及唯一值；完整原functionOn而非单值弱化 |
| SingletonMap | 实际构造Kuratowski编码p、域{x}、图{p}，证明完整functionOn |
| ObjectGraphs | 五个全量词闭句；两公理原核证书、源ZF与实际nativeZF回放 |

所有存在见证用原exI/exE的对象变量槽处理；没有从存在命题抽取Type数据。
同一输入/输出对象允许相等，未添加x≠y或外部标准ω/良基假设。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0，其8条命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，107个任务。
19规则及9类源ZF/SHA检查通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
471个列举审计声明：42个无公理依赖、429个有记录依赖；0条Lean警告。
新增72个审计声明，其中11个无依赖。五个kernel_certificate仅依赖标准
propext/Classical.choice/Quot.sound，不继承原底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；未新增自定义公理或sorry/admit。
检查包括原完整公式对应、五个实际原核闭句、源ZF证书、两公理证书、
直接返回原Source.SetLanguage.functionOn的开放接口和重复变量槽x=x的单点图实例。
verification/保留实际命令、日志、依赖与当前源码哈希；未推送远端。

## 下一工作与全目标缺口
下一项3b.2b.2：实际集合图的插入、相容合并/限制和定义域求值，供内部有限迭代使用。
然后构造内部ω及其全部内部成员上的迭代图、传递覆盖集，再证明对象递归与秩/累积层。
未将单点图存在或一般图的性质当作ω迭代/传递闭包已经完成。
仍需源Replacement证明原Collection、两种AC、内部ProofZF/U/Con及编译器表示、
对象解释/对称强迫和最终Derives nativeZF [] (Con_ZF → Con_target)。
OpenAI原4.34.1工程与Comparator仍未运行；没有宣称PP/AC相对一致性已证明。
