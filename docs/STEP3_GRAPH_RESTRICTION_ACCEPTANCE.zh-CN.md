# 任意对象图限制：实际分离构造、完整函数性与组合律
日期：2026-10-21；基点1fdaa4b425a4b096076181aaf8d094cd6dd7bd97。
分支migration/yesmeta-step3；原源19规则、ZF九类公理与YesMetaZFC推导核及依赖均未修改。
本批完成3b.2b.2b.i；相容图族合并、内部ω/传递闭包及最终内部Con主句仍待完成。

## 对象语言、输入公理与实际构造
语言仍为纯成员/等词ℒ，K/E/Fun均沿用原Kuratowski/edge/functionOn。
RestrictionSyntax.subset_original以rfl核对源原subset。
定义R(g,f,b)为完整对象公式：
∀p [p∈g ↔ (p∈f ∧ ∃x∃y (x∈b ∧ K(p,x,y)))]。
实际构造只用一个完整原Separation实例，矩阵为entryOn(b,p)。
b是对象参数，不是宿主集合；分离上界就是原图集合f。
ObjectRestriction.assumptions只含Extensionality和该分离实例两个闭公理。

## 六个完整对象闭句
每个闭句均有两公理理论像上的kernel_certificate、源Replacement版ZF内Source.Derives，
以及实际原FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。

1. setSentence：∀f∀b ∃g R(g,f,b)。这一项允许任意集合f/b，不先假设f是函数。
2. functionSentence：∀f∀d∀b [Fun(f,d) → (b⊆d → ∃g W(g,f,b))]，其中
   W同时断言R(g,f,b)、完整Fun(g,b)和全部边刻画
   ∀x∀y [E(g,x,y) ↔ (E(f,x,y) ∧ x∈b)]。
3. edgeSentence：∀g∀f∀b [R(g,f,b) → 上述全部边刻画]。
4. uniqueSentence：∀g∀h∀f∀b [R(g,f,b) → (R(h,f,b) → g=h)]。
5. identitySentence：∀g∀f∀d [Fun(f,d) → (R(g,f,d) → g=f)]。
6. composeSentence：∀h∀g∀f∀b∀c [c⊆b → (R(g,f,b) → (R(h,g,c) → R(h,f,c)))]。

存在、唯一性及代数律都在对象层证明；没有用宿主限制函数或语义模型结论代替。
函数限制保留原Fun的两个合取：每个图成员的合法性/定义域条件，以及域内存在唯一输出。
子域条件b⊆d明确留在对象句子内；未要求b/d不同或图/定义域有限。
恒等律实质使用原图每个成员是域内有序对的条件，不能从弱化的单值关系得到本结果。

## 证明模块
| 模块 | 已证明内容 |
|---|---|
| RestrictionSyntax | 对象限制及其结果AST、完整分离实例、任意参数映射/全rename和量词特化 |
| RestrictionEdges | 限制边属于原图、输入属于限制集合、反向保留边及全量词双向刻画 |
| RestrictionFunction | 旧唯一值在子域保留；域内每点实际存在输出；完整原functionOn |
| RestrictionAlgebra | 外延唯一性、自定义域限制恒等、子域单调及连续限制组合律 |
| RestrictionExistence | 用实际分离见证组装完整函数限制与边刻画 |
| ObjectRestriction | 六个闭句、两公理原核证书、源ZF/实际nativeZF回放 |

存在见证均经原exI/exE；分离矩阵的所有参数提升和binder作用域已严格核对。
本批不调用Pairing、Union、Replacement、Collection、Foundation或对象AC作为逻辑输入。
并未把R关系的AST存在或编译通过本身当作对象定理，交付包含实际原核Derives证书。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0；8条实际命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，123个任务。
19源规则、9类源ZF及固定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
610个列举审计声明：56个无公理依赖、554个有记录依赖；0条Lean警告。
新增65个审计声明，其中6个无依赖；六个kernel_certificate仅依赖标准
propext/Classical.choice/Quot.sound，不继承原底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；没有新增自定义公理或sorry/admit。
检查包含六个原核闭句、源ZF及两公理证书、原subset对应、直接返回完整原Source.functionOn
的开放接口及同一个域变量b=d的限制存在闭句。verification/记录真实日志、命令、依赖和源码哈希。
未推送远端，未运行OpenAI原4.34.1工程或Comparator。

## 下一工作与全目标缺口
下一项：构造任意对象图G的实际定义域，并证明任意内部相容图集合族的并图仍满足完整Fun。
计划先从Kuratowski编码推导每个边输入属于∪∪G，再在该集合上分离定义域；
随后对任意内部图集合族处理并集，而非仅外部可数族或有限样例。
仍需内部ω的全部成员上的迭代图、传递覆盖、对象递归/秩/累积层、源Replacement证明原Collection、
两种AC、内部ProofZF/U/Con与编译器表示、对象解释/对称强迫及最终内部Con主句。
本批没有证明内部ω迭代、传递闭包或原PP/AC相对一致性结论。
