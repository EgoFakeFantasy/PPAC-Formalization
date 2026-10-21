# 任意内部相容图集合族：实际定义域、并图与唯一性
日期：2026-10-21；基点04e95625292c3dbdaa59e2ddf4f1c6f2c53e29e1。
分支migration/yesmeta-step3；原推导核、源19规则、ZF九类公理及固定依赖均未修改。
本批完成图定义域与任意内部相容族合并；内部ω/迭代及最终内部Con主句仍未完成。

## 对象语言与完整族范围
语言仍为纯成员/等词ℒ。K/E/Fun分别是原Kuratowski、edge与完整functionOn。
F在对象语言中量化，表示一个任意内部集合，未限制有限、外部可数或非空。
Graphs(F) := ∀h(h∈F → ∃d Fun(h,d))。
Compatible(F)断言F内任意两个图在任意共同输入上的输出相等。
每个成员域的存在见证均由原exE处理，没有选择宿主层域函数或额外对象AC。

## 实际集合构造
任意集合图G的输入x都有Kuratowski码p∈G。消去p={{x},{x,y}}的对象见证，
逐成员推出x∈∪∪G；这是实际原19规则推导，不使用外部秩或良基性。
用原Union实际构造U=∪G、V=∪U，在V上分离矩阵HasEdge(G,x)，得到D。
由输入界消去分离结果中额外的x∈V条件，证明精确定义域：
Dom(D,G) := ∀x(x∈D ↔ ∃y E(G,x,y))。

给定Graphs(F)和Compatible(F)，再用Union构造G=∪F并构造其实际定义域D：
- 每个p∈G来自某h∈F；h的完整Fun条件给出p的合法对编码。由G上的实际边得输入在D。
- 任意G边来自某h∈F的同一条边，反向每条成员边也实际进入G。
- 两个G边的成员见证由Compatible(F)得到输出相等。
- D内每点的实际边见证与上述单值性组成原Fun的总性/唯一性合取。
由此取得完整原Fun(G,D)、精确逐成员边关系，并以外延性取得G和D唯一。

## 六个原核全量词闭句
ObjectGraphFamily中的每个闭句都有三公理kernel_certificate、源Replacement版ZF内Source.Derives，
以及实际FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
1. domainSentence：∀G ∃D Dom(D,G)，适用于任意集合G，不先假设G为函数。
2. domainUniqueSentence：∀D∀E∀G [Dom(D,G) → (Dom(E,G) → D=E)]。
3. unionSentence：∀F [Graphs(F) → (Compatible(F) → ∃G∃D W(G,D,F))]，
   W同时包含G=∪F、Dom(D,G)、完整Fun(G,D)与
   ∀x∀y [E(G,x,y) ↔ ∃h(h∈F ∧ E(h,x,y))]。
4. uniqueSentence：同一F的任意两组W见证，其G和D分别相等。
5. edgeSentence：对任意G/F，只要G=∪F即有上述精确边关系，不要求函数性或相容性。
6. emptySentence：∀F [Source.SetLanguage.empty(F) → ∃G∃D W(G,D,F)]。
   原空集谓词实际推出Graphs/Compatible，未添加族非空条件。

输入理论仅含原Union、Extensionality及一个完整Separation实例，矩阵为HasEdge(G,x)。
没有用Replacement、Collection、Pairing、Infinity、Foundation或Choice作为逻辑输入。
没有事先收集各成员的域，避免依赖尚未证明的Collection反向数学方向。

## 工程模块
GraphDomainSyntax/Bound/Existence/Algebra构造实际定义域及其界、唯一性和等词运输。
GraphFamilySyntax/Edges/Values/Entries/Function/Existence/Empty证明任意内部图族的完整合并。
ObjectGraphFamily闭合六个句子，给出三公理证书并回放到源ZF与实际nativeZF。
默认入口import PPAC已导入本批；没有改用新推导核或恢复退役反射实现。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0；8条命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，135个任务。
19源规则、9类ZF/SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
703个列举审计声明：67个无公理依赖、636个有已记录依赖；0条Lean警告。
新增93个审计声明，其中11个无依赖；六个kernel_certificate仅依赖标准
propext/Classical.choice/Quot.sound，不继承原底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；无新增自定义公理、无sorry/admit。
检查包括六个完整原核闭句（含空族）、源ZF/三公理证书、直接返回原Source.functionOn
的开放接口，以及直接针对原edge的二重并集输入界。verification/保存实际日志、命令和源码哈希。
未推送远端；未运行OpenAI原4.34.1工程或Comparator。

## 下一工作与全目标缺口
下一项为原Infinity和Separation内的实际最小归纳集ω、唯一性及对象ω归纳模式。
随后在对象ω归纳中构造全部内部n的唯一迭代图，经Replacement取得实际集合族再合并，
构造传递覆盖并推进对象递归、秩与累积层。不得以外部Lean.Nat归纳代替全部内部ω成员。
仍需源Replacement证明原Collection、两种AC、内部ProofZF/U/Con及编译器表示、
对象解释/对称强迫与最终Derives nativeZF [] (Con_ZF → Con_target)。
本批没有证明内部ω迭代、传递闭包或PP/AC相对一致性主结论。
