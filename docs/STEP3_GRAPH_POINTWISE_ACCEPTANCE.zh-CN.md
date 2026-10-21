# 完整对象函数图逐点外延性的实际验收
日期：2026-10-21；基点f4b67b4770612a76b8d97e49e655d9365efa0a3b。
分支migration/yesmeta-step3。本批完成流程3b.2b.3b.i；内部有限迭代和最终Con仍未完成。

## 语言与理论输入
纯等词/成员语言ℒ及原YesMetaZFC FirstOrder.Derives保持不变。
edge/functionOn严格沿用原Source图定义；没有采用宿主函数替代内部集合图。
有限公理理论ObjectGraphPointwise.assumptions仅含原Extensionality。
背景nativeZF和原Source Replacement版ZF分别提供实际回放；未使用Collection作为数学输入。

## 全部对象闭句
记Entries(f,d)为原entriesOn，Fun(f,d)为完整原functionOn。
E(f,g) := ∀x∀y(edge(f,x,y)→edge(g,x,y))；SameE(f,g):=E(f,g)∧E(g,f)。
A(f,g)沿用原GraphFamilySyntax.agrees：∀x,y,z(edge(f,x,y)→edge(g,x,z)→y=z)。
下列全部参数均在对象闭句中全称量化，包含任意内部图、域和空域：

| 闭句 | 对象内容 |
|---|---|
| subsetSentence | Entries(f,d)→E(f,g)→f⊆g |
| edgesSentence | Entries(f,d)→Entries(g,e)→SameE(f,g)→f=g |
| inclusionSentence | Fun(f,d)→Fun(g,e)→d⊆e→A(f,g)→f⊆g |
| equalitySentence | Fun(f,d)→Fun(g,d)→A(f,g)→f=g |
| domainSentence | Fun(f,d)→∀x(x∈d↔∃y edge(f,x,y)) |
| domainUniqueSentence | Fun(f,d)→Fun(f,e)→d=e |

每句均有source_*、*_kernel_certificate、source_ZF_*和native_*。
native_*类型为真实FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
源理论上的证明沿用已锁定19条原规则，再由已验收编译器生成原Hilbert核证书。
没有添加可信规则或只用语义真值替代推导。

## 推导构造
GraphPointwiseSyntax固定逐边包含/等价及重命名、全称实例化、边输出等词替换。
GraphPointwiseEntries从p∈f及Entries(f,d)消去对象输入/输出见证，取得p编码某条边；
逐边包含将该边送入g，消去g中的实际边码q，以Kuratowski唯一性证明p=q，故p∈g。
保留Entries前提排除无边的杂项；没有把任意集合的边相等误作集合相等。
两个方向的实际成员包含最后应用Extensionality得到图集合相等。

GraphPointwise由f的完整functionOn推出边输入属于d，沿d⊆e进入g的域，
用g的对象总性取得输出见证，以相容性对齐输出并传输边；全过程仅用原exI/exE，
未从∀x∃y中抽取Type层选择函数。同域时两个方向同时成立，遂得图相等。
GraphPointwiseDomain证明任意functionOn域恰好等于实际边定义域，以已有域外延唯一性取得d=e。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1，LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，155个任务。
19条源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
926个列举审计声明：81个无依赖、845个记录允许依赖；0条Lean警告。
新增51个审计声明，其中2个无依赖；无sorry/admit、新自定义公理或固定模式截断。
有限单公理理论上的所有kernel_certificate仅依赖标准propext/Classical.choice/Quot.sound；
实际nativeZF回放维持底座7个固定句子FreeClosed证书的既有基线。
verification/记录实际命令、日志、依赖及源码SHA；没有推送远端。

## 下一项与剩余目标
内部有限迭代尚未定义或证明完成。下一项在全部内部n∈ω上构造唯一函数图，
域为n的后继、空集位置输出任意种子a、后继位置输出前一位置值的并集。
先以对象ω归纳证明两份任意有限轨迹在共同输入的输出一致，再用本批图外延性证明图唯一；
存在步使用新鲜后继图扩展，保留完整原functionOn并验证全部递推关系。
之后以Replacement收集全部内部n的图或末值，实际合并得到传递覆盖。
传递覆盖/秩/累积层、反向Collection、两种AC等价、内部ProofZF/U/Con及任意内部码上的
编译器正确性、对象解释/对称强迫和最终Con_ZF→Con_target仍未完成。
OpenAI原4.34.1构建与Comparator仍未运行，未宣称原PP/AC相对一致性定理已经验收。
