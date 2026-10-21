# 全部内部ω长度的实际有限迭代存在与唯一性验收
日期：2026-10-21；基点e8119b1d38491a599fb577c7328a04b911a55336。
分支migration/yesmeta-step3。本批完成内部有限轨迹实际存在和域/图唯一性；最终Con未完成。

## 对象合同
纯等词/成员语言ℒ、原19条源规则及原YesMetaZFC FirstOrder.Derives/Hilbert核均保持不变。
Track(f,d,z,a)沿用上轮精确定义：完整原functionOn(f,d)、edge(f,z,a)及
∀j,k,u,v[Succ(k,j)→edge(f,j,u)→edge(f,k,v)→UnionOf(v,u)]。
FiniteIterationSyntax.witness(f,d,n,z,a) := Succ(d,n) ∧ Track(f,d,z,a)。
existsTrack(n,z,a) := ∃d∃f witness(f,d,n,z,a)。
对象域d不是宿主数组；n、d、f、z、a与全部中间值均在对象语言中量化。

## 三个完整闭句与原核证书
ObjectFiniteIteration每句均有source_*、*_kernel_certificate、source_ZF_*及native_*：

| 闭句 | 对象内容，所有显示参数均全称闭合 |
|---|---|
| baseSentence | Empty(z)→existsTrack(z,z,a) |
| existenceSentence | Omega(w)→Empty(z)→∀n(n∈w→∃d∃f witness(f,d,n,z,a)) |
| uniquenessSentence | Omega(w)→Empty(z)→n∈w→witness(f,d,n,z,a)→witness(g,e,n,z,a)→(d=e∧f=g) |

native_*是实际FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
存在闭句和唯一性闭句分别以完整对象量词证明，并非仅宿主Lean中的存在或函数唯一性。
结论覆盖全部内部n∈ω，包括非标准模型中的内部有限长度；未假定ω外部标准。
Omega和空集前提所需的实际存在已由先前原ZF证明提供；本批不把宿主Nat冒充内部ω。

## 零长度存在构造
IterationBase证明空集z的单元集{z}严格满足Succ(d,z)。
对单点函数图f={(z,a)}，若有内部后继索引j,k及其两条边，单点图边刻画给出j=k=z。
Succ(k,j)推出j∈k，经等词传输得到z∈z，与Empty(z)矛盾；因此全部对象量词下Next(f)成立。
IterationBaseExistence用原Pairing/Extensionality的实际单点图存在证明，逐层用原exE消去
域、图及Kuratowski码见证，再以exI构造existsTrack(z,z,a)。没有抽取Type层数据。

## 实际后继存在构造
给定内部n的旧图，域d满足Succ(d,n)。对下一索引s满足Succ(s,n)，由外延唯一性得到d=s。
从完整旧函数图的总性取得n处实际末值r；由原Union取得实际v=∪r；
s∉s由原Foundation和实际单元集推导，故可用既有图扩展构造新增(s,v)的实际新图。
新域e满足Succ(e,s)，并保留完整原functionOn及精确旧/新边刻画。

IterationExtensionAlgebra验证所有索引及输出的四类边组合：
- 旧→旧：沿用旧图的Next规律。
- 旧→新：后继消去确定旧输入正是n；单值性对齐旧末值，再传输并集公式。
- 新→旧：旧域s的传递性与后继成员关系推出s∈s，矛盾。
- 新→新：两个输入都等于s，后继成员关系同样推出s∈s，矛盾。
IterationExtension将这四类推导闭合于全部对象j,k,u,v，得到真正Next(newGraph)。
IterationExtensionExistence组合原Union见证和真实图扩展，产生后继existsTrack，而非仅定义扩展谓词。

## 全部内部长度及唯一性
IterationExistence.existenceMatrix是两个种子参数、一个归纳变量的Formula 3。
将零存在和后继存在代入完整对象ω归纳，实际得到∀n∈ω existsTrack(n,z,a)。
其中所需n及后继的传递性、任意集合不自属均由既有对象定理推导；未使用外部良基归纳。

FiniteIterationUniqueness由Succ(d,n)、n∈ω推得d的传递性和d⊆ω；
两个后继域先由外延唯一性对齐，再以先前共同输入相容性与完整图外延性取得图相等。
这次已补齐此前缺失的全内部存在性，不再只有“给定图则唯一”的条件结果。

## 公理输入和实际验收
ObjectFiniteIteration.assumptions精确含8句：Extensionality、Pairing、Union、Foundation，
以及transitiveMatrix、existenceMatrix、subsetMatrix、agreementMatrix的四个完整Separation实例。
未调用Replacement、Collection、对象AC或不可达作为输入；给定Omega前提的有限构造不再另取Infinity。
此处不声称无条件ω存在不需要Infinity；其实际构造另有先前证书。

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，170个任务。
19条源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
1037个列举审计声明：89个无依赖、948个记录允许依赖；0条Lean警告。
新增57个审计声明，其中3个无依赖；无sorry/admit、新自定义公理或外部标准长度截断。
三个有限公理kernel_certificate仅依赖标准propext/Classical.choice/Quot.sound；
实际nativeZF回放维持底座7个基础句子FreeClosed证书的既有基线。
verification/保存真实命令、日志、依赖及源码SHA；未推送远端。

## 下一项与全目标边界
下一项用原完整Replacement收集全部内部n的唯一轨迹图或末值，实际构造集合族，
再证明其相容并调用任意内部图族合并，取得全局ω迭代图/值域及每个集合的传递覆盖。
本批尚未取得该全族集合或全局并图，object_omega_iteration_proved仅指上述全内部有限轨迹存在唯一；
全族收集与全局合并的验收状态另列为false，不将有限图提升为全局图已经存在。
传递覆盖/秩/累积层、反向Collection、两种AC、内部ProofZF/U/Con及内部编译器正确性、
对象解释/对称强迫和最终Con_ZF→Con_target仍未完成。
OpenAI原4.34.1工程及Comparator仍未运行；未宣称原PP/AC相对一致性定理已经完成。
