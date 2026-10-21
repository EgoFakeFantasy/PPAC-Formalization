# 给定对象并集递推轨迹的相容性与同域唯一性验收
日期：2026-10-21；基点0e2b37d10896b493092d47288823790fbd664efd。
分支migration/yesmeta-step3。本批完成给定轨迹的条件相容/唯一性；实际轨迹存在仍未完成。

## 纯对象定义与交付边界
仍使用纯成员/等词ℒ、原19条源规则和原YesMetaZFC Hilbert核。
没有引入新可信核、对象函数符号、宿主自然数索引数组、外部良基或标准ω假设。
Next(f) := ∀j,k,u,v[Succ(k,j)→edge(f,j,u)→edge(f,k,v)→UnionOf(v,u)]。
Track(f,d,z,a) := functionOn(f,d) ∧ edge(f,z,a) ∧ Next(f)。
functionOn、edge、Succ及UnionOf均沿用已有严格对应原源编码的纯公式。
完整functionOn已经保证边的输入在实际域中；Next量化全部内部集合及输出。
Track只规定单条图的局部递推规律，未把两图相容、相等或存在当作字段假设。

At(f,g,x) := ∀u,v[edge(f,x,u)→edge(g,x,v)→u=v]；
Common(f,g,d,e,x) := x∈d→x∈e→At(f,g,x)。
agreementMatrix是一个四参数、一个归纳变量的完整Formula 5，没有复杂度截断。
外部Fin只编码有限变量位置，内部ω成员由对象量词覆盖。

## 三个实际原核闭句
ObjectIterationUniqueness的三句均全称闭合所有参数：

1. commonSentence：Omega(w)、Empty(z)、Track(f,d,z,a)、Track(g,e,z,a)、
   Transitive(d)、Transitive(e)推出∀x∈w Common(f,g,d,e,x)。
2. compatibleSentence：上述前提再加d⊆w，推出原GraphFamilySyntax.agrees(f,g)。
   第二域e不额外要求为w的子集；这比两个域都在ω中的常用实例更一般。
3. uniqueSentence：Omega(w)、Empty(z)、Track(f,d,z,a)、Track(g,d,z,a)、
   Transitive(d)、d⊆w推出f=g。

每句有source_*、*_kernel_certificate、source_ZF_*、native_*；后者类型为
FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
有限公理理论仅含原Extensionality和agreementMatrix的一个完整Separation实例。
不使用Foundation、Pairing、Union、Replacement、Collection或AC作为理论输入；
这些结论以已给定的实际轨迹及其递推性质为条件，没有据此制造任何存在性结论。

## 实际证明
IterationValues用空集唯一性对齐种子位置，再用完整函数图单值性对齐其输出。
后继步将共同前驱输出的等词传入UnionOf，以并集外延唯一性取得共同后继输出相等。
此处不需要Union存在公理，因为两个已给定轨迹的Next前提已经约束各自实际输出。

IterationStep先从Succ(k,j)取得j∈k；若k属于传递域d，则j∈d。另一域同理。
利用各轨迹的对象总性取得前驱输出，逐次用原exE消去见证，由归纳假设对齐前驱值，
再调用并集唯一性。未抽取宿主选择函数，也未假设两个轨迹长度具有已证的比较关系。
IterationInduction将上述四参数矩阵代入完整对象ω归纳，返回全部内部x∈ω的Common推导。
IterationCompatibility从实际边推得输入属于域，沿d⊆ω进入归纳结论，取得全图相容性；
同域时调用上轮完整函数图逐点外延性，获得实际图集合相等。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，161个任务。
19条源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
980个列举审计声明：86个无依赖，894个有记录允许依赖；0条Lean警告。
本批新增54个审计声明，其中5个无依赖；无sorry/admit、新自定义公理或固定长度取代全内部范围。
三个有限公理kernel_certificate仅依赖标准propext/Classical.choice/Quot.sound；
实际nativeZF回放保留既有7个基础句子FreeClosed证书基线。
verification/保存真实命令、日志、依赖及源码SHA；未推送远端。

## 下一工作与最终缺口
还没有证明每个内部n∈ω上存在Track，不能把给定轨迹唯一性升级为存在唯一性。
下一项以实际单点种子图证明零长度情形，再用Union取得下一值、新鲜后继扩展图，
验证全部旧/新输入输出的Next规律，在对象ω归纳中证明所有内部n的实际图存在。
随后推导后继域的传递性及其属于ω，从而把本批一般条件唯一性装配到有限轨迹上，
再用Replacement取得全部内部n的图或末值的实际集合，合并并证明传递覆盖。
传递覆盖/秩/累积层、反向Collection、两种AC、内部ProofZF/U/Con及内部编译器正确性、
对象解释/对称强迫和最终Con_ZF→Con_target仍未完成。
OpenAI原4.34.1构建与Comparator仍未运行，未宣称原PP/AC相对一致性已经完成。
