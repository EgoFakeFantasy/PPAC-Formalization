# 对象ω结构与任意内部集合不自属的实际验收
日期：2026-10-21；基点04349f66b797e5e9d1cdd0ba28a7952db5a1c453。
分支migration/yesmeta-step3。本批完成流程3b.2b.3a.i，未完成内部迭代或最终Con。

## 对象语言与背景
仍使用单排序纯成员/等词ℒ，原YesMetaZFC FirstOrder.Derives/Hilbert核。
背景nativeZF是原Collection呈现ZF的纯语言像；没有加AC、不可达或Con假设。
所有ω、后继及函数图均为对象公式，ω是上轮实际构造的最小归纳集。
原Source.successor与本工程successor严格相同；没有宿主Nat作为对象ω。

## 本批八个结构闭句
ObjectOmegaStructure构造完整纯对象闭句，对每句均提供：
source_*（六句有限公理理论上的原19规则推导）、*_kernel_certificate（其原核证书）、
source_ZF_*（源Replacement版ZF推导）、native_*（实际nativeZF原核推导）。

| 闭句 | 对象内容 |
|---|---|
| decompositionSentence | ∀w(Omega(w)→∀n∈w[Empty(n)∨∃m∈w Succ(n,m)]) |
| transitiveSentence | ∀w(Omega(w)→Transitive(w)) |
| elementsSentence | ∀w(Omega(w)→∀n∈w Transitive(n)) |
| zeroSentence | ∀w,z(Omega(w)→Empty(z)→z∈w) |
| successorSentence | ∀w,n,s(Omega(w)→n∈w→Succ(s,n)→s∈w) |
| nonzeroSentence | ∀w,n(Omega(w)→n∈w→¬Empty(n)→∃m∈w Succ(n,m)) |
| injectiveSentence | ∀w,n,m,s(Omega(w)→n∈w→Succ(s,n)→Succ(s,m)→n=m) |
| freshSentence | ∀w,n(Omega(w)→n∈w→∃s∈w[Succ(s,n)∧s∉s]) |

Transitive(x)展开为∀y(y∈x→y⊆x)。没有外部标准自然数限制。
后继消去的第二前驱m量化于全部内部集合，并未额外要求m∈ω。
给定Omega前提的结构证书只以Extensionality、Foundation、Pairing和三个固定Separation实例
为理论输入；不使用Infinity、Union、Replacement、Collection或对象AC。
这不宣称ω的无条件存在不需要Infinity；其存在推导见上轮验收。

## 证明构造与覆盖范围
OmegaStructureSyntax固定前驱/分解/传递公式及三个矩阵，并证明重命名、参数替换和量词实例化。
OmegaElementary通过原等词、成员和量词规则证明空集/后继的子集与传递性质。
OmegaStructureInduction将三个完整公式分别代入上轮对象ω归纳：
零/后继分解以一个ω参数；成员属于ω的子集性质以一个ω参数；成员传递性无额外参数。
每次都返回∀全部内部n∈ω的推导，而非只枚举外部标准n。

ObjectIrreflexivity以原Pairing构造实际单元集{x}，对其应用原Foundation取得成员极小元，
由单元集刻画推出该极小元等于x；假设x∈x即与正则性矛盾。
其sentence与native_proof给出真正∀x x∉x的原核闭句，理论输入仅Foundation和Pairing。
不使用宿主WellFounded、内部ω的外部标准性、外部成员良基或Type层选择函数。
OmegaStructureAlgebra再以成员分情况、传递性和不自属证明后继消去。
fresh_successor在实际对象后继见证内部附加不自属证明；可用于旧域为s时的新索引条件s∉s。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0。
8条正式命令全部退出0；Lean4.33.1、LEAN_NUM_THREADS=1。
lake --no-cache --wfail build成功，150个任务。
19源规则及9类ZF与锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
875个列举审计声明：79个无依赖，796个记录允许依赖；0条Lean警告。
本批新增89个审计声明，其中4个无依赖；无sorry/admit或新自定义公理。
有限公理理论上的kernel_certificate仅有propext/Classical.choice/Quot.sound标准依赖；
实际nativeZF回放保留既有7个基础句子FreeClosed证书依赖基线，没有把全项目标成标准三公理。
verification/含实际命令、日志、依赖和源码SHA；未推送远端。

## 下一项与未完成范围
先证明保留完整functionOn的函数图逐点相等推出图相等；再定义内部有限迭代图，
在对象ω归纳中证明每个内部n的实际图存在唯一，以Replacement收集并合并得到传递覆盖。
现有后继新鲜性和相容族合并均为该构造的前置引理，并非迭代本身。
传递覆盖/秩/累积层、源Replacement推导原Collection、两种AC等价、内部ProofZF/U/Con检查器、
任意内部码上的编译器正确性、对象解释/对称强迫和最终Con_ZF→Con_target仍未完成。
OpenAI原4.34.1工程与Comparator尚未运行；没有提高原PP/AC相对一致性结论的完成状态。
