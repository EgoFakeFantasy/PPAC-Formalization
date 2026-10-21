# 实际对象ω：最小归纳集存在唯一、成员刻画与完整归纳模式
日期：2026-10-21；基点f32e37dff0328ec90dd3cc3f9627b2d96ae1128c。
分支migration/yesmeta-step3；原核、源19规则、源ZF九类公理与固定依赖均未改动。
本批完成3b.2b.3a；内部迭代、传递覆盖与最终内部Con主句仍未完成。

## 语言、定义与原Infinity
语言仍是纯成员/等词ℒ；没有添加对象常元、宿主Nat对象域或新推导规则。
Empty(z)与Succ(s,x)严格采用原Source.empty/successor定义；
Ind(i) := (∃z∈i Empty(z)) ∧ ∀x(x∈i → ∃s∈i Succ(s,x))。
OmegaSyntax.infinity_original以rfl证明原Infinity恰为∃i Ind(i)。
U(x) := ∀i(Ind(i) → x∈i)；Omega(w) := Ind(w) ∧ ∀i(Ind(i) → w⊆i)。

原Infinity取得实际对象归纳集I。在I上以矩阵U(x)应用完整Separation，得到
∀x[x∈w ↔ (x∈I ∧ U(x))]。外延性给出空集/后继唯一性，进而证明：
- I中空元属于所有内部归纳集，因此进入w。
- 若x∈w，取I中实际后继s；任意内部归纳集中的后继与s相等，故s亦进入w。
- w中每个元素属于任意内部归纳集，故w是最小归纳集。
所有对象存在见证通过原exI/exE处理，不抽取Type层选择函数。
该存在证明只用原Infinity、Extensionality和一个完整Separation实例。

## 三个固定原核闭句
ObjectOmega给出三公理理论像上的kernel_certificate、源Replacement版ZF的Source.Derives，
以及实际FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)：
1. OmegaSyntax.omegaExists：∃w Omega(w)。
2. ObjectOmega.uniqueSentence：∀w∀v [Omega(w) → (Omega(v) → w=v)]。
3. ObjectOmega.characterizationSentence：∀w [Omega(w) → ∀x(x∈w ↔ U(x))]。
ω的存在、唯一性及成员刻画都已实际推导，未把Omega谓词AST本身当成完成。

## 任意参数公式的对象ω归纳模式
对任意外部模式索引p : Source.Formula (n+1)，OmegaInductionSyntax.sentence p构造完整闭句：
∀参数 ∀w [Omega(w) → (Base(p) → (Step(p,w) → ∀x(x∈w → p(x))))]，其中
Base(p) := ∀z(Empty(z) → p(z))；
Step(p,w) := ∀x∀s(x∈w → (p(x) → (Succ(s,x) → p(s))))。
参数数目与公式复杂度均不受限；多个参数及交错对象量词的实例已验收。

证明在w中分离p的满足者集合S，利用Base/Step与Ind(w)逐对象证明Ind(S)，
再用Omega(w)的最小性得到w⊆S，从精确分离定义推出所有内部成员满足p。
OmegaInduction.kernel_certificate p仅以该p的一个分离实例为理论输入；
native_induction/source_ZF_induction对每个实例返回原核/源ZF的实际推导。
外部n只计数有限变量及模式参数，并不是内部ω成员；证明没有使用外部Lean.Nat归纳
冒充全部内部ω归纳，也没有假定模型的ω外部标准或成员关系外部良基。
保留外部公式模式索引，不引入内部统一真值断言。

## 模块与实际验收
OmegaSyntax/Universal/Cut/Existence/Algebra实现实际ω构造及唯一性/成员刻画；
OmegaInductionSyntax/Cut/Induction实现任意公式归纳模式；ObjectOmega闭合固定句子并回放到原ZF。
C:/Python314/python.exe scripts/verify.py退出0；8条命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，144个任务。
19源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
786个列举审计声明：75个无公理依赖、711个有已记录依赖；0条Lean警告。
新增83个审计声明，其中8个无依赖；固定存在证书及模式kernel_certificate只依赖标准
propext/Classical.choice/Quot.sound，不继承底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；无新自定义公理或sorry/admit。
本批存在性不使用Foundation/Pairing/Union/Replacement/Collection/AC作为逻辑输入；
归纳逻辑核心在给定Omega前提下只用相应分离实例。
verification/保存实际命令、日志、依赖和源码SHA；未推送远端。

## 下一工作与全目标缺口
继续对象ω的空元/后继分解、成员闭包/传递性及图迭代所需的新输入条件。
继而在对象ω归纳中构造全部内部n的唯一迭代图，用Replacement收集后实际合并，构造传递覆盖。
对象递归/秩/累积层、源Replacement证明原Collection、两种AC、内部ProofZF/U/Con与编译器表示、
对象解释/对称强迫及最终内部Con主句均仍待完成。
OpenAI原4.34.1工程与Comparator尚未运行；未宣称原PP/AC相对一致性已经证明。
