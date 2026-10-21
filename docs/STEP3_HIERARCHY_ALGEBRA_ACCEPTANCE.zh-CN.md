# 层成员递归、单调传递及后继幂集验收
日期：2026-10-21；基点854951811efa48ba8a6d018e00d144c94daa7d60。
分支migration/yesmeta-step3；极限层、秩覆盖及最终内部Con主句仍未完成。

## 对象范围与实际闭句
对象签名仍为原单排序纯等词/成员语言，背景仍为原nativeZF，终点仍为FirstOrder.Derives nativeZF [] φ。
所有α、β、f、h、s、y、v、z量词均遍历全部内部集合；Ord严格是原Source.ordinal，未限制外部标准序数。
对象层Layer沿用实际后继域上的完整递归图在该索引处的原Kuratowski输出边定义。
ObjectHierarchyAlgebra提供七条闭句，每条都有source_*、*_kernel_certificate和native_*：

| 闭句 | 完整数学内容（仅用缩写展示原纯对象公式） |
|---|---|
| historySentence | ∀α,h,β,v[Ord(α)→Graph(h,α)→β∈α→(Edge(h,β,v)↔Layer(β,v))] |
| operationSentence | ∀α,h,y,z[Φ(α,h,y)→(z∈y↔∃β∃v(β∈α∧Edge(h,β,v)∧z⊆v))] |
| membershipSentence | ∀α,y[Ord(α)→Layer(α,y)→∀z(z∈y↔∃β∃v(β∈α∧Layer(β,v)∧z⊆v))] |
| monotoneSentence | ∀α,β,u,v[Ord(α)→Ord(β)→Layer(α,u)→Layer(β,v)→β⊆α→v⊆u] |
| memberSentence | ∀α,β,u,v[Ord(α)→Layer(α,u)→β∈α→Layer(β,v)→v∈u] |
| transitiveSentence | ∀α,y[Ord(α)→Layer(α,y)→TransitiveSet(y)] |
| successorSentence | ∀α,s,u,v[Ord(α)→Succ(s,α)→Layer(α,u)→Layer(s,v)→PowerOf(v,u)] |

每处⊆量化全部内部成员，PowerOf(v,u)严格是∀z(z∈v↔z⊆u)。
闭句中没有未证算子总性/单值性前提，没有宿主层powerset、WellFounded或模型满足谓词。

## 原规则证明路线
HierarchyHistory正向用原Pairing/Union实际构造β后继s，由Ord成员闭包及后继保持取得Ord(s)。
α传递给s⊆α，一个原Separation实例实际取得h在s上的限制图g，并保留完整Recursor。
限制边规律给Edge(g,β,v)，因此得到Layer(β,v)，无需先假定Layer存在。
反向消去实际Layer见证的后继域和图，以递归图相容及精确域包含把原边传回h。

PowerUnionMembership由实际并集成员先取得实际幂集像成员P，再取得实际β和输出v，
用PowerOf(P,v)得到z⊆v。反向从真实β/v/子集见证调用原PowerSet取得实际P，
精确像给P∈C，再由并集成员规律给z∈y。没有在宿主选择幂集或输出族。
HierarchyMemberTransfer在两个内部存在式间逐见证替换早期边和Layer。
HierarchyMembership从实际α层见证的递归方程取得历史h，验证其在α上仍是完整递归图，
从而得到完整层成员递归式；原历史限制集合未被丢掉或仅当作字段假设。

HierarchyAlgebra将β⊆α传到成员式中的每个早期索引，取得层包含单调性。
取z=v及v⊆v得到β∈α时Vβ∈Vα。任意z∈Vα给z⊆Vβ，
而Vβ⊆Vα，从而z⊆Vα；据此得到原TransitiveSet公式的推导。
HierarchySuccessor把内部索引β∈α+1分成β∈α或β=α。
旧位置由成员递归和层传递性推出z⊆Vα，新位置用层值唯一和对象等词替换得到同一包含。
反向以α本身作为内部索引见证，因此后继层确为原PowerOf(Vα)，不是仅有一个包含方向。

## 可信基和工程边界
八个新模块的全部76个显式声明加入Audit；包括AST构造、重命名、实际见证消去、原规则证明和原核端点。
七条*_kernel_certificate以完整source Replacement ZF的句子像为背景，只允许既有三项标准Lean依赖。
native_*回放按既有nativeZF固定七句FreeClosed证书的native_decide.ax_1基线审计，未新增自定义公理。
源证明不使用Collection或对象AC；nativeZF含原Collection不能据此误称反向完整Collection已证。
CheckStep3直接检查原Source.ordinal、全部内部双存在/子集量词、完整成员递归及后继PowerOf AST，
并以实际原核Derives类型接合全部七个native端点。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成259个任务。
源19规则、9类ZF及锁定SHA核对通过，Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1854个声明：147个无公理依赖、1707个记录允许依赖；0条Lean警告。
新增76个审计声明，其中3个无公理依赖；七条新增*_kernel_certificate的依赖逐条实际核对
恰为propext/Classical.choice/Quot.sound。nativeZF端点仅继承既有固定七句证书基线。
226个验收文件实际SHA256复核一致，未新增sorry/admit、unsafe、自定义公理或外部良基/标准性前提。
定向构建时修正闭句装配中局部上下文未定元，显式给出完整Source上下文；最终串行全验收通过。
实际命令、日志、依赖与哈希保留于本地verification/，不作为自动发布材料。

## 下一项
先定义原纯语言的内部极限索引条件，并证明极限层正是全部早层的并；
再证明非空可定义序数性质的实际唯一最小元模式，以全Replacement及任意序数族严格界推进秩覆盖。
不能把层存在唯一、层传递或后继幂集等式当作每个集合已有秩。
全局ω图、最小传递闭包、反向完整Collection、两种AC、专用内部ProofZF/U/Con AST及代码正确性、
对象解释/对称强迫和最终Con_ZF→Con_target的原核对象证明仍未完成。
OpenAI原4.34.1构建与Comparator仍未运行，未推送远端。
