# 原证明树根关闭性与精确结论字段验收（2026-10-24）

本批从未改动的原12分支推出根入口的准确双条件：根入口等价于同一载荷的节点入口，加上六类实际载荷中的自由变量数字段为0、结论字段等于候选结论。反向实际构造数值根行、原守卫和闭轨迹，没有假定根已有效。8组闭句已通过既有源推导传输返回原FirstOrder.Derives nativeZF []。

test : Formula 1仍是显式对象公式参数；节点入口仍含此前接受的真实闭轨迹。本批尚未完成节点可靠性归纳、原共享Bool对应、专用ZF/U测试、Proof_T／内部编译与数学解释或最终内部Con。

## 对象层背景与主公式

语言为纯等号／成员；背景保持原nativeZF、完整Separation／Collection，不新增对象Choice。最终目标保持：

~~~text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

专用Proof_T仍须覆盖原六规则／27模式、完整理论模式及全部内部ω码。本批主定理是下列公式的原核闭包：

~~~text
Ω(w) →
 (Root(test,w,p,c) ↔ Node(test,w,p) ∧ ClosedPayload(w,p,c))

ClosedPayload(w,p,c) =
 ⋁ kind∈[0,1,2,3,4,5] ∃v0,…,v(k−1).
   EnvNat(w,v) ∧ Ctor(k,tag_kind,w,v,p) ∧ Empty(v0) ∧ v1=c
k = [3,3,4,3,3,5][kind]
~~~

kind及固定字段数是外部公式模式索引；全部运行数码p、c、vi、行码与轨迹都是对象变量／量词，覆盖全部内部ω。最终双条件只有Ω对象前提；无给定轨迹、载荷、有效前驱、测试正确性、IH或模型前提。Empty(v0)描述载荷的自由变量数字段，不能单独充当专用Proof_T可靠性。

## 实现与原核传输

| 模块 | 实际对象推导 |
|---|---|
| ProofTreeConstructorFacts | 构造器自然值域，同一码的指定字段相等；内部索引对象构造／消去 |
| ProofTreeZeroGuard | Num1非空、u∈Num1↔Empty(u)，原var0<literal1↔Empty(v0) |
| ProofTreeTraceQuery／BranchHead | 真实递归前提和node／root头对应准确数值构造器，不调用宿主求值 |
| ProofTreeRootLocal | 原裸tag投影在实际tag1上取Num1，推出原局部条件 |
| ProofTreeEntryFacts／RootSyntax | 重命名、载荷相等传输、独立六类载荷规格 |
| ProofTreeRootForward | 枚举原12分支，tag0／tag1互斥及同码字段唯一性，消去全部赋值／载荷EX |
| ProofTreeRootBackward | 构造实际根行、原严格守卫、节点前提及闭轨迹 |
| ObjectProofTreeRoot | 8组source／sourceZF原核／nativeZF闭句 |

独立ClosedPayload规格没有头表达式图、搜索界、guard、闭轨迹或递归方程。Node入口明确保留在主定理中。CheckStep4包含展开后的主双条件；Audit覆盖全部新声明。verify.py逐名列出新增native证书，没有扩展信任锁。

## 实际验收

| 项目 | 实测 |
|---|---|
| 新模块／显式声明／原核闭句 | 10／77／8组 |
| 定向native构建 | 1712项，退出0、零警告 |
| 全仓构建 | 1914项，退出0 |
| 声明审计 | 21210项：424无公理、20786允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立SHA256 | 1740份一致 |
| 全部core／native精确足迹 | 2384对一致 |
| Internal显式覆盖 | 18866项 |
| 上游／锁 | 039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core依赖恰为propext、Classical.choice、Quot.sound；native另含上游既有7项锁定证书依赖。没有增加信任项，也没有把Lean的Classical.choice当作对象Choice。此前全部跟踪的PPAC证明／接受AST保持原Git字节，仅4个工程接入文件和6个文档改动，加10个新模块。

证据：verification/proof-root-readback.json、summary.json、commands.json、build.log、audit.log；定向及全仓日志.local/proof-root-native-directed.log、proof-root-full-verify.log。验收前基点bbffc176127354f1b2c8b19c86625c12c5ae28a5；按仓库eol=lf统一后重新全仓验收，提交后accepted_commit及逐文件Git字节回读写入本地收据。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。

## 清理与下一步工程表

全仓编译前确认无遗留工作区Lean／Lake进程；删除9份已被成功构建替代的失败日志，共19927逻辑字节，未终止其他应用或删除有效脚本／缓存。盘面空闲实测由103867760640变为103867666432字节，净减少94208字节；逻辑删除量不能宣称为盘面净增。收据.local/workspace-cleanup-proof-root-result.json。

| 步骤 | 输入／实际工作 | 对象层验收产物 | 尚未达成 |
|---|---|---|---|
| R1，本批完成 | 原12分支、数值头、严格guard、字段唯一性 | 原核Ω→(Root↔Node∧ClosedPayload)，无外加有效根／轨迹 | 最终Con |
| N1，下一单元 | node0入口；排除root1，消去tag0／field0局部条件，规范化六类children | Node与六类载荷／准确局部表／各子Node的对象双条件，赋值EX消去 | 完整可靠性／Bool |
| N2 | 全部内部子码严格下降，根phase1到nodephase0 | 原2*payload+phase或等价双层内部归纳，消去IH | 专用Proof与Con |
| T1 | 原完整ZF/U理论模式与实际公式编码 | 实例化Formula1测试，完整Separation／Collection；核查纯EqMem／扩展签名对应 | 未实现Proof |
| P1 | 六规则／27模式、全部内部ω及真实程序 | 专用Proof_T AST、原共享Bool对应、内部编译／源推导传输 | 内部解释与Con |
| I1 | 目标ZF+PP+ACwo+¬AC及实际内部翻译 | 内部数学解释与证书转换，背景依赖逐项对象证明 | 最终Con |
| C1 | 完整Proof_ZF／Proof_target与以上推导 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 达成前不得置true |

根关闭性已单独完成；此前“秩归纳／根关闭性／完整检查器”的合取门仍为false，因为其他合取项未完成。新增独立根定理门为true。未恢复退役反射实现，未推送远端。Agent广场同步只在API成功回执后计为完成。
