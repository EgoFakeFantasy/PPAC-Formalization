# 原证明树六类节点及精确子节点方程验收（2026-10-24）

本批将原node0入口化为准确六类局部表，加上原六种载荷及各实际子Node的对象双条件。tag0投影、field0载荷、12分支、完整赋值块和头图见证全部在对象推导中处理。正向排除root1分支，反向实际构造node0行、原局部条件与闭轨迹，未假定父节点已有效。细化后的root方程沿上一轮根关闭性定理组合返回原nativeZF推导核。

本批仍是显式test : Formula 1参数下的纯关系方程。子Node入口明确留在结论中，没有伪装为完整可靠性归纳；专用ZF/U测试、原共享Bool对应、完整Proof_T／内部编译／数学解释及最终内部Con仍未完成。

## 对象语言、背景与目标

纯等号／成员对象语言；背景保持原nativeZF与完整Separation／Collection。最终要求仍是：

~~~text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖原六规则／27模式、完整理论模式及全部内部ω码。本批主公式在原核中闭包：

~~~text
Ω(w) → (Node(test,w,p) ↔ Table(test,w,p) ∧ Cases(test,w,p))

Cases(test,w,p) =
 ⋁ kind∈[0,1,2,3,4,5] ∃v0,…,v(k−1).
  EnvNat(w,v) ∧ Ctor(k,tag_kind,w,v,p) ∧
  ⋀ j∈children_kind Node(test,w,vj)

Ω(w) →
 (Root(test,w,p,c) ↔
  (Table(test,w,p) ∧ Cases(test,w,p)) ∧ ClosedPayload(w,p,c))
~~~

Table是此前已验收的准确六类局部表，公理Kind的test参数未被假定为ZF/U识别器。ClosedPayload是上一轮六类实际载荷、free字段0和结论字段=c的独立规格。k及children依照实际原形状：

| kind | k | children |
|---|---|---|
| logical | 3 | 空 |
| theory | 3 | 空 |
| MP | 4 | 2、3 |
| forall | 3 | 2 |
| strengthening | 3 | 2 |
| substitution | 5 | 4 |

固定kind与列表是外部有限公式模式索引；全部运行数码、赋值、实际行、投影及轨迹见证均为对象变量／量词，覆盖全部内部ω，不假设外部标准性或有限证明。主双条件只有Ω(w)对象前提，没有给定有效父节点、局部测试真值、IH或模型前提。

## 实现与验收边界

| 新模块 | 对象推导及用途 |
|---|---|
| ProofTreeNodeFieldLocal | 原实际constructor1tag0的field0查询唯一等于payload；替换到准确Table；零索引由对象Num0构造／消去 |
| ProofTreeNodeTag | 实际裸tag0投影的对象见证，功能性对齐所有候选；消去emptyTag→atZero条件，得到Local↔Table(payload) |
| ProofTreeChildren | 原每个child表达式查询↔实际Node；按原顺序组合完整children列表，并提供逐child消去 |
| ProofTreeNodeSyntax | 独立payload Cases及外层准确Table；字段数／children直接来自原shape；任意字段严格小于父码 |
| ProofTreeNodeForward | 原12分支和完整赋值块展开，tag1互斥排除；同码field0唯一性对齐载荷，全部见证对象消去 |
| ProofTreeNodeBackward | 从六类载荷与实际子Node构造原节点头、空guards、局部条件和真实闭轨迹；组合节点／细化根双条件 |
| ObjectProofTreeNode | 9组source／sourceZF原核／nativeZF闭句，包括展开后的节点及根主契约 |

独立Cases规格没有头表达式图、搜索界、guard、闭轨迹或展开方程；它显式使用各实际子Node入口。准确Table也明确位于主结论外层，未藏入未证明的有效性谓词。字段严格下降已是对象推导，但尚未把它组成整个节点递归的内部Foundation归纳。

CheckStep4同时展开节点及细化根契约。Audit显式列出全部新声明；verify.py精确检查原构造、最终仅Ω前提与9项逐名native信任范围，未扩大信任锁。原接受AST、上游程序与全部既有证明均保持Git字节。

## 实际验收结果

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 7／70／9组 |
| 定向native构建 | 1718项，退出0、零警告 |
| 全仓构建 | 1921项，退出0 |
| 声明审计 | 21280项：424无公理、20856允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立SHA256 | 1747份一致 |
| 全部core／native精确足迹 | 2393对一致 |
| Internal显式覆盖 | 18936项 |
| 锁／上游 | 7锁不变；039c8e132cc19671d73a3933c66b4799d2599dd6干净 |

core依赖恰为propext、Classical.choice、Quot.sound；native另含上游既有7项锁定证书依赖。没有新增对象Choice或信任项。仅4个工程接入文件、6个文档及7个新模块进入本批提交。

证据：verification/proof-node-readback.json、summary.json、commands.json、build.log、audit.log；.local/proof-node-native-directed.log、proof-node-full-verify.log。验收前基点3955d9a81aaad539c9b63c4945ed75c0b1210757；提交后accepted_commit和逐文件Git字节回读记入本地收据。源文件按仓库LF规则写入。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。

编译前确认没有遗留工作区Lean／Lake进程，删除1份被成功构建替代的失败日志1332逻辑字节；盘面空闲实测增加4096字节，未停止其他应用或删除有效脚本／源码／缓存。收据.local/workspace-cleanup-proof-node-result.json。

## 下一步的agent工程流程

| 单元 | 输入及实际工作 | 对象层交付／验收 | 未完成门 |
|---|---|---|---|
| N1，本批完成 | 真实node0、12分支、tag0／field0、原children | 原核Ω→Node六分支方程，细化Root方程；所有赋值和行见证消去 | 最终Con仍false |
| N2a，下一单元 | 本批字段严格下降及完整六分支方程 | 对任意显式对象性质公式建立证明树内部归纳；从各子Node及成员IH推出父性质，原SetInduction.all_holds消去IH | 实际Bool／专用Proof仍false |
| N2b | 原phase1根连接和payload内部归纳 | 与原rank=2*payload+phase或等价双层结构对应；全部内部码的正负／唯一行为，不用外部Nat归纳替代 | 完整检查器门未达成前false |
| T1 | 完整ZF/U理论模式及准确编码 | 实例化Formula1参数；完整Separation／Collection；核对纯EqMem／扩展签名与上下文 | 专用Proof未实现部分false |
| P1 | 原六规则／27模式与全部内部ω | 专用Proof_T AST、原共享Bool对应、内部编译与源推导传输 | 解释与Con仍false |
| I1 | ZF+PP+ACwo+¬AC及内部翻译 | 实际内部数学解释与证书转换，逐项证明背景依赖 | 最终Con仍false |
| C1 | 以上实际对象推导及两个完整Proof谓词 | FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 达成前不得置true |

N2a可用纯对象性质公式作外部模式索引，闭句明确把六类局部闭包条件写为对象前提；必须在具体可靠性用途内消去该闭包条件，不能把任意性质的条件归纳定理冒充最终Proof_T正确性。构建成功、参数化公式、有限实例与语义模型均不是最终Con交付。未恢复退役反射实现，未推送远端。
