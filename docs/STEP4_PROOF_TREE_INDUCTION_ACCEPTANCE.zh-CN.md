# 原ZF内部证明树归纳模式验收（2026-10-24）

本批用原ZF的Foundation、完整Separation及已证明的TransitiveCover，在对象推导中消去全部内部证明码的成员IH。原六类载荷的每个实际child严格小于父码，故可从对象ALL成员IH取得子性质；完整赋值块消去后得到父性质，再由集合归纳闭合整个证明树。7组source／原核／nativeZF闭句已经传输。

这是显式二元对象性质P的条件归纳模式：最终只需Ω及明确写入对象公式的局部闭包条件，不需要IH、给定有效前驱、模型或外部标准性。具体Proof_T的局部闭包条件尚未证明；本批不等于完整Proof_T正确性、Bool对应或最终内部Con。

## 背景及最终目标

对象语言仍为纯等号／成员，背景为原nativeZF及完整Separation／Collection，没有新增对象Choice。最终要求保持：

~~~text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T须覆盖原六规则／27模式、完整理论模式与全部内部ω码。test : Formula 1与P : Formula 2是外部有限公式模式索引；P以对象重命名P[w,p]实例化，不是宿主Prop谓词，也不是内部统一真值谓词。

## 本批准确对象公式

~~~text
Cases_P(w,p) =
 ⋁ kind∈[0,1,2,3,4,5] ∃v0,…,v(k−1).
  EnvNat(w,v) ∧ Ctor(k,tag_kind,w,v,p) ∧
  ⋀ j∈children_kind P[w,vj]

Closure(test,P,w) =
 ∀p∈w. (Table(test,w,p) ∧ Cases_P(w,p) → P[w,p])

Correct(test,P,w,p) = Node(test,w,p) → P[w,p]

MemberIH(test,P,w,p) =
 ∀q∈p. (Node(test,w,q) → P[w,q])

nativeZF ⊢ close(
 Ω(w) → Closure(test,P,w) →
 ∀p. (Node(test,w,p) → P[w,p]))
~~~

Table是准确原六类局部表；Cases_P保留实际payload arities [3,3,4,3,3,5]和children [],[],[2,3],[2],[2],[4]，把子Node性质换为同一显式对象P。Closure在本批最终闭句内是对象蕴含前提，不能在后续具体Proof_T用途里当作已证明事实。

最终∀p遍历全部对象集合。Node的自然码范围由实际载荷构造器推出，用于实例化Closure的p∈w守卫；没有把内部自然数假定为标准Nat，也没有用外部Nat强归纳替代对象集合归纳。

## 实际对象推导

| 模块 | 实现 |
|---|---|
| ProofTreeInductionSyntax | 明确P[w,p]、原children性质、全部赋值Cases_P、Closure、Correct及对象MemberIH；捕获规避重命名 |
| ProofTreeInductionChildren | 从对象ALL实例化成员IH；每个实际child用原载荷字段严格下降得到成员前提；按原列表组合P性质 |
| ProofTreeInductionStep | 各完整赋值分支消去；由准确局部表与P子性质构造Cases_P；实际码自然性及Closure推出父P；六分支析取全部处理 |
| ProofTreeInduction | 原Separation、Foundation、TransitiveCover和SetInduction.all_holds消去IH，取得全部内部Node的性质；原根连接传输性质并导出条件拒绝 |
| ObjectProofTreeInduction | 7组source／sourceZF原核／nativeZF闭句，包含展开后的全域及单点归纳接口 |

SetInduction的矩阵是Node→P这个有限对象公式。所需否定分离实例、Foundation和TransitiveCover均由现有源ZF证据提供，不保留集合归纳已正确的未证外部合同。唯一仍保留的数学前提是具体P的明确对象Closure。

附带的根性质使用上一轮原Root↔Node∧ClosedPayload，由根取得Node后应用内部归纳。若¬P[w,p]，则得到¬Node(test,w,p)及对每个候选结论的¬Root；这些仍以Closure为前提，不是实际Bool拒绝算法的完整正确性。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 5／65／7组 |
| 定向native构建 | 1722项，退出0、零警告 |
| 全仓构建 | 1926项，退出0 |
| 声明审计 | 21345项：424无公理、20921允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立SHA256 | 1752份一致 |
| 全部core／native精确足迹 | 2400对一致 |
| Internal显式覆盖 | 19001项 |
| 上游／锁 | 039c8e132cc19671d73a3933c66b4799d2599dd6干净，7锁不变 |

core依赖恰为propext、Classical.choice、Quot.sound；native另含上游既有7项锁定证书依赖，没有增加信任项或对象Choice。所有新声明显式列入Audit，7个native名称逐项列入依赖检查；sourceguard拒绝宿主谓词／外部Nat归纳替代，检查最终恰为Ω与对象Closure前提。

此前全部跟踪的PPAC证明及接受AST保持Git字节；本批仅4个接入文件、6个文档及5个新模块。证据verification/proof-induction-readback.json、summary.json、commands.json、build.log、audit.log；日志.local/proof-induction-native-directed.log、proof-induction-full-verify.log。验收前基点0e901ed0c5cdb4af135425a58b18e628cae51264；提交后accepted_commit及逐文件Git字节回读记入本地收据。复验C:/Python314/python.exe -X utf8 scripts/verify.py。

编译前检查无遗留工作区Lean／Lake进程，本批未发现可确认退役的脚本或失败诊断，因此删除0文件、停止0进程。保留有效源码、成功证据、生成／回读脚本与缓存。收据.local/workspace-cleanup-proof-induction-result.json。

## 下一步具体工程流程

| 单元 | 实际工作 | 对象验收 | 仍未完成 |
|---|---|---|---|
| N2a，本批完成 | 原六分支child成员严格下降；Foundation／Separation集合归纳 | Ω→Closure→∀p(Node→P)，IH对象消去；根性质及条件拒绝 | 具体Proof闭包 |
| N2b，下一单元 | 任意显式P的实际递归方程；用Node↔P双向成员IH与同一六类载荷逐child传输 | 原闭轨迹节点是该内部下降方程的唯一解；根phase1经原连接处理；所有方程见证／IH消去 | 专用Bool／Proof对应 |
| T1 | 原完整ZF/U理论模式和实际公式编码 | 实例化Formula1测试，完整Separation／Collection，核查纯EqMem／扩展签名与上下文 | 专用测试未实现部分 |
| P1 | 原六规则／27模式、全部内部ω、实际执行表示 | 专用Proof_T AST与共享Bool对应；证明其局部Closure／方程并实例化本批归纳；内部编译与源推导传输 | 内部解释／Con |
| I1 | ZF+PP+ACwo+¬AC实际内部翻译 | 内部数学解释与证书转换，逐项对象证明背景依赖 | 最终Con |
| C1 | 完整Proof_ZF／Proof_target和以上对象推导 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 达成前不得置true |

N2b的唯一解定理仍须把递归方程作为明确对象前提，实际Bool／Proof_T用途必须另行证明该方程。不能用通用条件定理冒充专用检查器正确性，更不能改写最终Con目标。当前专用Proof闭包、全部内部检查器正确性、内部解释与Con门保持false。未恢复退役反射，未推送远端。
