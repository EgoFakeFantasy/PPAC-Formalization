# 原证明树递归方程唯一性及规范解验收（2026-10-24）

本批证明：任意显式二元对象公式P若满足原六分支递归方程，就在全部对象码上等价于原Node入口。正向局部Closure由方程实际推出；反向IH用原ZF Foundation／Separation／TransitiveCover消去。原Node的实际有限Formula2模板也已构造，并在只有Ω前提下证明满足该方程，未把规范解存在性留作合同。

本批提供9组source／原核／nativeZF闭句。候选P的唯一性仍明确以其对象方程为前提；实际Bool／专用Proof_T的方程尚未证明。它不是完整Proof_T正确性、内部数学解释或最终Con。

## 背景与最终目标

对象语言为纯等号／成员，背景保持原nativeZF、完整Separation／Collection，不加入对象Choice。最终要求不变：

~~~text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T须覆盖原六规则／27模式、完整理论模式与全部内部ω码。test : Formula 1和P : Formula 2是外部有限对象公式模式索引，运行码与赋值在对象量词中；不存在宿主Prop测试或内部统一真值断言。

## 准确对象方程与结论

~~~text
Normalized(test,P,w,p) = Table(test,w,p) ∧ Cases_P(w,p)

Equation(test,P,w) =
 ∀p. (P[w,p] ↔ Normalized(test,P,w,p))

nativeZF ⊢ close(
 Ω(w) → Equation(test,P,w) →
 ∀p. (Node(test,w,p) ↔ P[w,p]))

nativeZF ⊢ close(
 Ω(w) → Equation(test,nodeTemplate(test),w))
~~~

Cases_P使用准确六类payload arities [3,3,4,3,3,5]与children [],[],[2,3],[2],[2],[4]，全赋值EX内部绑定。Table是已验收的完整六类局部检查，公理Kind仍显式参数化。

Equation对全部对象集合p量化，没有p∈w外层守卫。若只在ω内给方程，任意P在ω外取真将破坏全域等价。实际方程加上Ω会推出P的所有接受码都在w内；这一自然范围已有单独对象定理。

nodeTemplate(test)是实际Node入口的有限Formula2 AST。模板实例化、children、matrix、body、branch、Cases及Normalized与原Node规格逐层相等，因此规范方程由此前Node六分支双条件推出，而非自定义一个预设满足方程的宿主谓词。

## 实际推导及原核传输

| 模块 | 对象层工作 |
|---|---|
| ProofTreeEquationSyntax | 全对象域Equation、反向Correct／成员IH、重命名、方程实例化；方程实际推出正向Closure |
| ProofTreeEquationReverseStep | 从P子性质与真实字段严格下降取得Node子入口，原全部赋值块／六分支对象消去，重建真实Node |
| ProofTreeEquationUnique | 反向Foundation归纳消去IH，组合正向归纳取得全域／单点唯一性；两解等价、精确Root连接、接受码自然性 |
| ProofTreeEquationCanonical | 实际Node模板及逐层公式相等；只有Ω前提的规范Equation对象证明 |
| ObjectProofTreeEquation | 9组source／sourceZF原核／nativeZF闭句及展开后的主验收接口 |

原SetInduction.all_holds的Foundation、否定分离实例及TransitiveCover均由源ZF证据提供。正向使用上一轮对象归纳，但Closure在本批由Equation消去，不作为最终唯一性额外前提。反向把P父节点的实际方程展开成真实载荷，按子码成员IH重建Node；没有假设P父节点已对应有效证明。

附带结果包括Root(test,w,p,c)↔(P[w,p]∧ClosedPayload(w,p,c))、任意两个方程解逐点等价、原Node及任意候选解接受码的自然范围。Root的free=0和精确结论字段保持原ClosedPayload，未省略候选结论。

规范模板局部标记irreducible仅控制Lean elaboration的自动展开；所有公式相等和规范Equation仍经原推导核检查，不改变信任或对象公理。此设置用于避免深层Node AST被congruence自动反复展开。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 5／72／9组 |
| 定向native构建 | 1726项，退出0、零警告 |
| 全仓构建 | 1931项，退出0 |
| 声明审计 | 21417项：424无公理、20993允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立SHA256 | 1757份一致 |
| 全部core／native精确足迹 | 2409对一致 |
| Internal显式覆盖 | 19073项 |
| 上游／锁 | 039c8e132cc19671d73a3933c66b4799d2599dd6干净，7锁不变 |

core依赖恰为propext、Classical.choice、Quot.sound；native另含上游既有7项锁定证书依赖。未增加对象Choice或信任项。所有声明均显式列入Audit，9项native证书逐名检查。sourceguard检查全对象域方程、规范解最终只需Ω、唯一性只需Ω与Equation；CheckStep4展开两项主公式。

此前全部跟踪的PPAC证明及接受AST保持Git字节。本批仅4个接入文件、6个文档及5个新模块。证据verification/proof-equation-readback.json、summary.json、commands.json、build.log、audit.log；.local/proof-equation-native-directed.log、proof-equation-full-verify.log。验收前基点8c580c922ae342451bcff4c96969c169c410f3f0；提交后accepted_commit和逐文件Git字节回读记入本地收据。复验C:/Python314/python.exe -X utf8 scripts/verify.py。

全仓编译前确认无遗留工作区Lean／Lake进程；删除1份已由成功构建替代的失败日志2827逻辑字节，盘面实测增加4096字节。未停止其他应用或删除有效源码／脚本／缓存。收据.local/workspace-cleanup-proof-equation-result.json。

## 后续具体工程流程

| 单元 | 实际工作 | 对象层验收 | 未完成门 |
|---|---|---|---|
| N2b，本批完成 | 全对象域方程、双向内部归纳、实际Node模板 | Ω→Equation→全域Node↔P；Ω→规范Equation；正向Closure和反向IH消去 | 实际Bool／Proof方程false |
| T1.0，下一单元 | 锁定Contract.nativeZF的纯成员像及targetTheory；精确证书类型、数值编码与两种schema | 七条固定ZF公理、全部Separation／Collection及目标PP／ACwo／¬AC的实际公理测试规格；不加入Choice | 专用完整测试未达成前false |
| T1.1 | 先接七固定公理及目标三个实际闭句的结构数码；同码／错误分支对齐 | 有限固定分支的准确对象双条件；标明尚未覆盖schema | 完整测试false |
| T1.2 | 全内部参数数目、实际schema体、语法／闭性及实例化 | 完整Separation／Collection专用Formula1测试；源Replacement与原Collection编码需形式传输 | 达成前专用测试false |
| P1 | 六规则／27模式、全部内部ω、实际共享Bool／编码 | 专用Proof_T AST及其实际Equation，实例化本批唯一性；内部编译与源推导传输 | 内部解释／Confalse |
| I1 | ZF+PP+ACwo+¬AC的实际内部翻译 | 内部数学解释与证书转换，背景依赖逐项对象推导 | 最终Confalse |
| C1 | 完整Proof_ZF／Proof_target及以上推导 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 达成前不得置true |

T1不能直接采用上游ProofT/ZFC的完整呈现：该呈现含Choice及公共支撑理论，与Contract.nativeZF不同。上游ProjectDecode的schema AST还包含subset及扩展签名／闭性约定，须核查纯EqMem编码和上下文对应，不能默认与既有纯语法AST相同。SourceTheory使用Replacement，nativeZF使用Collection，两者已有推导传输，但数值公理测试也须实际对齐。

本批只为具体Bool／Proof_T正确性提供已证明的唯一性接口，不能省略其方程、专用理论测试、内部编译与数学解释。最终Con等门保持false；未恢复退役反射实现，未推送远端。
