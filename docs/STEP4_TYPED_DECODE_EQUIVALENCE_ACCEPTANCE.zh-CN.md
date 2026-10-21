# 完整TypedData双向识别验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点0d34d620326b41144ef611e59a89637bab897f0c。
R1至R4已完成：真实槽位恢复全内部字段图和原森林，再恢复同根构造器，关闭完整类型识别的反向缺口。
新增9模块141项显式声明、25个完整Source/sourceZF核/nativeZF核闭句模式。

## 对象合同及边界

背景仍为原YesMetaZFC的ZF纯成员语言像；证书终点仍为原FirstOrder.Derives nativeZF [] φ。
无新增对象公理、AC、不可达或一致性假设。没有借模型语义或宿主完备性取得结论。
w、码、bound/free上下文、payload、内部长度、完整函数图、索引和值均为对象变量。
外部Nat/Fin及有限字段向量仅索引有限公式模式，每个实例返回实际闭句Derives。
实际字段值只经原对象exE消去；没有从Prop抽取Type层的字段数组。

## R1：实际槽位恢复所有内部边

Slots(k,g,xs)为有限对象合取，逐一断言原Slot(g,j,xs_j)。
Slots不是只在标准样本上检查图：原完整Fields给出functionOn及ω范围，
原数码唯一性把每个实际Slot索引传到任意同数码索引；原函数单值性恢复实际边值。
Num_k(l)的内部成员恰为Num_0至Num_(k-1)，因此全内部候选满足：

∀i∀y (Edge(g,i,y) ↔ Positions(k,xs,i,y))。

同时每个实际字段自然，正式得到原Inputs(k,w,xs)。
零字段情形由原空定义域推出无边，不假定某个图恰为空。

## R2：恢复同一payload的原森林

从Inputs实际构造一个原Forest q；其实际长度为同一个内部l。
原Replacement取得q的实际完整字段图h，其全内部位置定律与g一致。
原图外延性得到h=g；字段图的对象等词替换将Fields(q,l,h)传到Fields(q,l,g)。
原列表码唯一性在共同l和共同完整g上得到q=p，最后通过对象等词替换得到Forest(k,w,xs,p)。
实际Shape提供原标签自然性及Raw配数，故正式恢复同一个根n的Constructor(k,tag,w,xs,n)。
整个反向接口不预设Constructor或payload相等。

## R3：完整类型数据反向识别

| 原标签 | 实际字段数 | 真实检查及恢复 |
|---|---|---|
| 0、1 | 0 | 完整Ctx，恢复原零字段常量 |
| 2 | 3 | 原0符号、两个同上下文Term的真实Checked槽位 |
| 3 | 2 | 两个同上下文Term槽位 |
| 4 | 1 | 同上下文子FormulaCode槽位 |
| 5至8 | 2 | 两个同上下文子FormulaCode槽位 |
| 9、10 | 1 | 真实Succ(u,b)下的子FormulaCode(u,f)，free保持不变 |

RootCheck实际给出每个所需槽位的对象存在量词。
零至三个字段逐一使用原exE，重建Constructor时保留完整原RootCheck。
之后应用既有已知构造器类型双条件的反向，得到同根FormulaCode。
量词的真实内部后继、原membership编号0符号和全部Term作用域由原检查保持，没有改成宿主条件。

由完整有限Cases对象析取消去，取得任意内部候选上的：

Ω(w) → (TypedData(w,n,b,f,t,p,l,g) → FormulaCode(w,n,b,f))。

TypedData定义没有放入父FormulaCode；递归字段检查使用实际子码。
反向只需其中的Shape及完整Cases，但与已证正向组合后自动保留全部原树子有效性。

## R4：完整识别闭句

给定任意同根真实Shape，原核证明：
Code ↔ TypedData，以及Code ↔ Cases(11)。
在全部候选n,b,f上，只需Ω(w)，原核证明：
Code ↔ TypedFiber，以及¬Code ↔ ¬TypedFiber。
TypedFiber实际存在tag、payload、长度、完整字段图及对所有同根Shape的四分量唯一性。
另有(Code∧TypedFiber)∨(¬Code∧¬TypedFiber)完整正负分类。

关键原核证书位于ObjectFormulaCodeTypedDecode：
native_forestRecover、native_constructorRecover、native_rootCheck、
native_dataCode、native_dataIff、native_fiberIff、native_rejectFiberIff、native_classification。
这些证书覆盖全部内部ω候选及所有上下文，不限制外部标准码。

## 实际机器验收

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令全部退出0：两份源锁检查、版本检查、全仓wfail构建、
Check/CheckStep2/CheckStep3/CheckStep4和Audit共五个trust=0入口。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 665 jobs，退出0 |
| 全声明审计 | 6819项；254项无公理，6565项允许依赖 |
| 警告 | 0 |
| Internal显式声明覆盖 | 4504项，无漏审 |
| 本批闭句模式 | 25对核心/native精确足迹 |
| 累计闭句模式 | 527对核心/native精确足迹 |
| 源码SHA256独立回读 | 634份，差异0 |
| 九命令及五trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

核心证书精确依赖propext、Classical.choice、Quot.sound；
native证书另含原七个固定ZF定义证书的既有依赖，未新增自定义公理。
额外原choice证书仍限制在原choice桥中，本批25对证书不含它。
源码哈希、九命令退出、25对足迹、锁和固定依赖另作独立回读，
记录在忽略目录verification/typed-decode-equivalence-readback.json。

## 门禁和下一步

object_typed_data_reverse_recognition_proved、
object_actual_complete_recursive_typed_data_decode_and_reverse_recognition_proved、
object_all_eleven_formula_constructors_type_check_proved现为True。

任意内部非单射捕获规避rename/替换、专用ProofZF/U完整AST、
全内部证明码正确性、内部编译器以及最终对象Con蕴含仍未实现，相关门禁保持False。
下一单元4c.c从完整内部映射图的RenameTerm/RenameFormula纯AST和量词下真实提升开始。
完整工程流程已按这一边界修订；完整类型识别不能替代最终Derives nativeZF [] (Con_ZF→Con_target)。

原OpenAI完整构建及Comparator本批未运行；未推送；本地探针、日志及回读不作为发布内容。
