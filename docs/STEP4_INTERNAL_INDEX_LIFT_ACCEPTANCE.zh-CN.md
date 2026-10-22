# 实际量词绑定映射提升验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点75ba640a608dbd1f0b90174b12a9568918fd14a5。
L1、L2、L3完成：任意参数对象函数关系的实际唯一完整图，量词下实际绑定映射提升，以及原项重命名兼容性。
新增15模块236项显式声明、35个完整Source/sourceZF核/nativeZF核闭句模式。
完整公式重命名、捕获规避替换、ProofZF/U及最终内部Con蕴含仍未完成。

## 对象合同

背景仍为原ZF的纯等词/成员语言像；证书终点仍为原FirstOrder.Derives nativeZF [] φ。
不加入AC、不可达、Con或新推导核。所有索引、长度、图、后继和候选值均为对象变量。
外部关系矩阵P和参数个数只索引对象句子模式，每个实例均有真实闭句推导。
图、值和后继的见证全部经原exE取得并消去，没有从Prop抽取宿主函数或集合数据。
自然数范围始终为内部ω，允许模型外部非标准；不以宿主Nat枚举内部输入。

## L1：任意功能关系的实际完整图

对任意纯公式矩阵P、全部对象参数ρ及任意内部域集合d，假定对象：
∀x∈d ∃!y P(ρ,x,y)。

先对每个实际x构造原Kuratowski对p=(x,y)，利用关系唯一性及原有序对唯一性证明p唯一。
原Replacement作用于这个索引对矩阵，取得全部且仅有这些索引对的实际精确像g。
逐实际成员见证证明g无杂项，再恢复全部内部x,y上的精确式：
Edge(g,x,y) ↔ (x∈d∧P(ρ,x,y))。

原关系总性和唯一性给每个域内输入的原valueAt，故g满足完整原functionOn。
任意两个满足同一完整图合同的集合图，由原图外延性相等；实际唯一图纤维已证明。
若关系输出限制在c，还证明Sequence(g,d,c)。域d不限于内部有限自然数。
关键证书：native_graphExists、native_graphFiber、native_graphUnique、native_pairEdge、native_graphSequence。

## L2：量词下实际绑定映射提升

原native VariableRenaming.lift采用头槽约定：新here映到here，旧there(k)映到there(r(k))。
对应内部提升值关系固定为：
Value(r,a,i,j) :=
(Zero(i)∧Zero(j)) ∨ ∃k,l(k∈a∧Edge(r,k,l)∧Succ(i,k)∧Succ(j,l))。

给定实际IndexMap(w,r,a,c)、u=Succ(a)、v=Succ(c)，证明：
每个内部i∈u实际存在唯一j满足Value，且j∈v。
证明实际使用内部零/后继分解、原自然序数传递性、前驱单射和原图单值性；
没有将完整后继域限制为外部标准点。

把Value矩阵实例化L1，实际取得完整g:u→v。
其原图边对所有内部候选精确等价于Value，额外域守卫由原序界证明消去。
同时证明以下原核双条件：

| 候选 | 实际对象结论 |
|---|---|
| 任意内部i,j | Edge(g,i,j)↔Value(r,a,i,j) |
| 实际零z、任意内部y | Edge(g,z,y)↔Zero(y) |
| k∈a、i=Succ(k)、j=Succ(l) | Edge(g,i,j)↔Edge(r,k,l) |

实际提升图对全部候选图唯一。
进一步原Pairing/Union实际构造u和v，与唯一完整g联合绑定；
只需Ω和原IndexMap，即得到实际提升系统，不残留后继存在前提。
关键证书：native_liftFiber、native_liftAll、native_liftZero、native_liftSuccessor、native_liftSystem。

## L3：与原项重命名兼容

给定原bound/free完整图(r,s)和实际提升图g，新的完整图对是(g,s)。
原对象推导证明：

- 新绑定变量的原零索引码实际自重命名，原码保持不变。
- 每个旧bound边k→l，在真实后继索引Succ(k)→Succ(l)下满足原项重命名。
- 每个free边继续使用原s及原索引，穿过量词时不改变。

这些结论返回实际RenameTerm关系并保留全部源/目标作用域，
没有只交付宿主AST上的lift等式。
关键证书：native_mapsLifted、native_newBoundFixed、native_oldBoundShifted、native_freePreserved。
整套原11类FormulaRename递归尚未实现，不能由这些项结论替代。

## 实际机器验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0。
两份源锁、版本、全仓wfail构建、Check/CheckStep2/CheckStep3/CheckStep4/Audit共九命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 689 jobs，退出0 |
| 声明审计 | 7234项；280项无公理，6954项允许依赖 |
| 警告 | 0 |
| Internal显式声明覆盖 | 4919项，无漏审 |
| 新增闭句模式 | 35对核心/native精确足迹 |
| 累计闭句模式 | 593对核心/native精确足迹 |
| 源码SHA256独立回读 | 658份，差异0 |
| 九命令/五trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

核心证书精确依赖propext、Classical.choice、Quot.sound；
native证书另含原七个固定ZF定义证书的既有依赖，不含额外原choice证书。
无新增自定义公理；原19规则、九类ZF、原核和固定依赖不变。
哈希、35对足迹、九命令、锁和依赖另作独立回读，
记录在忽略目录verification/internal-index-lift-readback.json。
原OpenAI完整构建/Comparator本批未运行；日志及探针留本地；未推送。

## 下一工程单元

进入完整公式rename的对象递归。计划先将实际有限索引图编码为原内部自然列表码，
再以自然数状态元组记录映射码、四个上下文和目标码，避免假定类大小的历史状态集合。
具体实现与验收表见AGENT_WORKFLOW.zh-CN.md最后的F1a至S表。
该编码和递归尚未证明，不提升完整FormulaRename、替换或ProofZF/U门禁。
最终仍要求原核Derives nativeZF [] (Con_ZF→Con_target)。
