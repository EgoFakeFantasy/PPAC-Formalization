# 原free替换项列表与实际索引码的对象转换验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 06a22b358f58a229e218e95dbdc815ffd380b82f。
S1已验收：原替换项码列表和实际完整索引图/MapCode的双向存在唯一、准确输入和字段对应。
全公式free替换、原free_substitution检查器兼容、跨bound/free替换及最终内部Con仍未完成。

## 固定对象合同

对象语言仍为原纯等词/成员语言；背景是原nativeZF的完整Collection呈现。
源完整Replacement借既有对象公理互导和原核replay接入，没有新增对象公理。
本批source证明均返回Source.Derives；闭句通过TheoryTransport.sentence和ZFReplay.replay得到原FirstOrder.Derives nativeZF []。
最终目标仍是Con(ZF)→Con(ZF+PP+ACwo+¬AC)的对象蕴含。
内部Con规格必须量化全部内部ω证明码，保留原六规则、27逻辑模式、完整Separation/Collection。
专用ProofZF/U完整纯AST和最终Con原核推导尚未交付。

## 原参数格式与纯OpenTerm

原纯SetTheory.signature没有函数符号；本工程内部Term仅允许实际bound/free变量码。
在实际Empty(z)、Ω(w)、c∈w下，原对象核证明：

```
Term(w,z,c,t) ↔ ∃j (j∈c ∧ FvarCode(w,j,t)).
```

这里z和j都是对象；未调用宿主项解码、标准Nat索引或外部项构造归纳。
原ProofTreeCode的rule-5替换参数是termCode的原列表；本批保留它，不把该参数直接替换为裸索引列表。
上游扩展Nonlogical.BasicSetTheory含真实函数符号，不能套用上述纯语言归约。
NatDecode/NatPacket与带头部ProofTreeCode的包装不同，本批没有宣称二者数值编码相等。

## 实际图与双向码转换

TermGraph(w,f,a,c)同时保留自然作用域a/c、完整functionOn(f,a)、ω值域，以及每条实际边值的fvar分支合法性。
TermList(w,a,c,L)在对象存在量词中绑定实际字段图f，要求原Encoding(w,f,a,L)和TermGraph。
解码值关系为∃t(Edge(f,i,t)∧FvarCode(w,j,t))；编码值关系为∃j(Edge(r,i,j)∧FvarCode(w,j,t))。
两个关系在全部内部域点上都实际存在唯一；原Replacement据此构造完整函数图，无多余成员。
实际编码图和解码图互为精确转换，任意内部候选边均有双条件；实际图各自唯一。

CodeConversion(w,a,c,L,S)内部绑定f/r，要求原项列表编码、准确图转换、原索引图范围及原Encoded MapCode S。
在Ω(w)下实际证明：

```
(∃S CodeConversion(w,a,c,L,S)) ↔ TermList(w,a,c,L).
(∃L CodeConversion(w,a,c,L,S)) ↔ MapCode(w,a,c,S).
```

每个方向都实际构造唯一输出码；实际唯一纤维也分别与这两个精确输入互为双条件。
同一列表的不同字段图、同一索引码的不同解码图，先在四个对象见证下用原图唯一性对齐，
再用原等词替换与编码单射性证明输出码相等。
没有从存在证明抽取Lean数据，也没有假定实际索引图单射。
a/c和长度均为内部对象；定理不排除空域、重复目标索引或内部非标准长度。
源长度a与独立目标范围c始终显式保留；不从索引列表码本身推断c。

## 原列表真实字段的准确对应

任意实际Encoded(w,r,a,c,S)均可恢复与L相连的实际字段图；不是只对某个宿主选定图成立。
在Ω、CodeConversion、上述Encoded和任意FvarCode(w,j,t)下，对全部内部候选i/j证明：

```
Edge(r,i,j) ↔ (i∈a ∧ Field(w,L,i,t)).
```

源域守卫显式保留；没有把域外的列表投影值当作有效替换字段。
TermList中的任意实际域内字段都证明属于合法fvar分支。
这为后续按原term-code列表核验rule-5提供准确对象接口，但没有据此开启完整规则兼容门禁。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py`退出0。
原规则/理论锁检查、版本、全仓严格构建及五trust=0入口共九命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 全仓严格构建 | 840 jobs，退出0 |
| 全部声明审计 | 9730项；294无公理依赖、9436允许依赖 |
| 警告 | 0 |
| 本批新增 | 12模块、230项显式声明、33个闭句模式 |
| Internal显式声明覆盖 | 7415项，无遗漏 |
| 核心/native精确足迹 | 新增33对；累计981对 |
| SHA256独立回读 | 809份，差异0 |
| 九命令、五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| 原YesMetaZFC依赖 | 039c8e132cc19671d73a3933c66b4799d2599dd6，工作区干净 |

新增核心证书恰依赖propext、Classical.choice、Quot.sound；native证书另恰含既定七项原证书。
这是固定Lean可信基足迹，没有向对象背景加入AC、标准ω、外部良基、模型或一致性假设。
原choice额外证书仍单独限域；原库未修改；未恢复退役反射实现。
独立回读在忽略目录verification/free-subst-readback.json；生成辅助、规格和详细日志仅留本地。
原OpenAI完整构建与Comparator未运行；未推送。

## 接续工程表

| 单元 | 实现职责及输入 | 对象交付与实际验收门 | 状态 |
|---|---|---|---|
| F2.4b.1–b.2 | 原恒等/位移码和全部内部公式 | Weak实际唯一输出、全11端点律、真实binder提升 | 已完成 |
| F2.4b.3 | 原weakenFree与数值语法编码 | 准确编码对应；随后连接全部内部证明码的加强规则检查 | 待完成 |
| S1 | 纯OpenTerm、原项码列表、实际完整字段图/索引图 | 双向实际唯一码、精确输入双条件、任意实际解码和全候选字段对应 | 本批完成 |
| S2 | S1的原项列表L与MapCode S、bound恒等码及RenameFormula | 原项列表参数化的全公式free替换，存在唯一、类型、11构造律和量词下相容 | 待完成 |
| S3 | 混合bound/free项像和真实binder提升 | InstantiateTop/AbstractFreeTop及捕获规避替换的全内部正确性；两类项像的bound部分均需提升 | 待完成 |
| 5a | 原六规则/27模式及完整ZF/目标公理码 | 专用ProofZF/U纯AST、准确原参数字段、所有内部证明码的规则核验 | 待完成 |
| 5b | 原源/目标转换器与内部检查关系 | 全内部编译器和检查正确性，包含完整Separation/Collection | 待完成 |
| 6 | 内部解释、固定Con_ZF和Con_target | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

本批四个细分门禁为True；原free_strengthening兼容、完整FormulaRename总门禁、完整捕获规避替换、
专用ProofZF/U、任意内部证明码正确性、最终Con及相对一致性门禁保持False。
S2仍须把实际原项列表接到全公式操作，不能仅把CodeConversion改名为完整替换证明。
S3须处理原模式20/23/25的InstantiateTop、21/22/24的AbstractFreeTop，以及规则3的forallFreeTop。
原始参数格式和纯/扩展签名范围须再次核对；主agent继续独占串行Lean/Lake并做逐声明验收。
