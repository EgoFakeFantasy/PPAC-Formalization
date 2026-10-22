# 实际映射自然码及七字段状态验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 4b59b0ac7d58173d6326d3bb70219216413f50a3。
F1a 与 F1b 的对象表示已验收；完整公式重命名、捕获规避替换和最终内部 Con 主句仍未完成。

## 对象语言与交付层次

背景仍为原 YesMetaZFC 的 nativeZF，即原 Collection 版 ZF 的纯等词/成员语言像。
没有加入对象 AC、不可达或 Con(ZF)。固定依赖为 039c8e132cc19671d73a3933c66b4799d2599dd6。
新增 13 个模块、234 项显式声明及 35 个闭句模式。
每个模式均有实际 Source.Derives、sourceZF 的原核证书，以及经 ZFReplay 返回的
FirstOrder.Derives nativeZF [] (Translation.sentence ...)。
参数全部闭合，前提使用对象 Formula.imp；内部码、图和长度均由对象变量或存在量词指定。
这些是编码基础设施的真实对象证明，尚未给出完整 FormulaRename 关系的递归正确性。

## F1a：完整索引图的实际自然编码

Encoded(w,r,a,c,k) := Encoding(w,r,a,k) ∧ IndexMap(w,r,a,c)。
MapCode(w,a,c,k) := ∃r Encoded(w,r,a,c,k)。
Encoding 保留原 structural_list_code 的完整 Fields 图和原实际长度。
原目标域 c∈ω 及 ω 的传递性把 r 的每个实际输出送入 ω，实际列表编码定理给出自然码 k。

原 ZF 推导以下结论，全部覆盖内部非标准自然数及实际完整非单射映射：

| 输入 | 实际原核结论 |
|---|---|
| Ω(w)、IndexMap(w,r,a,c) | 实际存在唯一自然码 k，满足 Encoded |
| Encoded(w,r,a,c,k) | k∈w 且原列表码有效 |
| MapCode(w,a,c,k) | 实际存在唯一完整图 r 满足 Encoded，且 a,c∈w |
| 同一 k 的 Encoded(w,r,a,c,k) 与 Encoded(w,s,b,d,k)、Ω(w) | b=a 且 s=r |

目标作用域 c 是额外范围参数，不编码在 k 中。同一实际图可适用于不同合法目标域；
没有声称能从 k 恢复唯一 c，亦没有推出 c=d。
主要证书：native_codeFiber、native_graphFiber、native_mapFiberIff、native_sourceGraphRecovery。

量词提升的 CodedLift 实际绑定原图 r、正确提升图 g 及 g 的原自然列表码 l。
给定输入 MapCode 和真实 Succ(u,a)、Succ(v,c)，原核实际构造唯一 l，
证明输出是 MapCode(w,u,v,l)，并能恢复与给定 r 对应的实际提升图。
原 Lifted 的全内部零/后继边规律保持；free 映射由后续状态继续保存。
本批编码提升的存在接口仍以给定真实后继为前提，不声称另外交付了无后继前提的联合编码提升系统。
主要证书：native_liftAtSource、native_liftExists、native_liftOutputCode、native_liftCodeFiber。

## F1b：七个内部自然字段的实际状态码

字段次序固定为：
(boundMapCode, freeMapCode, sourceBound, sourceFree, targetBound, targetFree, targetFormulaCode)。
源公式码是未来 recursor 的索引，不混入七字段状态。
Cell 是原 Forest(7)，Legal 是两个 MapCode 与目标 FormulaCode 的合取，State := Cell ∧ Legal。

从 Legal 实际得到七个字段都属于 ω，原 Forest 存在定理给出实际自然状态码。
对象核证明同字段状态码唯一、同状态码每个字段相等，并将七字段唯一性写成七个内部全称量词。
Recognized 实际存在量化七个字段；DecodedFiber 保留这些实际字段并量化全部候选字段。
在 Ω(w) 下，Recognized ↔ DecodedFiber，且所有被识别状态码属于 w。
只给两个完整 IndexMap 和目标 FormulaCode，也实际联合构造两个映射自然码及自然状态码。
主要证书：native_stateFiber、native_uniqueParams、native_actualDecode、native_stateDecodeIff、native_actualStateSystem。

State 的 Legal 只是类型和作用域元数据，不断言源码与目标码存在正确重命名关系。
没有把 Lean 七元组、宿主数据选择或标准自然数递归当作内部状态见证。

## 实际机器验收

C:/Python314/python.exe -X utf8 scripts/verify.py 退出 0。
两份源锁检查、版本检查、完整 wfail 构建和五个 trust=0 入口共九条命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 702 jobs，退出 0 |
| 声明审计 | 7468 项；282 项无公理依赖，7186 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 13 模块、234 项，全覆盖 |
| Internal 累计显式声明 | 5153 项，无漏审 |
| 新增闭句模式 | 35 对核心/native 精确依赖足迹 |
| 累计闭句模式 | 628 对核心/native 精确依赖足迹 |
| 源码 SHA256 独立回读 | 671 份，差异 0 |
| 九命令/五 trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 固定提交不变，依赖工作区干净 |

核心证书精确使用 propext、Classical.choice、Quot.sound；
native 证书另含原七个固定 ZF 定义证书的既有依赖，不含原 choice 的额外证书。
原 choice 额外证书继续仅限既有桥接范围；没有新增自定义公理。
原 19 条源规则、九类 ZF、公理模式和原 Hilbert 核保持不变。
独立复核记录在忽略目录 verification/map-code-state-readback.json。
原 OpenAI 完整构建与 Comparator 本批未运行；探针及日志留本地；未推送。

## 下一工程单元

F1c 定义实际状态历史查询和原 11 类重命名矩阵，由原 Separation 构造实际唯一状态子集，
关闭算子总性、单值性及状态载体范围；之后接全内部 recursor 和成员归纳。
量词必须实际提升并重新编码 bound 图，free 图不变，原零符号保持。
完整 FormulaRename、捕获规避替换、ProofZF/U、内部编译器和解释仍待证明。
最终目标仍为原核 FirstOrder.Derives nativeZF [] (Formula.imp Con_ZF Con_target)，
内部 Con 必须量化全部内部 ω 证明码。
