# 当前状态：原 1–11 阶段

本批输入基点 `b2fa4cb`。继续固定 OpenAI ProbeWords 的实际依赖：右乘过渡图、有向系统、共同阶段关系及实际直极限字母商。**连续完整验收到原 1–3；当前开发仍在阶段 8，尚未进入收尾；最终对象 Con 未证明。**

| 原阶段 | 已有成果与真实剩余 |
|---|---|
| 1–3 | 语言桥、重命名／替换、19 规则推导传输、完整 ZF 模式互导和两种 AC 对应已验收，不重做 |
| 4 | 历史原 Main 的 8998 项构建和五端点审计已通过；完整 Comparator 未运行，缺 Linux/landrun。本轮重核 75 份主链源码哈希，全部匹配；没有重跑原环境 |
| 5 | 内部集合／图／ω／递归、名字、统一作用和 HS 基础已有；最终具体系统的消费归 8–10 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及全模式已完成，此前已回读 Model/Choice 正文，本轮未重跑供体。剩版本、语言相对化和原核接入，不重证 L 数学 |
| 7 | forces_ZF 的固定公理和完整模式已有原核证书，保留源单子／Presentation／正规滤子前提；具体系统由 8 提供，整阶段不能打勾 |
| 8 | 初始 Base、完整 margin、Path 因子／终端图已有。本批完成 transition 实际函数图、有向系统定律、共同阶段等价关系、实际直极限字母商／投影及 letter_eq_iff 的原核证书。仍缺商上的动作／target、字母表与字正规形、实际 Probe/Merger 扩张、保守嵌入及 margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | 原 SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 装配、ZF/U 专用内部 Proof/Con、全部内部矛盾证明码归约和最终闭句未完成；底座通用 Proof/Sat 已有，不重造 |
| 11 | 最终主定理验收未开始 |

对象合同：纯成员／等词语言、完整 nativeZF、原 FirstOrder.Derives；最终 `Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC，覆盖全部内部及外部非标准证明码。固定源仍为 OpenAI 1581d4cb，不改为独立目标证明。

## 本批实际迁移与复用

ConstructionProbeTransitions 对应原 Path.transition、DirectedSystem 和 letter_eq_iff 的共同阶段关系。沿源右乘因子定义构造实际内部函数图；结合律与已有 factor_trans 给出恒等／复合。两个共同阶段通过内部 ω 的比较提升到共同上界，得到等价关系传递性；左作用兼容和消去只用原左消去律，不假定过渡映射单射或右消去。

ConstructionProbeLetters 用原生 ω×D 作为代表元集合，按共同阶段关系通过 Separation 构造每个实际类集合，调用 Replacement.exists_functionalImage 构造恰好由这些类组成的商载体，再用 FunctionConstruction.exists_setFunctionFromTo_of_denote 构造投影图。letter_eq_iff 精确证明字母相等当且仅当原共同阶段关系成立；letter_transition 与 projection_onto 分别给出过渡不改字母和每个字母有代表元。

两个 construction_kernel_certificate 均返回原 FirstOrder.Derives nativeZF [] 中的纯对象存在句子。字母商证书直接从原左消去单子和有界递增 Path 出发，内部构造因子图并证明所需等价关系定律；没有把这些定律、商载体或投影作为额外假设。覆盖模型全部内部 ω，不假定外部标准性或良基性。

实际复用原生积、分离、精确函数像、函数图、Kuratowski 编码唯一性和已接入的 BMS 式 ModelTransfer。未重建通用商库、函数图后端或推导核，未修改供体。下一消费者是原 Path.act/act_injective/target，随后 alphabet 和字正规形；代表元上的兼容性不冒称商上动作函数已经构造。

## 误判纠正与清理

此前错误在于把局部验收当成全局接近完成、把版本／语言接口未接通说成已有数学未完成，并让可选字节兼容路线扩张。对象层要求早已存在，不能归因于用户后来改变目标；详见 SCOPE_REASSESSMENT。

本轮移除现行待办中 transition／直极限字母仍待做的过时叙述；将含糊的“字母和扩张”合并标志拆开。删除未使用的局部前提及化简项，正式 Audit 接管 85 项声明后删除唯一临时 ConstructionProbeLettersAudit.lean；路径／SHA 清单为 verification/cleanup-probe-letters-audit-20261026.json。没有新增持久脚本。冻结字节模块仍有实际引用，依赖裁剪未完成，不声称全部无用成果已清除。

## 实际验收

定向构建、trust=0 预审及完整 scripts/verify.py 均通过。严格构建 2950 项任务；9 条命令全部退出 0，其中 5 次 --trust=0；30760 项声明审计，765 项无公理依赖、29995 项使用已记录依赖；构建 0 警告；2516 个当前文件指纹全部匹配。新增 85 项声明和两项原核存在证书，无新增可信依赖；底座原有 native Bool 证书仍明确记录。这些数字不表示完成比例。

证据：verification/commands.json、summary.json、build.log、audit.log、construction-probe-letters-preaudit.log、construction-probe-letters-full-verification.log。过渡图、实际直极限商／投影及共同阶段相等标志为 true；商上动作／target、扩张单子及 relative_consistency_proved 为 false。验收结束无 Lean/Lake 残留；仅本地提交，不上传或发布。
