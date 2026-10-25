# 优先复用的已完成接口（2026-10-25 用户纠正后）

纠正：此前仓库评估停在粗略目录／README层，没有继续消费已经完成的具体接口，导致重复开发。当前 YesMetaZFC 固定提交 039c8e132cc19671d73a3933c66b4799d2599dd6 已核对等于 EgoFakeFantasy/YesMetaZFC 远端 main；本轮不更新依赖、不改其他项目的脏工作区。

下表的“复用”包括定义、已证算法、原核证明和终局装配方式；不能因配套证明位于模型命名空间就把整组资产丢弃，也不能把它的背景或量词悄悄改成最终目标。

| 现成资产 | 精确入口 | 本工程的处理 |
|---|---|---|
| 集合结构满足关系、公式阶段、赋值压栈及对象定义规格 | FormalSystem/TarskiTruth.lean 的 formula_satisfaction_condition、assignment_update_condition、formula_satisfaction_semantics_theory | 撤掉本轮重复的 SetSatisfactionRow；先消费既有定义及配套，仅核对到纯ZF的支撑消去 |
| 完整公式识别与实际解码 | Automation/ObjectFormulaSound.lean:239，ObjectFormulaSyntax.checked_decode | 不重做识别／解码链；核对纯签名嵌入与目标理论参数 |
| 四种语法变换、27类逻辑公理 | ObjectSyntaxTransformSpec.checked_iff；ObjectLogicalAxiomSpec.checked_decode_iff | 直接消费现成规则图，不再逐标签复刻程序 |
| 六规则节点、整树证明图与 quotation | ObjectProofNode.ofNodeTest；ReducedProofPresentation.presentation | 使用通用构造，只提供本任务公理测试及所需背景证书；不要求无效外壳逐值等于另一算法 |
| 支撑语言消去、裸理论对象可证明性与一致性公式 | PureSentenceTransfer.derives_iff_m；PureProvability.provable_m／consistency_m | 复用装配和消去方法；具体ZFC实例不得冒名为ZF／U的证明谓词 |
| 全部内部码上的图／规范扩张对应 | PureSourceLocalTests.codeProof_agreement、provableCode_agreement | 复用同一族局部测试和模型回传；不把逐标准 numeral 的正确性误当作这项完整对应 |
| 纯成员语言的固定公平调度与强完备性 | PureRosserSchedule.target；Completeness.strong_completeness | 直接使用，不重写调度。可对任意纯理论T从所有Type 0模型中的同一句子返回原 Derives T [] φ；不要求T为ZFC |
| 其他项目的原核收尾 | BMS SecondOrderCompleteness.derives_m、PowerlessBMSNonemptyTransfer.derives_m、SecondOrderHereditaryBMSWellOrder.derives_m | 复用“逐模型消去全部实际候选前提，再经原完备性回传”的闭合方式。背景／签名／universe须对应，不复制BMS结论或额外公理 |
| 已有 L／Def／Gödel运算与逐公式编译 | 本地 lean-constructible-universe-stage4 的 FormulaGodel、RudimentaryConstructible、CodedSatisfaction、LStageZF、BasicAxioms、Choice | 使用已完成的构造和证明路线，不再到外部项目重建L。只补其实际语言与原ZF推导接口之间的桥 |
| 已有集合Sat支持条件与有限纯公式 | IBLP 的 SetSatisfaction、SetSatisfactionFormula；BMS 的 PowerlessSourceCompilation | 复用已编码的赋值、支持与公式迁移，不再新造同类语法／递归后端 |

YesMetaZFC 文件相对于 `.lake/packages/YesMetaZFC/YesMetaZFC/`。BMS 本地已核对源码位于 `../bms-publish-20260928/ConstructibleBridge/BMSConstructibleBridge/`；现行最终 derives_m 另已从所连接 GitHub 仓库核对。构造L的本地项目位于工作区根的 `lean-constructible-universe-stage4/`；有scope差异的终局模块不能直接改名当作本项目主定理。

本轮撤回的重复候选在 `.local/superseded-set-satisfaction-20261025/`，源文件与恢复副本 SHA-256 一致，未接入PPAC／正式审计／验收状态。已完成一次定向编译不使它成为需要保留的新主线。

现有语法／证明图资产已经完成；接下来的工作必须是选定这些接口后的ZF／U公理测试、背景消去、语言对应或实际数学证明传输。新增基础模块前必须先给出具体接口不适用的类型／前提证据，不能再以“对象层需要”为理由从头重建。

实际接入代码为 `PPAC/Migration/ModelTransfer.lean`，共6个声明：从已验收源公理推导取得外延性，直接消费通用 `FirstOrderSemantics.models_iff` 得到精确nativeZF／Project ZF的模型等价；对任意模型universe证明U的模型条件恰为Project ZF加原PP、ACwo、¬AC矩阵；直接复用既有纯语言调度和强完备性，把所有相应Type 0模型中的Project定理回传为原核 `Derives nativeZF [] (fo_sentence φ)`。这正是BMS的收尾方式，不新增满足关系、调度、证明核或模型构造。

这项接线不把具体ZFC规范扩张自动改成ZF扩张，也不把单个标准模型里的L构造改称所有模型中的定理。现有L／逐公式编译和ZF／U内部证明图的实际适配继续使用上述已有资产；未满足的全模型数学前提和内部任意码传输仍明确保留。

实际验收：定向构建ModelTransfer（155 jobs）通过；正式 `python scripts/verify.py` 完整通过，2656构建任务、28549审计声明（新增6项全部覆盖）、9条命令全成功（5条trust=0）、零警告。新增通用收尾只依赖三项标准宿主逻辑公理，其余五项精确保留既有七个ZF语法证书基线；没有激活额外choice语法证书或新增对象AC。日志与源码哈希在忽略的verification目录，不将日志加入源码。

早先三个既有接口目标的196 jobs构建及本地trust=0调用探针也已通过；它们是复用可调用性证据。误扩至整套PureProvability的构建已主动中止，不列为重新编译通过。重复满足关系候选及冻结packet候选不恢复；本批临时探针已删除，正式源文件和审计保留。

最终目标仍为原nativeZF中的内部Con_ZF → Con_U。最终Con、相对一致性、专用ZF／U内部检查器、任意内部码正确性及完整内部模式测试五项完成标志均保持false。接口接线验收不是主定理完成验收。
