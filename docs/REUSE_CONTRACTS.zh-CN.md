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

数学收尾批正式验收：2657构建任务、28562声明审计（新增13项完整覆盖）、9条命令全成功、5条trust=0、零警告。公式构造精确依赖propext／Quot.sound；五项模型／原核证书精确保留标准三项及既有七个ZF句子证书，未激活额外choice证书。本批早先审计曾因错误地要求公式构造无任何宿主逻辑依赖而失败，已按实际两项标准依赖设置精确检查并完整重验通过。

数学收尾已实际复用到 `DefinableMinimaChoice.lean`：原L工程的Choice／InternalWellOrder用分离选取集合族各成员的最小元。本适配以三元纯公式lt(r,x,y)表达带内部参数的关系，证明对象句子

```text
Min_lt := ∀a ∃r ∀x∈a (x非空 → ∃唯一y (y∈x ∧ ∀z∈x ¬lt(r,z,y)))
Derives nativeZF [] (Min_lt → AC)
```

r在对象量词内为每个族分别存在，无需在元层选一个关系函数或统一的全宇宙最小元关系。已用实际Kuratowski关系图edge(r,x,y)实例化；量词回归覆盖lt内部另有存在量词时的变量保护。现成反向编译及相对化还给出原核中的 `∃D → (Min_lt)^D → AC^D`，背景明确为相对化的源ZF理论。此证书关闭了L选择公理的分离收尾；实际L域、全部相对化ZF公理及内部层序关系的最小元前提尚待接通。

复用来源为本地已核对提交7f5a7d03d63d9769172f17350bbe8303996e5b53的Choice.lean、InternalWellOrder.lean和Def.lean；原文件SHA-256及适配路径记入SOURCE_LOCK.json的companion_reuse，版权和Apache许可证完整保留。未修改L工程或YesMetaZFC依赖。

内部良序批正式验收：2830构建任务、28580声明审计（新增18项完整覆盖）、9条命令全成功、5条trust=0、零警告。两份适配的逐声明足迹已精确锁定：构造为原标准两项，纯语义辅助为标准三项，其余模型／原核证书仍为标准三项加原七个ZF句子证书，没有激活额外choice证书。首次消费的两个既有库目标也已成功构建（219 jobs）；源码依赖未改。

内部良序覆盖已实际接入：`KuratowskiZF`复用固定YesMetaZFC的同一Kuratowski convention／Code／坐标单射和KP配对构造，提供任意nativeZF模型中的完整Interpretation记录；只适配原入口要求ZFC的背景，不重写有序对或整个规范扩张。`InternalWellOrderChoice`直接使用原Project.isSetCodedWellOrder及其语义定理，并通过既有ProjectDecode取得Source闭句：

```text
CoverWO := ∀a ∃b ∃r (a⊆b ∧ r在b上是内部集合编码良序)
Derives nativeZF [] (CoverWO → Min_edge)
Derives nativeZF [] (CoverWO → AC)
```

这里的良序最小元条件只量化模型内部子集。由原线序的自反空缺／传递性把“≤所有元素”转成“无更小元素”，并证明唯一性；在族的并集上应用CoverWO后，得到上批所需同一个内部关系参数。Source反向编译及任意域相对化证书也已取得，仍保留域非空与相对化ZF背景。此处没有证明实际L层序满足CoverWO，也没有假定宿主WellFounded或外部标准ω。

原L工程StageInternalOrder／InternalWellOrder的覆盖与最小元路线记录在SOURCE_LOCK.json；未修改该工程或固定依赖。该适配是L实际层序构造的消费端，接下来应传输已有构造以证明L域中的CoverWO，而不是继续新增可选编码设施。

实际Def后继构造已接入：`ExistingConstructibleSyntax`保留固定L工程godelDefOutputFormula所需的99个既有纯语法声明（11个源文件）；原声明正文逐项SHA-256锁定，数据的构造器和原变量槽位保留，仅移除Mathlib／模型导入和证明，有限向量在本模块作用域内展开为Fin.cases。这个语法切片解决原工程Lean 4.33.0-rc1＋Mathlib与当前4.33.1＋Std的实际导入差异，不引入新的识别器、满足关系递归或推导核。

`GodelDefOutput`以五构造器翻译接入已有Source语言，证明重命名保真、原派生逻辑外壳及固定输出公式的实际语义对应。对原布局 `[U,varTag,appTag,empty,op0,...,op8,omega,nextU]`，原ZF核取得：

```text
∀十四个输入参数 ∃nextU godelDefOutputFormula
∀十四个输入参数 ∀nextU nextU' (Output(nextU) ∧ Output(nextU') → nextU=nextU')
```

这两条是无额外算子前提的闭句Derives证书：幂集给候选范围，完整分离按固定原求值公式构造精确输出族，外延性关闭唯一性。程序码、结果、输入参数均为模型内部集合；未假定外部良基或标准ω，也未把原求值公式换成不透明的宿主oracle。源19规则的反向编译证书已提供，供后续原内部递归直接消费。

固定Def批实际验收：scripts/verify.py全流程通过；2832构建任务，28702个声明审计（535项无公理依赖、28167项依赖已核对），9条命令全部成功，其中5条trust=0，零警告。新增122项声明全部覆盖，2421份源码哈希与验收记录一致。该数量只记录验收覆盖，不表示最终主定理的完成比例。

本批没有证明该求值谓词在任意内部程序码上的完整运行正确性，也没有证明实际L的全部公理／层序图／CoverWO。下一项数学工作是用已有内部递归和这一确切后继公式传输原层历史；不能把此Def-step验收当成完整L解释或最终Con完成。

最终目标仍为原nativeZF中的内部Con_ZF → Con_U。最终Con、相对一致性、专用ZF／U内部检查器、任意内部码正确性及完整内部模式测试五项完成标志均保持false。接口接线验收不是主定理完成验收。
