# 清理决定
只清理本轮独立迁移分支；原始提交为 721d331a4ddd3c1d759a719a55f09388ade4fa30。
清理前已生成外部 git bundle 与源码 tar.gz；原来没有用户未提交改动。
保留 Pullback、StageCapture、Choice/Basic、Splice、Splitting 作为条件辅助。
从 Repair/Forcing 精确提取 jrelOf、jrelOf_fun、jrelOf_sec、jrelOf_inj、jrelOf_injDir、jrelOf_total。
其余 Repair、ClassObstruction、Cohen、Random、FuchsPrikry 删除，因为不服务选定的新模型路线。
辅助模块统一由 PPAC.Auxiliary 导入，不再让宿主 PP 与对象 PP 共享主入口。
README、GAPS、THEOREM_COVERAGE、Audit、verify 重写以符合新范围；不删除 Git 历史。
逐文件理由见 CLEANUP.json。未因此证明旧引理有错，也不判断其在其他项目中无用。

## 2026-10-26 重审清理

恢复点：清理前受 Git 管理的文件均可从 `7dbb1c1` 恢复。README、OBJECT_TARGET、STATUS、GAPS 去掉重复或过时的调度，恢复原 1–11 阶段；历史单批验收报告保留。

已按绝对路径白名单删除本项目 `.local` 顶层过期 `.py`、`.log`、审计／预审 `.lean` 及旧复用探针，共 1,276 文件，逻辑大小 5,694,498 字节；当次实测可用空间增加 4,837,376 字节。逐文件 SHA-256 清单位于忽略的 `verification/cleanup-20261026.json`。已先确认 `.local` 没有 Git 跟踪文件，跳过 reparse 项，不递归触及其他项目。

没有残留 Lean/Lake 编译进程需要终止；两个本轮沙箱初始化会话已退出。此后仅启动串行正式验收。

本次没有删除已验收的 Packet/Varint 证明：静态进口图显示直接按名称删除会连带列表拼接、反转等其他模块。它们退出开发主线，但尚未完成独立依赖裁剪，仍纳入历史证明审计；不能宣称这部分已全部删除。冻结候选子目录及原清单暂保留，不重新激活。不因历史辅助数量大就批量丢弃依赖。

本次实际消费者复审另删除 49 个未跟踪文件：40 份正式跟踪文件均未引用的 .local/*-prior-summary.json 副本，以及错排的 ForcingAtomicDecisions 源码和其自身生成缓存。总逻辑大小 222,715,674 字节；未将该数冒充实测磁盘增量。均已解析并核对绝对路径位于本仓，跳过链接／重解析项，清单及 SHA-256 见 verification/cleanup-route-audit-20261026.json。保留正式验收日志、源依赖和既有证明。


## 本轮继续裁剪

已删除 133 份、120882 字节无跟踪文件引用的 `.local/*-staged-files.json`，它们只是历史生成的 git 暂存路径清单；逐文件哈希和字节数见 verification/cleanup-stage-lists-20261026.json。正式源、日志和验收报告保留。

此前冻结目录中的 14 个 packet 候选及重复 SetSatisfactionRow 确认没有活动 Lean import 后退役；连同两份原清单共移除 17 个散文件、100472 字节。删除前生成并逐文件 SHA-256 回验 verification/retired-unused-candidates-20261026.zip（24306 字节），仅作恢复证据，不是待继续代码。已验收 packet 模块的依赖裁剪尚未完成，未据名称删除它们。这里覆盖上文“冻结候选暂保留”的旧裁决。

覆盖表删掉被后来验收推翻的历史“尚未”描述，流程保持原 1–11 阶段。主目标没有改写；完整公式作用对称性通用证书与实际 HS 实例分别记录。

## 本轮生成元数据清理

另确认并删除 369 份已消费／冻结的 `.local` 计划、wrapper-spec、batch 和 checks 元数据，共 4,371,395 字节；没有 Git 跟踪文件引用这些文件名。删除前建立并逐项 SHA-256 回验 `verification/retired-generator-metadata-20261026.zip`；清单在 `verification/cleanup-generator-metadata-20261026.json`。只处理已解析到本仓 `.local` 顶层的普通文件，跳过重解析点，保留正式源、日志和证明。

本轮静态 import 闭包发现 2137 个 Internal 模块中有 1906 个未被非 Internal 正式模块传递导入；这个数字不包含审计根，不能据此将全部模块判为错误或无用。已验收冻结证明尚未完成精确裁剪，未声称已全部删除。没有残留 Lean/Lake 进程需要终止；正式验收继续串行。

正规滤子批次：删除已消费的 verification/ForcingNormalAudit.lean 探针，保留其预审日志和完整验收日志。预审识别出九项额外底座 native 依赖后，已停止提前启动的旧验收及其自身子进程，完成显式记录／重算后重新验收通过；未终止其他项目进程。


## 本批复审清理

再次确认并删除 24 份 `.local` 验收草稿、报告模板、暂存文件清单，共 102222 字节；无 Git 跟踪文件按名称引用它们。删除前在 verification/retired-drafts-20261026.zip 归档并逐项 SHA-256 回验，清单为 verification/cleanup-drafts-20261026.json；逐个核对绝对路径严格位于本仓 .local 顶层、普通文件且内容未变后删除。未把逻辑字节数当作实测磁盘增量。

现行流程和复用合同删去重复批次叙述；OBJECT_TARGET 修正仍以旧 LCarrier 描述供体范围的过时句子，GAPS 去掉“两套核”的歧义。旧正式验收报告保留为历史证据，不再作为待办表。没有发现应终止的残留 Lean/Lake；本批仅串行启动自身编译，未触碰其他仓库脏改动。


Diagram 载体／序作用批次：完整验收后删除自身一次性 verification/ForcingDiagramOrderAudit.lean 探针，保留定向构建、预审计及完整验收日志。未生成额外脚本或历史验收报告；未发现残留 Lean/Lake 进程。

Cohen 条件／序作用批次：完整验收后删除已消费的 verification/ForcingCohenAudit.lean 一次性探针，正式 Audit.lean 已覆盖全部 60 项声明；保留预审、定向及完整验收日志，清单见 verification/cleanup-cohen-probe-20261026.json。回读未发现残留 Lean/Lake 进程；没有删除其他项目文件。

Cohen 作用律／Product 批次：完整验收后删除已消费的 verification/ForcingProductAudit.lean 探针；正式 Audit.lean 覆盖新增 46 项声明，定向、预审与完整日志均保留。清单为 verification/cleanup-product-probe-20261026.json。整体装配的数字索引展开曾触发心跳上限，已改为显式 binder 索引并在默认上限下通过，未保留扩大资源额度的改动。回读没有残留 Lean/Lake；本批没有新增持久生成脚本或另建验收报告。

WithTop 批次：完整验收后删除 verification/ForcingWithTopAudit.lean 一次性探针，正式 Audit.lean 已覆盖全部新增 58 项声明；定向、预审和完整验收日志均保留，清单见 verification/cleanup-withtop-probe-20261026.json。未新增持久生成脚本或单独验收报告；未发现残留 Lean/Lake 进程。


统一作用／Context 批次：绝对路径、无跟踪文件名引用及逐项 SHA-256 回验后，删除 37 份已消费的 .local 模板／schema-spec／exports／旧 WIP 元数据，以及已由 Audit.lean 接替的一次性 ForcingProductFamilyAudit.lean，共 38 文件、270921 字节。前 37 份归档于 verification/retired-consumed-metadata-20261026.zip；清单为 verification/cleanup-family-20261026.json，预审日志保留。清理后才启动本批完整验收。现行 GAPS/THEOREM_COVERAGE 去掉重复历史批次和过时未完成声明；已验收冻结字节模块未在缺少精确依赖裁剪时批量删除。


源参数／具体公式对称性批次：正式 Audit.lean 已接管全部新增和改动声明后，按绝对路径与 SHA-256 白名单删除一次性 verification/ForcingProductSystemAudit.lean，再启动串行全验收。保留预审日志及 cleanup-product-system-probe-20261026.json；没有新增持久生成脚本或重复验收报告。


偏序合同批次：正式 Audit.lean 已覆盖新增 36 项声明后，删除一次性 ForcingProductPosetAudit.lean；另核对无跟踪引用后删除旧 choice-trust-probe.lean。均按本仓解析绝对路径、普通文件、未跟踪状态和 SHA-256 白名单操作，清单为 verification/cleanup-product-poset-probe-20261026.json、cleanup-old-choice-probe-20261026.json。预审及正式日志保留；.local 未发现待清理执行脚本；没有残留 Lean/Lake。本轮纠正 SOURCE_LOCK 中已失效的 Cohen/WithTop/omega/two/作用族未完成描述，未删除具有实际依赖或尚未完成裁剪判断的证明。


HS 配对／并集批次：删除一次性 verification/ForcingProductHSClosureAudit.lean，正式 Audit.lean 已覆盖新增 14 项声明和改动模块原 12 项声明；保留预审、正式验收及静态集成门失败日志。清单为 verification/cleanup-hs-closure-probe-20261026.json。未新增持久生成脚本；旧并集接口保留，依赖集合未变化。验收后未发现残留 Lean/Lake，未触及其他项目。


四条强迫公理批次：删除已由正式 Audit.lean 接替的 verification/ForcingSetAxiomsAudit.lean，保留预审和完整验收日志；路径／SHA-256 清单为 verification/cleanup-forcing-set-axioms-probe-20261026.json。删除空集辅助定理中不需要的条件参数，保持 --wfail；未新增生成脚本或独立验收报告。验收后未发现残留 Lean/Lake。


Foundation／状态复审批次：正式 Audit.lean 接替后按绝对路径及 SHA-256 白名单删除 ForcingFoundationAudit.lean；清单为 verification/cleanup-foundation-probe-20261026.json。另删除 37 份完全无跟踪文件名引用的本仓旧消息草稿／回执及取消记录，共 35102 字节；删除前归档并逐文件核验 verification/retired-message-drafts-20261026.zip，清单为 cleanup-message-drafts-20261026.json。只处理本仓 .local 普通文件，未操作 AgentPlaza 服务数据或其他项目。逻辑字节数不是实测磁盘增量。

现行覆盖表纠正已完成偏序律仍报为待办的条目，流程去掉重复批次叙述；Foundation 从未完成项移至有原核证书项。未新增生成脚本／独立报告，正式验收日志保留。冻结字节证明的精确依赖裁剪仍未完成，不能据此报告已全清理。


Infinity 批次：正式 Audit.lean 接管新增九项声明后，按绝对路径、普通文件及 SHA-256 白名单删除一次性 ForcingInfinityAudit.lean；清单为 verification/cleanup-infinity-probe-20261026.json。预审及正式验收日志保留；无新增持久生成脚本或独立报告。下一消费者按源依赖修正为 collect/separate 后再接 PowerSet.normalize，不为同文件相邻顺序重排数学依赖。


收集名字批次：正式 Audit.lean 接管新增 33 项声明后，按绝对路径、普通文件及 SHA-256 白名单删除 ForcingCollectAudit.lean；清单为 verification/cleanup-collect-probe-20261026.json。预审探针曾因 import 排在声明之后失败，调整为全部 import 在文件开头后重新预审通过；该错误未作为形式化通过证据。预审及完整日志保留；没有新增持久生成脚本或独立报告。


参数稳定子复审批次：按解析后的绝对路径、普通文件和无跟踪引用白名单，删除 8 份旧规划元数据及已由正式 Audit.lean 接管的 ForcingTupleAudit.lean，共 9 文件、14915 字节；旧元数据先归档并逐项 SHA-256 回验，清单见 verification/cleanup-tuple-review-20261026.json。mode2-source-batch.json 因仍有跟踪引用而保留；正式预审和全验收日志保留。移除新模块对 CollectedHS 的不必要导入，改为直接复用 ProductStabilizer/NormalFilter。没有重启冻结字节路线，也没有在未分析消费者前批量删除已验收证明。


Separation 批次：正式 Audit.lean 已覆盖全部 36 项新增声明后，按本仓绝对路径、普通文件和 SHA-256 白名单删除一次性 ForcingSeparationAudit.lean；预审与全验收日志保留，清单为 verification/cleanup-separation-probe-20261026.json。本批没有生成持久脚本或独立验收报告，也没有修改供体或恢复冻结支线。


幂集／复审批次：正式 Audit.lean 接管新增 32 项声明后，按解析后的本仓绝对路径、普通文件及 SHA-256 白名单删除 ForcingPowerAudit.lean，再运行串行全验收；预审日志保留，清单为 verification/cleanup-power-probe-20261026.json。删除 normalized_bounded 未使用的模型参数；流程第 7 阶段去掉重复的逐批叙述，当前缺口／覆盖表移除已完成 PowerSet 的待办。现有三个脚本均有验收用途；.local 剩余 batch 元数据均有跟踪引用，不误删。冻结字节模块仍需按实际依赖裁剪，本批没有声称全部无用代码已清完，也没有恢复该支线。


Replacement 批次：删除未被实际消费者使用的 orbit/localBound 额外 AST 及其展开引理，保留构造所用 movePair/witness AST 和直接服务最终证书的证明。正式 Audit.lean 接管 45 项声明后，按解析本仓绝对路径、普通文件和 SHA-256 白名单删除 ForcingReplacementAudit.lean，再启动串行全验收；清单为 verification/cleanup-replacement-probe-20261026.json。保留预审／全验收日志；修正 MATH_REDUCTION_ROUTE 中实际作用、HS pair/union 和全 ZF 仍被报为待做的旧描述。没有生成持久脚本或独立验收报告，没有修改供体或恢复冻结支线。

Base.M 批次：去掉 ConstructionBaseMonoid 对 ProductParameters 的不必要导入，直接使用原生自然数与积构造；没有新增算术后端或持久脚本。正式 Audit.lean 覆盖全部 23 项声明后，核对本仓绝对路径、普通文件和 SHA-256，删除 verification/ConstructionBaseMonoidAudit.lean；清单为 cleanup-base-monoid-probe-20261026.json，预审日志保留。旧字节支线仍冻结，未作无依据批量删除。

Base 数值数据批次：只适配直接消费的 Dyadic 正分母、唯一性、幂比较及数字构造，不复制零距离／Baire 分支，不导入新版依赖树。正式 Audit.lean 接管 41 项声明后，按解析本仓绝对路径、普通文件和 SHA-256 删除一次性 ConstructionBaseWeightsAudit.lean；清单为 verification/cleanup-base-weights-probe-20261026.json，预审和全验收日志保留。未新增持久脚本，供体未修改，字节支线未重启。

分数比较批次：直接导入已存在的原生 NaturalPrime 交换律，不复制其整除／素数后续内容，也不修改底座。正式 Audit.lean 接管 50 项声明后，按本仓绝对路径、普通文件和 SHA-256 白名单删除 ConstructionFractionOrderAudit.lean；清单为 verification/cleanup-fraction-order-probe-20261026.json。预审／完整日志保留，无新增持久脚本，冻结支线未恢复。

本次阶段复审删除 39 份冻结字节／reader 兼容支线的旧 STEP4 验收叙述；逐文件核对 HEAD 内容和 SHA-256，唯一外部引用为已重写的中文 README。恢复点 c1059d6，清单 verification/cleanup-stage-review-20261026.json。中文 README 原 636 行旧批次叙述替换为当前合同与阶段入口，英文入口同步。未删除原证明或正式验收日志。

实际 import 图中有 431 个名称包含 Packet/Varint/Reader/Bytes 的模块，其中存在 13 个非同名模块直接消费者（例如 FixedAxiomTableSyntax、SequencePrependSyntax）。因此没有按名称批量删除它们；剩余裁剪必须先解开具体依赖，不能把“冻结”误记为“已删除”，也不以已投入成本继续开发。三个现有 scripts 均为验收入口，没有认定为垃圾。本轮未修改其他项目或供体。

切割表示批次：正式 Audit 接管全部 74 项声明后，按本仓绝对路径与 SHA-256 删除唯一临时探针 ConstructionCutRepresentationAudit.lean，清单 verification/cleanup-cut-representation-probe-20261026.json。没有新增脚本、另开实数库或复制供体依赖树；全部集合／函数构造调用既有接口。旧字节支线继续冻结，本轮未作未经依赖核对的证明删除。

加法批次：正式 Audit 接管全部 62 项声明后，核对本仓绝对路径与 SHA-256，删除唯一临时探针 ConstructionAdditionAudit.lean；清单 verification/cleanup-addition-probe-20261026.json，预审日志保留。没有新增脚本、通用代数后端或修改供体。字节支线继续冻结，剩余依赖裁剪未冒称完成。

非负差／原阶段复审：对照最初 f28b0334 的 1–11 阶段和当前源 Base.margin，删除“先补完整实数运算再做 Base.margin”的不必要执行门，改为原两个二进分数估计及统一上确界界。去掉未使用的局部绑定；正式 Audit 覆盖 16 项声明后删除一次性 ConstructionDifferenceAudit.lean，清单 verification/cleanup-difference-probe-20261026.json。无新增持久脚本；未无依据删除仍被引用的冻结证明，剩余裁剪未完成。

原成本界批次：将新模块的导入从 ConstructionFractionDifference 缩为实际使用的 ConstructionCutWeights，移除不必要的分数加法／差依赖。正式 Audit 覆盖全部 25 项声明后，按本仓绝对路径及 SHA-256 删除一次性 ConstructionBaseCostBoundAudit.lean；清单 verification/cleanup-base-cost-bound-probe-20261026.json。保留预审和完整验收日志；无新增持久脚本、供体修改或冻结支线开发。

完整 Base margin 批次：清除未使用局部绑定；正式 Audit 接管 23 项声明后按本仓绝对路径与 SHA-256 删除唯一临时探针 ConstructionBaseHeightGapAudit.lean，清单 verification/cleanup-base-margin-probe-20261026.json。当前覆盖表、缺口表及流程移除 margin 仍待证明的过时陈述，保留模块本身的准确证明范围。无新增持久脚本或无依据证明删除。

Probe Path 批次：修正覆盖表把已完成强迫前端整体标为未迁移的错误描述，压缩第 8 阶段缺口表，删除复用表及 README.md 中 margin 仍待接的过时表述，两个 README 同步。正式 Audit 接管 49 项声明后删除唯一临时 ConstructionProbePathAudit.lean，SHA 清单为 verification/cleanup-probe-path-audit-20261026.json；无新持久脚本。编译前无 Lean/Lake 残留；未无依据删除仍有消费者的冻结证明。

Probe 字母批次：删除未使用的局部前提和化简项；正式 Audit 覆盖 85 项声明后删除唯一临时 ConstructionProbeLettersAudit.lean，路径及 SHA 清单为 verification/cleanup-probe-letters-audit-20261026.json。拆开含糊的“字母和扩张”合并标志，分别记录字母已构造与扩张未完成。更新现行待办，移除已完成 transition／直极限字母仍待做的叙述；未新增持久脚本或修改供体，冻结模块依赖裁剪仍未完成。

Probe 动作／target 批次：去掉未使用的公式参数和局部绑定；正式 Audit 接管 57 项声明后删除唯一临时 ConstructionProbeActionTargetAudit.lean，路径／SHA 清单为 verification/cleanup-probe-action-target-audit-20261026.json。现行文档不再列动作／target 为待做；数学路线中的第 8 阶段长段改为准确的现有接口与下一消费者。无新增持久脚本、供体修改或冻结支线开发。

大小界／复审批次：REUSE_CONTRACTS 去掉重复逐批叙述及过时未完成声明，保留现行接口和边界；恢复点 45512cc。没有复制供体中不被当前消费者使用的 countable-only 特例及 join/lift/end 模块。Audit 接管 42 项声明后删除唯一预审输入，绝对路径及 SHA 清单为 verification/cleanup-probe-word-cardinality-20261026.json；正式日志保留。未新增持久脚本；冻结字节模块的精确依赖裁剪未完成，未宣称全清理。
