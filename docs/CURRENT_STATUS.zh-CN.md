# 当前工作入口（2026-11-09）

当前为原第10阶段；最终对象Con未证明。原1–11阶段见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，来源与可信边界见[FEASIBILITY](FEASIBILITY.zh-CN.md)。

最终目标保持普通nativeZF原核中的`Con_ZF → Con_(ZF+PP+ACwo+¬AC)`，覆盖全部内部／非标准证明码。`InternalConsistency.closing_kernel_certificate`只证明同一`reduction → goal`；reduction及最终goal仍未证明。

原1–9已完成并保留：语言／19规则源推导传输、完整理论及数学模式、任意ZF模型内同一L/ZFC解释、实际具体系统和全部源模型应用。原第4官方Comparator已在固定Lean4.34.1及真实Linux沙箱下接受，78原输入不变；见`verification/original-comparator-acceptance.json`。不重建这些基础。

原第10的代码生产已完成：原ZF/U公理表统一闭类型及实际理论公理证明；全部11原公式构造的实际forcing递归、带类型总性、输出唯一性及任意内部自由范围的开放公式闭包解释；原六类目标证明码构造器。各项均有原nativeZF证书，实际Node／头字段和空free时Root已构造。源码、范围及既有依赖见SOURCE_LOCK和对应验收报告；这些代码生产结论不等于强迫规则保真。

原第10实际AND双向证明组合：InternalProofTemplates直接复用原ObjectTreeTemplate及ObjectLogicalAxiom.prop／shapes，为固定模板取得完整FormulaCode并生成原逻辑证书、完整查询与真实父证明；原表成员是已核实的外部固定模式条件，洞内公式码允许内部非标准。具体消费者为原rule12／13及真实MP，两个投影已直接消费同一ForcingLogicalCode.binary 0输出；结合已验收的正向组合，在空目标bound、任意内部free范围取得Proved(Q)↔(Proved(N)∧Proved(M))。保留原Node／头字段与空free时Root，无新语法／检查器／核。开放闭包传输、完整单调性／稠密性、MP强迫桥、统一公理／Proof正确性、reduction及最终Con仍未证明。九项完整验收和五项trust=0通过，零警告；全部38488项既有足迹及旧证明正文不变，12项兼容回归和三库来源预检通过。验收见verification/internal-proof-templates-acceptance.json。

正向AND组合及原rule11证明生产保留，见verification/internal-proof-conjunction-acceptance.json。

原第10内部蕴含证明组合：InternalProofImplication复用已验收原模板工厂及原K/rule2、S/rule0，不给定公理证明或中间码；从实际A→B、B→C码及其真实证明构造三个实际MP父节点，取得同一A→C码的证明。固定原模式成员由内核验证，全部运行公式／free范围／证明码允许内部非标准；原Node／头字段和空free时Root保持。它是原强迫证明所需的普通字面蕴含证明操作，不是ForcingLogicalCode.binary 2的规范化强迫蕴含桥；该桥、完整统一保真、reduction及最终Con仍未证明。九项完整验收和五项trust=0通过，零警告；全部38497项既有足迹及旧证明正文不变，12项兼容回归和三库来源预检通过。验收见verification/internal-proof-implication-acceptance.json。

后续开放节点按原ForcingSound.sound的名字赋值逐点结构核对解释，保留名字／固定参数索引和原free头计数。既有ForcingOpenCode是“先forallClosure再forcing”的已验收代码生产，不冒称逐点开放解释或六规则保真。变量图、混合替换、类型和唯一性配套已存在，优先核对并消费精确合同，不另建后端。

真正剩余：强迫解释的MP蕴含桥、其他统一六规则保真、内部／非标准ZF/U公理及语义／Proof正确性、同一矛盾码reduction与最终Con，以及原第11最终验收。不得以标准quotation模式或辅助构建代替这些门，不建立全宇宙统一真值／强迫谓词。

发布门：只在前一整轮远端CI成功并读回实际日志后推送；推送后核对远端HEAD、所有改动blob及关键证明／报告实际字节。本地验收不冒充远端通过，不以文档中的历史批次号替代GitHub实际状态。

原第10逐点开放代码适配：ForcingOpenLayout复用原恒等／加法Replacement图、变量像和混合替换列表，在全部内部／非标准范围构造名字前缀i、参数偏移b+i及唯一环境；ForcingPointwiseCode实际消费该环境、既有reify_total、十一构造强迫编译总唯一性及原混合替换，得到free范围t=b+f的逐点开放输出。未插入forallClosure。已取得nativeZF原核中的类型化总唯一证书；重命名／raise／instantiate交换、语义对应、强迫六规则保真、reduction与最终Con仍未证明。完整九项验收及五项trust=0通过，零警告；全部38504项旧足迹与旧证明正文保持，12项兼容回归和三库／75哈希预检通过。源声明名称核对至固定原文forcing_sound；验收见verification/forcing-pointwise-acceptance.json。

原第10实际二元编译计算律：ForcingCodeBinary从真实父／子compiled判断推出四种原ForcingLogicalCode.binary结果；历史在对象EX内生成，直接复用compiled_step、既有分支选择、有界读取和独立子输出唯一性。ForcingCodeStepUnique仅追加公开选择入口，全部旧正文不变。空源bound时，实际合取编译已接到原Node／Root证明构造，取得两种完整ZF/U测试下Proved(Q)↔(Proved(N)∧Proved(M))。所有运行码／范围允许内部非标准。原AbstractTopFormulaOperation、InstantiateTopFormulaOperation与execution_iff早已完成，相关旧False标志纠正；不重新证明这些桥。逐点开放交换、规范化强迫MP桥、统一公理／Proof正确性、reduction及最终Con仍未证明。完整九项验收、五项trust=0通过，38570项声明、零警告；全部38562项旧足迹和旧证明正文保持，12项兼容回归及三库／75哈希预检通过。验收见verification/forcing-code-binary-acceptance.json。

原第10实际逐点开放合取交换：ForcingMixedBinary只消费已有二元替换端点、构造存在和输出唯一性；reified_binary／opened_binary把任意独立输出对齐到同一实际父环境。ForcingPointwiseCode.conjunction实际复合重编码、原四分支编译计算律及逐点打开，取得任意内部／非标准source free范围b、target free范围t=b+f的准确AND输出；未插入forallClosure，无给定局部强迫答案／历史。conjunction_iff进一步接到原Node／Root证明构造，两种完整ZF/U测试下取得实际父可证性↔两个实际子输出可证性。原两个模块旧正文不变，仅增加导入与追加必要消费者。完整重命名／raise／instantiate交换、规范化强迫MP桥、统一内部公理／Proof正确性、reduction及最终Con仍未完成。完整九项验收、五项trust=0通过，38578项声明、零警告；全部38570项旧足迹和旧证明正文保持，12项兼容回归及三库／75哈希预检通过。验收见verification/pointwise-conjunction-acceptance.json。

原第10实际原子／否定／量词计算律：ForcingCodeUnary从真实父及独立子compiled判断推出原ForcingAtomCode、ForcingNegCode、universal和ForcingExistCode片段。历史在对象EX内生成；直接复用既有选择器、有界读取与输出唯一性。否定子式保留bound a，全称／存在子式使用A=a+1，原三层successor合同不变，全部运行码和范围允许内部非标准。四项原选择证明只去掉private修饰，正文完全保持；不是新证明这四个选择器。结合既有四种二元计算律，11类原raw编译构造均有实际输出计算接口。该结果不替代逐点否定／量词／原操作交换、强迫MP和统一规则／公理保真；reduction及最终Con仍未完成。完整九项验收、五项trust=0通过，38594项声明、零警告；全部38578项旧足迹及既有证明正文保持，12项兼容回归和三库／75哈希预检通过。验收见verification/forcing-code-unary-acceptance.json。
