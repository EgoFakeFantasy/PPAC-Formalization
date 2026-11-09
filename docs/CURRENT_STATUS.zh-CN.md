# 当前工作入口（2026-11-09）

当前处于原1–11规划的第10阶段；第11阶段未开始，最终对象Con尚未证明。原阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。本页只列当前结论；历史批次以Git和不可改写的逐批验收报告为据。

最终目标仍为原YesMetaZFC纯集合语言／普通nativeZF中的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码及完整公理测试和原六规则Root。`closing_kernel_certificate`只证明`reduction → goal`，不能代替尚未证明的reduction或goal。

## 已完成并必须复用

| 已有资产 | 当前精确边界 |
|---|---|
| 原1–3语言／19规则／全理论对应 | 已有原核证书；不是待重做的基础。全部内部Proof/Con仍属第10 |
| 原第4外部基线 | 原4.34.1 Main／五端点与官方Comparator均已接受，运行42492087042；与目标4.33.1保持隔离 |
| 原第6内部L/ZFC及完整模式 | 任意ZF模型内部L、原生／源全部模式、Choice、全局序及解释背景／非空消费均已完成；不重新建立L或真值后端 |
| 原第5、7–9数学前端和实际系统 | 沿固定OpenAI源及既有供体完成；当前消费者见SOURCE_LOCK和REUSE_CONTRACTS，不从旧批次叙述重新开工 |
| 原内部语法／证明配套 | AbstractTop／InstantiateTop／execution_iff、原27逻辑模式和六证明构造器已有。完整ZF/U公理码生产、全11构造实际raw强迫编译、类型化总唯一性、开放闭包代码已有 |
| 实际逐点opening与原证明操作 | 名字前缀和参数偏移的实际环境总唯一；无forallClosure。准确AND组合、原K/S、原rule20共同背景实例、同一falsum到原闭Root均已接入 |
| 完整否定外层实例 | 从真实完整NegCode及opening生成同一量词体／环境／lift和G→实例证明；完整守卫／重绑定交换及规范化强迫MP仍未证明 |
| opening／lift／mode2的变量部分 | 旧名字／参数项经真实lift和原kind1 mode2运行保持精确码；新头变为指定合法参数。均有普通nativeZF原核证书 |
| 实际条件参数识别 | 从同一opening真实参数表内部生成选中字段P和偏移J=a+j，证明新头／原mode2组合结果恰为J处原自由变量码。P、偏移、头码和执行均非给定答案；覆盖内部非标准索引及码 |
| 实际原重绑定的项方程 | 从完整compiler取得同一六见证和公式Subst；实际coded项替换精确对应原bound后继／free条件分支。只公开两项已有数据接口，原正文保持；完整三段公式相消仍未证明 |
| 实际三段根项组合 | 对任意内部纯项，真实重绑定／lifted opening／原mode2输出等于直接opening输出；实际操作判断和选中参数字段是前提，变量角色／索引／后继内部取得 |
| 任意目标深度的单步binder项交换 | 原mixed substitution与真实binder lift交换，输出为旧输出的原移位rename；复用实际shift／identity图，头码／变量见证内部取得。整组三段组合的binder闭包尚未证明 |

## 当前真正缺口及依赖顺序

- 根部项组合和单步项交换已完成；下一消费者是三段操作与直接opening四张真实码表的整组binder闭包，使用`ForcingMixedTermLift.natural`及已有`InstantiateFrameTerm.coded_iff`衔接原mode2，再做内部公式归纳以完成**全内部公式相消**。现有纯索引重命名复合及编码解码往返定理已有，但尚未建立它们对跨bound/free混合替换的直接适用性；不把已有接口本身误报缺失。
- 消费真实守卫、regularity／单调性，完成**规范化强迫MP**及其余统一内部六规则保真。普通字面蕴含组合和外层量词实例不能替代此门。
- 接通全部内部／非标准ZF/U公理实例及完整Proof正确性，证明同一矛盾码的`InternalConsistency.reduction`，再取得最终`goal`。外部固定正文的quotation模式不替代此门。
- 最终对象主句及量词／依赖／固定源对应全部满足后，才进入原第11阶段终验。

## 最新实际验收

`verification/forcing-rebind-opening-triangle-acceptance.json`：九项命令和五项trust=0均退出0；38721项声明，零警告；38713项旧依赖足迹和全部2822份旧证明源码哈希不变，全部既有SOURCE_LOCK条目保持。12项跨平台回归、三个干净锁定依赖及75项源哈希检查通过。已取得根部全内部纯项的真实三段组合和任意目标bound深度下的单步binder项交换，不证明整组组合binder闭包、完整公式相消、强迫MP、reduction或最终Con。

每批发布前等待上一轮远端CI终态成功并读取实际native PASS日志；本地通过不冒充Linux干净环境通过。只清理已核对路径／大小／SHA256的自建临时材料，不清理其他项目或重启仍活跃的任务。
