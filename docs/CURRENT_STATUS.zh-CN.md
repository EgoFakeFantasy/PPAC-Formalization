# 当前工作入口（2026-11-08）

当前为原第10阶段；最终对象Con未证明。完整状态见[STATUS](STATUS.zh-CN.md)，原1–11阶段及agent入口见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)。

已完成的原完整标准模式quotation链、实际ZF/U公理表的统一闭类型、L及完整数学模式全部保留，不重做。实际公理类型已由原六规则theoryShape有界查询消费，覆盖内部任意正文／次数；它不等于统一强迫可靠性。

本批InternalConsistency已把实际完整公理测试与原六规则根关系组装为同一内部Con_ZF、Con_U和目标句goal；其reduction准确量化同一内部ω中的全部U矛盾证明码和ZF矛盾证明码。普通nativeZF原核中的closing_kernel_certificate证明reduction → goal，已通过完整验收。它没有证明reduction，也没有证明goal；不把条件性封闭门当成最终成果。

本批InternalAxiomProof已从实际完整ZF/U公理查询构造同一理论中的内部证明码，实际取得原node/root轨迹，并消去外给类型、自然数字段、局部检查和轨迹前提。此为内部证明传输的公理生产基例，不是U公理到ZF强迫解释证明的归约。

下一步主线只证明此精确内部reduction，沿同一原强迫解释和已完成的L解释，复用ObjectProofNode、ReducedProofPresentation、PureProvability/PureSourceLocalTests。不得改成全宇宙统一真值／强迫谓词，也不得限制外部标准码。原第4 Comparator及第11终验仍待完成。

最新报告：`verification/forcing-atom-dispatch-acceptance.json`；此前原子独立见证报告为`verification/forcing-atomic-unique-acceptance.json`；原子构造／类型报告为`verification/forcing-atomic-code-acceptance.json`；此前内部公理证明生产报告为`verification/internal-axiom-proof-acceptance.json`；实际Con与封闭门报告为`verification/internal-consistency-closing-acceptance.json`；实际公理闭类型报告和完整标准quotation链报告分别保留为`verification/original-axiom-typing-acceptance.json`及`verification/schema-matrix-quotation-acceptance.json`。九条命令、五条trust=0均通过，零Lean警告、无新增公理依赖。43e876e远端主线已成功，Comparator在比较前的ABI预检失败；已读实际日志。本次包含兼容修复，经完整本地验收后一次性上传全部待推批次。

原第4阶段本批只准备验收入口：固定官方Comparator/lean4export已在原4.34.1编译通过；78份原输入复制与防篡改检查、拒绝Windows冒充真实验收、工作流actionlint均通过。原核CI成功后，显式`[original-comparator]`提交标记或手动参数才启动非特权、NoNewPrivileges、AF_UNIX受限及真实Landlock预检的Comparator。尚无Linux接受结果，不记为阶段4通过；报告见`verification/original-comparator-preflight-acceptance.json`。

当前原子编译推进：`ForcingAtomicCode`直接使用现有`ForcingAtomicRelations.forces`的原生模板，原核构造全部公式码、次数、项像列表和实际替换输出。输入项绑定范围允许内部／非标准自然数，自由变量范围为零；固定R及其参数个数仍为外部模式索引。两个普通nativeZF原核端点分别证明内部输出存在与准确类型。定向与全量验收、清理后trust=0复验均通过；实际验收结果见`verification/forcing-atomic-code-acceptance.json`。完整公式／任意自由变量编译、U公理解释证明及全部内部Proof/Con归约仍未完成。

原子编译单值性：本轮在保留原11项公开定义／证明正文的基础上，复用既有组件唯一性比较两套独立五见证执行，取得`unique_kernel_certificate`及`fiber_kernel_certificate`。后者的输出存在、准确类型和任意候选唯一性均在对象句内；未假设规范码、共同见证、归纳正确性或单值性。该分支服务完整递归编译的确定性，完整公式／全部Proof/Con仍未完成。验收见`verification/forcing-atomic-unique-acceptance.json`。

实际原子公式码入口：ForcingAtomCode覆盖假／真／成员／相等四分支，直接解析原实际公式码，消去外给字段；成员／相等复用既有ForcingAtomicCode，常量保留原码。真常量经既有Reverse.formula回译的bottom→bottom与原toBasic强迫取得原核规范化证明。三个普通nativeZF端点的定向及全量验收均通过；准确类型、独立解析见证下唯一性与带类型唯一输出的实际结果见verification/forcing-atom-dispatch-acceptance.json。源自由范围仍为零，完整逻辑／binder递归解释、全部Proof和Con仍未完成。

远端42483548594：原核主线成功，真实Comparator在开始比较前因ABI10要求与runner ABI8不匹配停止。兼容修复保持固定官方源码和全部验收项目，明确最低ABI8并按官方参数调用，以外层全网络／io_uring拒绝和五项实测文件拒绝覆盖所需守卫；快速Linux预检前置。新策略仅本地回归／静态检查通过，真实Linux仍待重验，原第4不可记为完成。

5596a08已上传，快速预检在28秒内发现systemd255瞬态D-Bus属性不接受字面none，原核长构建与Comparator均未启动。本轮仅将两处RestrictAddressFamilies改成空允许列表（D-Bus实际编码deny all）；全网络／io_uring过滤和ABI8／文件拒绝守卫不变。全部Lean、原核及其他2818项验收输入哈希未变，沿用5596a08形式化全量验收；兼容复验见verification/comparator-systemd255-property-fix.json。
