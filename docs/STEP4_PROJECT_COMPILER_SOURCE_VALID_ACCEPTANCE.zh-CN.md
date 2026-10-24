# Project全内部源合法性反向与准确接受接口验收（2026-10-25）

本批用原Foundation证明实际Compiled产出的输入在任意内部自然源上下文中均为合法SourceCode，并给出带准确上下文守卫的接受双条件及准确类型唯一纤维双条件。10个新模块、99项显式声明、12组闭句返回原nativeZF核。

至此T1.2c.2的结构树码十二构造编译接口完成：存在性、目标类型、标量唯一及准确源合法性双向对应均为全内部对象推导。实际原ProjectEncode／NatPacket字节包、Horn、完整schema测试、Proof／解释及最终内部Con仍未完成，不能把结构树接口与原数值表示桥接混同。

## 背景和完整目标

对象语言保持纯等号／成员；背景仍为Contract.nativeZF及完整Separation／Collection；正式推导仍为原YesMetaZFC.Logic.FirstOrder.Derives。完整目标不变：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

完整Proof_T须覆盖全部内部ω、原六规则／27逻辑模式及完整理论公理模式。本批不以宿主Consistent、语义模型、结构树接口或编译成功替代最终内部Con推导。

## 实际原核结论与上下文守卫

ObjectProjectCompilerSourceValid.native_compilerAllInternalActualInputsValid给出：

~~~text
close(Ω(w) → ∀n,b,q,f
  (f∈w → Compiled(w,n,b,q) → SourceCode(w,n,b,f)))
~~~

源自由作用域f是任意内部变量。Compiled自身不以f为参数，因此不能删除f∈w守卫，也不能声称无效f会使Compiled本身拒绝。最终的准确接受定理将这一守卫放在右侧合取中，而不从对象量词中删去无效候选：

~~~text
close(Ω(w) → ∀n,b,f
  (SourceCode(w,n,b,f) ↔ (f∈w ∧ ∃q Compiled(w,n,b,q))))
~~~

这由native_compilerAllInternalSourceAcceptanceIff返回。它也处理非自然f：SourceCode及完整右侧接受式都拒绝该候选。n、b、f、q仍覆盖全部内部对象，未限制为模型外部标准自然数或有限quotation。

native_compilerAllInternalSourceTypedUniqueAcceptanceIff同时给出：

~~~text
close(Ω(w) → ∀n,b,f,z
  (Empty(z) →
    (SourceCode(w,n,b,f) ↔
      (f∈w ∧ ∃q ((Compiled(w,n,b,q) ∧ FormulaCode(w,q,b,z)) ∧
        ∀r (Compiled(w,n,b,r) → r=q))))))
~~~

其中唯一性比较所有实际Compiled产出。闭源上下文f=z时，Ω及Empty(z)实际推出z∈ω，native_compilerClosedSourceTypedUniqueAcceptanceIff消去该右侧guard，给出SourceCode(w,n,b,z)与实际typedFiber(w,n,b,z)的精确双条件。

## 原对象归纳与十二分支恢复

SourceSyntax固定correct(w,n)=∀b,q,f(f∈w→Compiled(w,n,b,q)→SourceCode(w,n,b,f))，并编码内部成员IH=∀x(x∈n→correct(w,x))。子查询的源根是被查询的输入子码x，绝不是目标输出码q；目标FormulaCode不能替代源合法性证明。

SourceQueries将真实守卫查询迁移到SourceCode，并保留量词分支原EX后继作用域。SourceMatrix从实际原子SourceAt、常量源构造器及逻辑源构造字段恢复独立源语法；一元严格子界从实际check的守卫取得，二元使用原两个guard及子SourceCode。

完整十二模式沿前批已证明的actual_cases_to_choices传输；SourceCases仅在对象EX4中消去字段见证，再返回独立源allCases。固定Mode只索引有限证明模板，不作为内部码域，也不改变实际Compiler的定义或接受条件。

SourceIH由内部成员IH和实际Compiled子查询供应SourceCode。SourceStep由真实Compiled递归方程取得输入／作用域自然守卫及局部分支，恢复源递归criterion，再使用独立SourceCode递归双条件反向得到源合法性。

ProjectCompilerSourceValid以原SetInduction作用于固定correct矩阵，使用Foundation、该矩阵否定的完整Separation及已有对象TransitiveCover，消去全部内部IH。没有外部Nat归纳、模型外部良基假设、源合法性oracle或宿主数据选择。

SourceAccepted结合前批实际存在性、准确目标类型与标量唯一性，得到准确的存在接受式、准确类型唯一接受式、闭源特例与合法上下文中的无效源拒绝。全部产出／字段见证均在对象量词内取得并消去。12组闭句经TheoryTransport.sentence进入原核，再由ZFReplay.replay返回nativeZF，CheckStep4逐组验收实际返回类型。

## 门禁与信任边界

99项新增显式声明逐一#print axioms；12组core精确依赖既定propext、Classical.choice、Quot.sound，native精确再继承原七项固定证书。没有新增自定义axiom、对象Choice背景、宿主求值oracle、预算提高或linter豁免。

scripts/verify.py核查源根／目标根区分、完整十二分支、原Foundation消去、上下文自然guard、准确接受RHS以及最终仅Ω前提。旧结构／类型／存在／唯一性推导及理论锁均继续核验。

本批实际产出反推源合法性及完整十二构造内部编译门从false改为true，含义是原T1.2c.2结构树码接口已经以原核闭句完成；原T1.2c.3数值字节包桥接是下一单元，仍未证明。准确源接受和准确类型唯一接受新增门为true；原schema数值测试、完整Proof／解释与最终Con门继续false。

## 实际验收

- 全仓2138构建任务通过；九命令及五个--trust=0入口全部退出0，零警告。
- 22966项声明审计：452项无公理、22514项仅含记录的允许依赖；99项新增显式声明全部覆盖。
- 1921份文件SHA256独立回读一致；累计2549对core／native精确公理足迹一致；20622项Internal显式声明全覆盖。
- 12组新增原核／native闭句精确足迹一致；1943任务native定向构建零警告。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净；此前跟踪的PPAC证明及AST保持原Git字节。
- 两次既有门禁变化为实际输入源合法性及十二构造结构编译false→true；原字节包／Horn、schema、Proof／解释及最终Con门禁继续false。

验收前基点6b459c5f53372774b8decbf92a6b630b1c7e4cbf。此前跟踪的PPAC证明及AST不改；本批只新增10模块、改4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,project-compiler-source-valid-readback.json}及.local/project-compiler-source-valid-native-directed.log；复验C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

全仓编译前复查残留Lean／Lake进程为0，停止进程0；本批各定向运行成功，未发现可确认无用的脚本或被替代失败日志，删除0。有效源码、缓存和有用生成／回读脚本保留；检查收据.local/workspace-cleanup-project-compiler-source-valid-result.json。

## 后续agent工程表

| 单元 | 工作 | 必须交付及实际验收 | 状态 |
|---|---|---|---|
| T1.2c.2a／b | 全内部实际产出类型与合法源存在性 | 原Foundation消去IH，实际输出具有目标FormulaCode | 前批已验收 |
| T1.2c.2c | 全内部真实标量唯一 | 所有实际产出相等，合法源有类型唯一纤维 | 前批已验收 |
| T1.2c.2d | 源合法性反向与精确输入接受 | 带f∈ω守卫的全内部输入接受双条件，闭源准确类型唯一接口；IH消去 | 本批已验收，结构树十二构造接口完成 |
| T1.2c.3 | 原ProjectEncode及实际数值证书载荷 | 核对原字段顺序、标签、NatPacket字节包；结构码与原Horn／数值编码全内部精确对应，不能只交付外部quotation实例 | 下一步，未完成 |
| T1.2c.4 | 原模式正文、指标重命名和闭合 | Sep／Collection原schema载荷及正文全内部精确对应，接此前三个实际指标系统 | 未完成 |
| T1.3／T2 | 完整公理测试及原六规则／27模式 | 共享实际Bool、Proof_ZF／Proof_target和全内部证明编译传输 | 未完成 |
| T3 | 完整数学解释及T2 | 原nativeZF内解释正确性及最终内部Con蕴含 | 未完成 |

下一单元先逐定义定位原ProjectEncode与NatPacket／Horn的准确表示，再固定双表示关系和全内部对应命题。必须同时覆盖无效候选、真实binder作用域和源／目标参数；不得把已有结构树码接口、标准quotation或宿主编码函数当作数值桥接已经完成。
