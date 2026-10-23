# 原规则轨迹扩展及模式0/3变量正分支验收

基点：cdb74dc5fd3d3f2ebb8f81f796455f4241621c24。只完成S3.4c.2b.2c.3c.2a正分支；完整原数值接口与最终Con仍未完成。

## 对象合同

背景保持原nativeZF（完整Collection呈现），对象语言只有等词／成员。最终目标保持原FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target为ZF+PP+ACwo+¬AC；内部Con量化全部内部ω证明码，检查器仍须覆盖原六规则／27模式、完整Separation／Collection。

本批每个运行时参数、赋值、行、轨迹都是对象变量。固定原Rule／Expr和arity只作为外部有限定理模式索引。新增15组闭句均由Source.Derives经TheoryTransport、ZFReplay返回原核证书。没有新公理、推导核或宿主模型假设。

## 实际实现

| 文件 | 对象层实现 | 使用位置 |
|---|---|---|
| HornTraceMonotone | 从R⊆S逐前提提升；有限前提合取、矩阵、原arity存在赋值块、任意固定规则表及完整原表均保持原步骤；另给行等词替换 | 保留原轨迹的每个既有推导 |
| HornTraceExtension | 已验收原Pairing／Union实际构造S=R∪{r}；证明包含R、S⊆ω、S闭合并取得含r的真实轨迹 | 从一个已有闭轨迹接入新的原根规则 |
| OriginalScalarPositive | 直接使用boundIdentity 0、boundIdentity 3、freeWeaken、freeReplace的真实head／premises，按原头表达式的出现变量推出搜索赋值界 | 模式0／3的四个变量正分支 |
| ObjectScalarTrace | 15组闭句、源推导及两层原核回放；包括四个实际P(ω)搜索闭轨迹结论 | 审计与CheckStep4验收 |

轨迹扩展的对象推导合同为：R⊆w、r∈w、Closed(w,R)、OriginalStep(w,r,R)推出Trace(w,r)。实际存在见证通过原InsertExistence取得，未假设预先给定S。ClosedInsert先按任意内部z∈S分为z∈R或z=r，再使用原表单调性／等词消去；不使用外部有限轨迹或ω标准性。

四个变量正分支的前提是Omega(w)、原arity自然赋值EnvNat和真实原头表达式Graph。原表中的模式0绑定变量保持不变、模式0自由变量索引后继、模式3绑定变量保持不变。模式3自由替换另外要求已证明的内部Executed(w,parameter,index,output)。后者实际构造原tag0查找子行，利用规范成功行集合的成员定理及原child_member_iff，取得freeReplace真实查找前提；随后按原四变量存在块取得应用、插入根行、转换到实际P(ω)搜索轨迹。

这里Graph(head,env,r)仍是原Expr AST的纯关系式编译前提。尚未给出这些原头与独立boundValue／freeValue数值输出的双向对应，不能据此宣称完整变量接口或完整模式0／3已完成。

## 语言桥核查及剩余边界

原ObjectHorn.Expr.term使用BasicSetTheory扩展签名中的emptySet／successor／godelPairing；原ObjectTrace还使用omega／powerSet等符号。该签名与本工程纯成员签名不同。原godel_pairing_definition位于单独非逻辑算术理论中，不能把那些扩展语言公理直接加入nativeZF，也不能把两种语言公式当作字面相等。需证明所需原公式片段的图消去及赋值／定义对应，再关闭quotation总桥。本批不导入新的扩展理论假设，原quotation总门继续为false。

下一步：在真实完整原表上完成tag1、mode0／3及输入变量构造子的精确分派，证明四个变量分支的可靠性／失败方向以及与独立数值接口的对应；同时关闭所需扩展语言片段的图消去桥。随后全11公式、原规则5／4、专用ProofZF/U及内部解释和Con均仍待完成。不附加FreeClosed、可数传递模型、标准性或选择前提。

## 实际验收

1326构建任务、14496项审计（371无公理／14125允许依赖）、零警告；九命令及五trust=0入口全部退出0；1190份工作区独立哈希一致、1581对精确证书足迹、12152项Internal显式声明覆盖。新增4模块81声明、15组闭句及15对精确证书；核心为std3，原native证书为std3加原七证书依赖。七锁、Choice桥及固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净依赖状态不变。证据见本地verification/scalar-trace-readback.json与verification/commands.json。

实际执行定向lake build --wfail和C:/Python314/python.exe -X utf8 scripts/verify.py；LEAN_NUM_THREADS=1，全程串行。验收数字取最终完整验证及独立回读。未执行OpenAI原仓完整构建、Comparator、推送或PR。
