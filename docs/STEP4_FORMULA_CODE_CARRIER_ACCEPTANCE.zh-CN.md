# FormulaCode载体消去及全11已知原构造类型验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点858063753fe2a61eb4d2b4f86a70f56151955ca2。
本批完成4c.b.3d.1，并完成4c.b.3d.2中的全11已知原构造精确类型分支和任意未知内部标签拒绝。
新增16模块216项显式声明、29个完整Source/sourceZF核/nativeZF核闭句模式。
合法输入的实际带类型码构造、完整接受码解码及错码分类仍需连接；完整识别关卡不提升。

## 对象合同与载体消去

背景仍为原YesMetaZFC的ZF纯语言像，语言只有原等词和成员，证书终点为原FirstOrder.Derives。
不加入对象AC、Con、不可达、语义模型或新的推导核。
Lean的有限标签、Bool及Fin索引只索引外部定理模式；码、上下文、载体、后继及payload都为对象变量。

Carrier(w,A,C):=Power(A,w)∧Power(C,A)。
FormulaCode(w,n,b,f):=∃A∃C(Carrier(w,A,C)∧Typed(w,C,n,b,f))。
以上缩写展开为固定有限纯成员公式；这里不主张未经证明的Σ复杂度分类。

原PowerSet实际取得A、C；原Extensionality证明两组实际载体的A和C分别相等。
通过原对象等词替换规则证明：
Carrier(w,A,C) → (FormulaCode(w,n,b,f) ↔ Typed(w,C,n,b,f))。
另证明FormulaCode在任意两个真实Ω见证之间的对象等价，以及根、bound、free及ω参数的对象等词传输。
没有从Lean的存在性命题抽取宿主载体。

## 无额外载体的递归式

所有Typed子式查询已逐字段迁移为FormulaCode，保留精确原构造和严格子码成员界。
AdvancedCode(w,x,b,f):=∃k(Succ(k,b)∧FormulaCode(w,x,k,f))。
全11构造仍按原四种Atomic、否定、四种binary及两个量词排列。
CodeCriterion(w,n,b,f):=n∈w∧AllCodeCases(w,n,b,f)。

真实载体存在现已从最终前提消去：
Ω(w) → (FormulaCode(w,n,b,f) ↔ CodeCriterion(w,n,b,f))。
还证明Ω(w) → ∀n∀b∀f(FormulaCode↔CodeCriterion)。
n,b,f遍历全部内部集合，不额外假设根码自然或上下文合法。
根非自然和非法上下文分别由对象守卫证明拒绝；实际ω可以为外部非标准模型中的内部ω。

关键证书是ObjectFormulaCode.native_recursive、native_universal、native_atCarrier和native_omegaIndependent。
它们的类型均为原FirstOrder.Derives nativeZF [] (Translation.sentence ...)，结论中的蕴含、双条件和量词都是对象公式。

## 已知原构造的精确类型

先假设精确原Constructor字段关系，再由完整FormulaCode递归式排除不相容标签，恢复对应类型。
没有把已知码双条件等同于合法输入的实际带类型构造。

| 原构造 | 已知原字段 | 完整FormulaCode类型条件 |
|---|---|---|
| falsum、truth | 原0/1标签及零字段 | Ctx(w,b,f) |
| membership | 原2标签、s,x,y | ZeroScalar(w,s)∧Term(w,b,f,x)∧Term(w,b,f,y) |
| equal | 原3标签、x,y | Term(w,b,f,x)∧Term(w,b,f,y) |
| negation | 原4标签、x | Ctx(w,b,f)∧FormulaCode(w,x,b,f) |
| conj、disj、imp、iff | 原5/6/7/8标签、x,y | Ctx(w,b,f)∧FormulaCode(w,x,b,f)∧FormulaCode(w,y,b,f) |
| forall、exists | 原9/10标签、x | Ctx(w,b,f)∧∃k(Succ(k,b)∧FormulaCode(w,x,k,f)) |

两个量词还在任意给定真实Succ(k,b)下精确等价于Ctx(w,b,f)∧FormulaCode(w,x,k,f)。
该特化使用原后继唯一性和对象bound等词替换；free保持f。
所有字段恢复使用已有原同码构造器单射性；不以宿主编码值测试替代内部字段。

## 任意未知内部标签拒绝

UnknownTags(11,t)是有限合取：t不满足内部数码0至10中的任何一个。
原核证明Ω(w)、t∈w、p∈w、UnknownTags(11,t)及Raw(w,t,p,n)蕴含¬FormulaCode(w,n,b,f)。
t,p,n均为内部候选变量；没有外部标签数值界、外部标准payload长度界或固定外部深度界。
该句包括内部非标准标签；它只完成未知标签拒绝，不等同于全部错误字段数/符号/作用域分类。

## 实际机器验收

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：原19规则锁、原九类ZF锁、Lean版本、完整wfail构建，
以及Check、CheckStep2、CheckStep3、CheckStep4、Audit中的五份--trust=0入口。
最终源哈希及固定依赖另经独立脚本回读，结果保存在verification/formula-code-readback.json。

- 完整构建620任务，审计6090项声明，0警告。
- 240项无公理依赖，5850项允许依赖；Internal累计3775项显式声明全覆盖。
- 累计406对核心/native证书或模式精确依赖核验，新增29对。
- 核心证书恰为propext、Classical.choice、Quot.sound；native端点另继承原七项ZF证书。
- Classical.choice是Lean证明基础依赖；没有新增对象选择公理。原choice额外证书仍单独限域。
- 589份源码SHA256独立回读差异0；原19规则、九类ZF、两份可信基及工具链/依赖锁不变。
- YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
- 日志、构造脚本、探针和verification回读不入库；本批未推送。
- 原OpenAI完整构建与Comparator未运行，不据本仓验收声称上游已整体验收。

CheckStep4覆盖全部29个闭句模式、四种binary具体实例、两种零元实例、两个量词的真实后继特化，
并检查FormulaCode存在载体AST、量词体真实后继AST和全内部候选的三重全称式。
Audit枚举新增16模块的全部216项显式声明；verify.py逐证书核对精确公理足迹。

## 工程表更新及下一项

| 工作单元 | 实际交付 | 验收状态 |
|---|---|---|
| 4c.b.3d.1 | 实际载体消去、ω独立性、全候选无载体递归式及全称定律 | 完成 |
| 4c.b.3d.2已知码 | 全11精确类型分支、真实后继特化、任意未知内部标签拒绝 | 完成 |
| 4c.b.3d.2a | 所有合法内部输入的实际带类型原码构造 | 下一主项 |
| 4c.b.3d.2b–c | 完整接受码唯一字段解码/重编码，以及错误字段数/符号/作用域分类 | 待做 |
| 4c.b.3d.3 | 原编码的完整内部识别和构造正确性 | 待做；总关卡保持False |
| 4c.c及后续 | 捕获规避替换、ProofZF/U、全内部证明码正确性、内部编译器 | 待做 |
| 最终主句 | Derives nativeZF [] (Formula.imp Con_ZF Con_target) | 未完成 |

完整工程表见AGENT_WORKFLOW.zh-CN.md；背景和内部Con的原六规则/27模式规格见OBJECT_TARGET.zh-CN.md。
对象背景、Con定义及全内部ω范围均未缩小；不将本批语法判断证书称作最终相对一致性证明。
