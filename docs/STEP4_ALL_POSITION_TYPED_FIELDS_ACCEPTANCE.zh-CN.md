# 全内部位置及字段图类型检查验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点935a97f146d3f7c2218daf02598a742041b77b57。
本批完成4c.b.3d.2b.i：原forest与完整字段图的全部内部位置对应，并装配已知原构造下的字段图类型检查。
新增12模块155项显式声明、22个完整Source/sourceZF核/nativeZF核闭句模式。
原树递归有效性、完整TypedData解码/反向识别、内部替换、ProofZF/U及最终Con仍未完成。

## 对象合同

语言仍只有原等词/成员；背景仍为原YesMetaZFC的ZF纯语言像；最终证书为原FirstOrder.Derives。
不增加对象AC、Con、不可达、模型语义前提或新的推导核。
外部k、j、有限变量向量及纯公式矩阵只索引有限对象句子模式，每个实例实际返回原核闭句证明。
内部索引i、值y、根码、payload、长度、完整字段图和bound/free上下文均为对象变量；
特别不把i或内部ω限制为外部标准自然数。

## 完整数码域与字段位置

Below(k,i)是Num_0(i)至Num_(k-1)(i)的有限对象析取，空析取为bot。
原核对所有内部候选i证明Num_k(l)→(i∈l↔Below(k,i))。
该证明使用实际后继见证、原插入集成员双条件、数码唯一性和对象等词替换。

Positions(k,xs,i,y)是所有j<k的Num_j(i)∧y=xs_j的有限对象析取。
给定原Forest(k,w,xs,p)、真实HasLength(w,p,l)、完整Fields(w,p,l,g)及Ω(w)，证明：
Edge(g,i,y) ↔ Positions(k,xs,i,y)。
另在对象层闭合∀i∀y，得到完整GraphLaw。
这涵盖全部内部索引和值：不在真实域内的索引也被正式排除，重复字段值及变量别名不被排除。

在任意给定实际Num_j(i)下，原投影/真实后继方程证明Field(w,p,i,y)↔y=xs_j。
完整Fields的域和全边精确式随后给出Edge(g,i,y)↔y=xs_j。
外部对有限模式k/j的归纳构造对象证书，不是对任意内部自然码作宿主递归。

## 原构造与任意同根Shape

原Node与同根真实Shape的payload相等由原raw配数单射性推出。
将Forest通过该对象等词传输到实际解码payload，再取得同一完整字段图上的GraphLaw。
原Constructor消去真实标签见证后继承该结论。
没有假定两份payload或图相等，也不以同输入编码唯一性代替同码字段恢复。

Slot(g,j,y):=∃i(Num_j(i)∧Edge(g,i,y))。
原核证明Slot(g,j,y)↔y=xs_j。
反向实际构造内部数码索引见证，再构造真实图边；没有使用宿主选择函数。
关键证书为ObjectSyntaxTypedFields.native_forestAll、native_constructorAll、native_constructorValue及native_slot。

## 任意外部纯公式模式与四种类型实例

Checked(P,ρ,g,j):=∃y(Slot(g,j,y)∧P_ρ(y))。
对任意有限纯公式矩阵P、任意全部参数ρ，原核证明：
Checked(P,ρ,g,j) ↔ P_ρ(xs_j)。
证明只使用实际Slot、对象等词规则和原存在规则。
P是外部定理模式索引，每个实例是完整纯成员对象句子；没有引入内部统一真值谓词。

| 实例 | 字段图上的真实检查 | 精确对应的原操作数条件 |
|---|---|---|
| codeField | 实际槽位值满足FormulaCode | FormulaCode(w,xs_j,b,f) |
| termField | 实际槽位值满足完整Term | Term(w,b,f,xs_j) |
| advancedField | 实际槽位值满足∃u(Succ(u,b)∧FormulaCode(w,xs_j,u,f)) | 原量词体的真实后继bound及不变free |
| zeroField | 实际槽位值满足原ZeroScalar | 原membership编号0符号 |

## 已知原构造下的父类型

给定精确原Constructor及任意同根真实Shape，证明父FormulaCode等价于以下真实图检查：
membership为zeroField(0)及termField(1)、termField(2)；
equal为两个termField；negation为Ctx及codeField(0)；
四种binary均为Ctx及codeField(0)、codeField(1)；
两个量词均为Ctx及advancedField(0)。
任意真实Succ(u,b)下，两个量词另精确等价于Ctx及codeField(0,u,f)。
零元常量保持前批已证的完整Ctx双条件，无需读取不存在的字段。

这些定理仍带已知原Constructor前提。
尚未证明从任意完整图类型数据反向重建并消去该前提，因此不能宣称完整TypedData接受/拒绝已完成。
同样，当前完整图字段对应不能代替原StructuralTree.valid的递归有效性证明。

## 实际机器验收

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：原19规则锁、原九类ZF锁、Lean版本、完整wfail构建，
以及Check、CheckStep2、CheckStep3、CheckStep4、Audit五份--trust=0入口。

- 644构建任务，6504项声明审计，0警告。
- 249项无公理依赖，6255项允许依赖；Internal累计4189项显式声明全覆盖。
- 累计474对核心/native证书或模式精确依赖核验，新增22对。
- 新核心恰为propext、Classical.choice、Quot.sound；native端点另继承原七项ZF证书。
- Classical.choice是Lean证明基础依赖，没有新增对象AC；原choice额外证书仍单独限域。
- 613份源码SHA256独立回读差异0；原规则、理论、两份可信基和工具链/依赖锁不变。
- YesMetaZFC仍固定039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
- 原OpenAI完整构建/Comparator未运行；本批未推送。
- 日志、生成脚本和回读留在忽略目录；独立回读为verification/syntax-typed-fields-readback.json。

CheckStep4覆盖全部22个完整闭句模式、四种binary和两个量词的真实后继实例，
并核验∀内部i∀y完整图定律、真实索引Slot存在AST及AdvancedCode后继bound AST。
Audit显式枚举全部12个新模块的155项声明；verify.py逐项检查22对新证书的精确公理足迹。

## 工程流程及下一项

| 工作单元 | 对象层验收 | 状态 |
|---|---|---|
| 4c.b.3d.2b.i | 全内部i/y位置双条件、真实Slot、任意纯公式模式及四类类型检查传输 | 完成 |
| 已知原构造的图检查 | 全部非零元父类型精确对应同根实际图；两个真实后继量词实例 | 完成；仍有Constructor前提 |
| 4c.b.3d.2b.ii | Term→Tree.valid，并以对象ω成员归纳证明FormulaCode→Tree.valid，保留全上下文 | 下一主项 |
| 4c.b.3d.2c.i | 完整TypedData实际唯一解码及反向重建，消去已知Constructor前提 | 待做 |
| 4c.b.3d.3 | 完整识别/构造正确性及递归错误符号/操作数/作用域排除 | 待做；总关卡False |
| 4c.c及以后 | 内部捕获规避替换、ProofZF/U、任意内部证明码正确性和内部编译器 | 待做 |
| 最终主句 | Derives nativeZF [] (Formula.imp Con_ZF Con_target) | 未完成 |

详细流程见AGENT_WORKFLOW.zh-CN.md，背景及Con的原六规则/27模式规格见OBJECT_TARGET.zh-CN.md。
完整类型识别、递归树有效性、完整TypedData和最终Con的门禁均保持False。
