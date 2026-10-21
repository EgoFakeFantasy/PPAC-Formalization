# 原树有效性与实际TypedData正向解码验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点6b7833edd57da0bc4094dd70ffa9544063796a3a。
完成4c.b.3d.2b.ii与4c.b.3d.2c.i正向：原树有效性的对象成员归纳，以及无Constructor前提的实际唯一类型数据解码。
新增12模块174项显式声明、28个完整Source/sourceZF核/nativeZF核闭句模式。
反向类型识别、内部替换、ProofZF/U与最终Con仍未完成。

## 不变的对象合同

签名仍只有原等词/成员，背景仍为原YesMetaZFC的ZF纯语言像，证书仍为原FirstOrder.Derives。
不增加对象AC、Con、不可达、模型语义、外部标准ω或新的推导核。
码、变量索引、bound/free长度、后继、payload、实际长度和完整字段图都为对象变量。
外部Nat/Bool/Fin和有限字段向量只索引有限对象句子模式，每个实例实际给出原核闭句。
没有宿主WellFounded递归或从Prop抽取对象集合数据。

## 原节点与纯项的树有效性

ValidInputs(k,w,xs)是所有原输入Tree.valid的有限对象合取。
原全内部图边定律保证每条真实字段边都精确命中某个输入位置；
对象等词替换将该输入的Tree.valid传到实际边值，得到∀内部图边的ValidChildren。

任意原Node实际解码出Shape后，将Shape和ValidChildren组合为原树递归数据，
由已有原树递归双条件得到该Node的Tree.valid。Constructor消去实际标签见证后继承结论。
零字段scalar叶对任意内部自然标签有效；bvar/fvar的实际scalar字段有效，因此封装节点有效。
完整Term消去真实变量分支/索引见证后树有效，不只处理标准有限索引样本。

## 全上下文对象成员归纳

P(w,n):=∀b∀f(FormulaCode(w,n,b,f)→Tree.valid(w,n))。
Earlier(w,n):=∀x(x∈w→x∈n→P(w,x))。

| 原分支 | 实际对象推导 |
|---|---|
| falsum、truth | 零字段原构造及空有效输入合取 |
| membership、equal | 原0符号及所有同上下文Term先分别证明树有效，再组合原构造 |
| negation及四种binary | 原严格子码x∈n、子Code守卫x∈ω，调用Earlier并实例化全部上下文 |
| forall、exists | 消去真实内部k见证，在Succ(k,b)下对(k,f)调用Earlier；free不变 |

组合原11分支得到Earlier→P。
使用原Foundation以及P否定矩阵的原Separation，在内部集合ω上执行成员归纳，取得∀n∈ω P(w,n)。
Code本身的根自然守卫消去最后的n∈ω前提，最终证明：
Ω(w)→(FormulaCode(w,n,b,f)→Tree.valid(w,n))。

该闭句无残留Earlier或外部良基性前提；n、b、f遍历全部内部集合。
内部ω可以来自外部非标准模型，证明不把它等同于宿主Nat。
这里只是单向蕴含：结构上有效的任意树不必是纯语言类型正确的公式。

还证明：非原有效树正式拒绝为FormulaCode；接受码实际唯一解码为原树数据，
并在任意同根真实Shape中证明所有真实字段边的子树都有效。
关键证书为ObjectFormulaCodeTreeValidity.native_code、native_allProperties、native_decodedTree及native_treeChildren。

## 无Constructor前提的实际类型数据

RootCheck按原11个有限标签展开为Ctx或真实图上的member/equal/negation/binary/量词类型检查。
Cases(11)同时保留真实内部标签数码、精确字段数码和相应RootCheck。
TypedData(w,n,b,f,t,p,l,g)包含：
原NodeData（实际Shape及全部图边子树有效）、完整Ctx、Cases(11)。

其定义没有直接放入父FormulaCode，也没有要求给定原Constructor。
从Code的完整递归判据取得各原分支后，逐分支消去全部字段见证，
将已证同根图类型双条件、实际标签和精确长度组合为Cases(11)。
因此在任意同根实际Shape上正式推出完整TypedData。

进一步实际存在t,p,l,g，使TypedData成立，并保存对所有同根Shape的四分量唯一性。
全部见证都由对象存在量词给出，未借宿主选择构造类型数据。
关键证书是native_typedCases、native_typedData和native_typedFiber。

任意同根Shape上的¬Cases或¬TypedData正式推出¬FormulaCode。
TypedData也直接蕴含原Tree.valid，但目前尚未证明TypedData→FormulaCode。
故正向实际唯一解码已完成，完整双向识别及全部拒绝分类的总关卡保持False。

## 实际机器验收

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：原19规则锁、原九类ZF锁、Lean版本、完整wfail构建，
以及Check、CheckStep2、CheckStep3、CheckStep4、Audit五份--trust=0入口。

- 656构建任务，6678项声明审计，0警告。
- 249项无公理依赖，6429项允许依赖；Internal累计4363项显式声明全覆盖。
- 累计502对核心/native证书或模式精确依赖核验，新增28对。
- 新核心恰为propext、Classical.choice、Quot.sound；native端点另继承原七项ZF证书。
- Classical.choice是Lean证明基础依赖，没有新增对象AC；原choice额外证书仍单独限域。
- 625份源码SHA256独立回读差异0；原规则、理论、两份可信基及工具链/依赖锁不变。
- YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
- 原OpenAI完整构建与Comparator未运行；本批未推送。
- 日志、生成脚本及回读保存在忽略目录；回读为verification/tree-validity-typed-data-forward-readback.json。

CheckStep4覆盖全部28个闭句模式、四种binary及两个量词分支，
并核验对象∀b∀f归纳性质、最终Code→Tree.valid无Earlier前提的AST，以及TypedData不含Constructor参数的AST。
Audit完整枚举12个新模块的174项显式声明；verify.py逐项核对28对新证书的精确公理足迹。

## 工程流程

| 工作单元 | 证据 | 状态 |
|---|---|---|
| 4c.b.3d.2b.ii | Term及Code→原Tree.valid；原Foundation/Separation关闭全上下文成员归纳 | 完成 |
| 4c.b.3d.2c.i正向 | 任意同根Shape的TypedData，实际唯一TypedFiber，无Constructor前提 | 完成 |
| R1/R2 | 从实际槽位恢复全图，再正式恢复原forest/Constructor | 下一主项 |
| R3/R4 | TypedData反向识别与Code/TypedFiber双条件；完整识别/拒绝汇总 | 待做；总关卡False |
| 4c.c及以后 | 内部捕获规避替换、ProofZF/U、任意内部证明码正确性、内部编译器 | 待做 |
| 最终主句 | Derives nativeZF [] (Formula.imp Con_ZF Con_target) | 未完成 |

具体职责和验收表见AGENT_WORKFLOW.zh-CN.md；背景和Con的原六规则/27模式规格见OBJECT_TARGET.zh-CN.md。
原树有效性与正向TypedData门禁现True；反向识别、完整类型总门禁和最终Con仍False。
