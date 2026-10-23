# 四种二元逻辑规则与统一对象归纳步骤验收

基点：4262425ea31fb4b9c0a5ac406729592f694e7c43。完成3f.2c.3b.2c.3a；5模块61项显式声明、8组闭句。

## 背景与最终目标

固定原YesMetaZFC等词／成员语言、完整Separation／Collection背景nativeZF及原FirstOrder.Derives。最终目标仍为：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con覆盖全部内部ω证明码和原六规则／27模式。本批未证明主句，不添加对象AC、标准ω、外部良基或新推导核。

## 统一内部上下文与真实前提

PureSyntaxFormulaInductionSyntax定义：

```text
correct(w,n) := ∀b ∀f
  (PureFormulaQuery(w,b,f,n) ↔ FormulaCode(w,n,b,f))
allIH(w,n) := ∀x (x∈n → correct(w,x)).
```

绑定界b、自由界f均在对象全称量词中变化；严格成员IH是对象公式。定义本身不代表所有根码correct已经证明。

PureSyntaxFormulaPremise的绑定界输入可以是任意固定原表达式。construct由实际字段图及真实子公式行构造原前提图；checked从真实EX前提行与同一闭轨迹取得子公式查询；typed_from_induction只在实际严格子码处实例化上述统一IH，以恢复准确上下文的FormulaCode。该接口也允许后续量词使用实际后继值，不假设宿主上下文长度。

## 四种原二元规则

PureSyntaxBinaryRule精确保留binaryRule 5／6／7／8、原head字段和两个kind4子公式前提。kind : Fin 4仅为固定四条规则的外部模式索引；运行字段和轨迹均是内部对象。

input_iff连接实际输入表达式图与原BinaryCode。known_iff统一已有四个对象类型双条件，使用不带历史参数的FormulaCodeBranchSyntax.binaryTypes。

matrix_sound和application_sound从实际原规则应用恢复两个子公式码，用原构造的child_member证明它们严格属于父输入码，随后在实际绑定界／自由界处实例化对象IH并取得父FormulaCode。它们不预给父FormulaCode，仍明确要求allIH、轨迹子集和闭合性。

matrix_complete和application_complete使用真实两个子行及其在同一轨迹中的成员关系构造原有界规则应用；搜索界来自实际head变量界。

PureSyntaxBinaryComplete.condition_from_rows实际合并两条子轨迹，构造并插入父行；from_rows再实际取得父编码行。checked_from_children从两个合法子公式及其实际查询与BinaryCode出发，消去所有子行、父行和公共轨迹见证。

typed_binary_checked的闭句合同保留明确IH：

```text
Ω(w) → allIH(w,n) → FormulaCode(w,n,b,f) → BinaryCode(kind,w,x,y,n) →
  PureFormulaQuery(w,b,f,n).
```

两个实际子码的严格成员关系在证明内取得，不由宿主递归或外部良基代替。这里的IH尚待完整十一公式分支与原ZF集合归纳统一消去。

ObjectPureSyntaxBinary提供八组source／kernel／native闭句。CheckStep4还直接展开上述带IH的对象合同，并以rfl核对实际原head。

## 实际验收

1562构建任务、16900项审计（390无公理／16510允许依赖）、零警告；九命令及五trust=0入口全部退出0；1424份独立哈希一致、1914对精确证书足迹、14556项Internal显式声明覆盖。

- scripts/verify.py退出0；全仓--wfail与五trust=0入口全部通过。
- 新增61项声明显式列入Audit；八组kernel证书精确保持三项标准依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核所有源哈希和证书对，两个变化上下文的对象量化，以及最终二元接口仍保留IH、实际见证均在对象EX中消去。
- 七锁文件和YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变；上游工作树干净。
- 无新增sorry／admit或占位公理；未更改纯接受定义或原十五规则表。
- 有限四种规则的分类改为显式标签5／6／7／8证明，不假设Rule具有可判定相等性，也未引入新的判定公理。

证据：verification/pure-binary-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另复核Git原始字节，保留17份既存CRLF-only blob。

## 后续工程流程及未完成范围

| 顺序 | 实现任务 | 对象验收条件 | 状态 |
|---|---|---|---|
| 1 | 四原子构造 | 完整Source原子取得真实查询；原规则局部健全 | 已验收 |
| 2 | 四二元连接词 | 实际规则和父查询构造，统一严格成员IH明确保留 | 本批完成 |
| 3 | 否定、两个量词 | 原unary前提；实际内部绑定界后继与变化参数IH | 待证明 |
| 4 | 完整公式分派 | 完整十五规则、十一公式构造的同一correct归纳步 | 待证明 |
| 5 | 原ZF集合归纳 | 消去全部公式IH，任意内部kind4查询↔FormulaCode仅需Ω | 待证明 |
| 6 | 数值检查器与最终迁移 | quotation／Option、ProofZF/U、内部解释和Con | 待证明 |

本批只开启统一IH公式构造、二元条件步骤及实际轨迹构造门。公式IH消去、全部逻辑规则桥、完整kind4桥、原数值检查器及最终Con门保持false。总体目标保持active。
