# 完整十一分支公式程序的全内部对象证明验收

2026-10-23；S3.4c.2b.2c.2；本批基点 6a11387f526624144da8dcea9108dd5c3954b289。

本批完成固定纯公式程序的独立组合编译、实际内部递归及全内部运行时规格正确性。背景为原 nativeZF 的完整 Collection 呈现，对象语言为纯等词／成员语言，证书为原 FirstOrder.Derives。最终 Con_ZF → Con_target 仍未证明；目标仍是 ZF+PP+ACwo+¬AC，Con 仍遍历全部内部 ω 证明码，保留原六规则／27逻辑模式及全部 Separation/Collection 实例。

## 程序与原推导证书

FormulaTransformProgramSyntax 定义 Instruction／Program 和固定十一分支 formulaProgram。compileInstruction／run 把有限程序组合编译为纯 Source.Formula；不是旧公式判断、旧 criterion 或旧 operator 的别名。分支在实际原节点构造上匹配：

| 原构造 | 运行时行为 | 全部内部数据 |
|---|---|---|
| falsum／truth，标签0／1 | 原零字段节点的源／目标重建 | 节点码、两端上下文长度 |
| membership，标签2 | 保留原成员符号0，两个项调用独立受检项程序 | 符号码、项码、实际像表及输出码 |
| equality，标签3 | 两个项调用独立受检项程序并重建原节点 | 两个实际子项／输出及像表 |
| negation，标签4 | 从实际历史读取严格较小子码的结果 | 子码、历史图、目标子码 |
| 四个二元连接词，标签5–8 | 读取两个严格较小子码的结果并重建节点 | 两个子码、历史图及两个输出 |
| forall／exists，标签9／10 | 实际取得 A,C,K,H 双表提升见证，按新元数据读取子码 | 源／目标后继长度、两份新像表、子码及结果 |

FormulaTransformHistorySyntax 直接展开图的真边、七字段状态及其成员关系。量词通过已验收的原数值 binder 库子程序实际取得四个见证；其 bound 表补入新变量并移动旧像，free 表也移动全部像，不能只提升一张表。公式原子指令实际调用上一批独立项程序；没有把旧项替换判断作为该项程序的执行原语。

这是用已证明数值库子程序建立的固定关系式编译器。分支以原构造形状匹配，程序输出的唯一性由对象证明取得。它没有实现读取任意内部 Program 码的通用解释器，也未声称对所有原始非法树保留宿主 SyntaxSubstitution 的默认复制行为。纯签名没有函数符号，合法 FormulaCode 排除扩展签名 app／其他关系符号。

## 关键证明链

| 模块／定理 | 对象层结果 |
|---|---|
| FormulaTransformAtomCorrectness.membership_iff／equality_iff | 每个实际内部子项调用与旧原子规格双向对应 |
| FormulaTransformStepCorrectness.step_iff | 对任意内部历史 h 的完整十一分支步骤双条件 |
| FormulaTransformOperatorCorrectness.row_iff／value_iff | 七字段状态行及实际 Separation 集合值逐候选双向对应 |
| FormulaTransformRecursionCorrectness.history_iff／equations_iff／graph_iff | 传输完整原递归方程，保留同一个实际限制图和真边 |
| actual_recursors／graph_exists／evaluation_exists | 全部内部原序数上实际唯一递归图；每个内部自然数源索引的实际求值 |
| execution_iff | 新执行判断对全部内部运行时参数与原混合公式代入规格等价 |
| FormulaTransformValue.actual_fiber／fiber_iff_input | 合法输入取得实际有类型唯一输出，且该纤维恰好等价于完整合法输入 |
| FormulaTransformProgramCode.exists_correct_program | 固定程序取得实际唯一内部码，并有同一句子内的八参数统一正确性 |

传输以对任意内部历史的算子双条件为起点，逐一穿过真实 Separation、递归方程和实际后继域求值。没有对外部 Tree 做输入归纳，没有假设内部自然数标准，没有外部深度上界，也没有以宿主模型语义或完备性替代推导。

execution_iff 的全部 R,S,a,b,c,d,n,q 都是对象变量。输出 value 同时包含执行、原目标 FormulaCode、q∈ω，以及对所有内部候选输出的唯一性。source／environment／完整input／target／非自然数output五类拒绝性质均有对象证明；不是只对外部逐例输入测试。

FormulaTransformProgramCodeSyntax.uniform 明确含八层对象全称量词；existsProgram 的含义是：

```text
∃P (P∈w ∧ Code_fixed(P) ∧
    (∀R S a b c d n q,
      (Code_fixed(P) ∧ Executed(w,R,S,a,b,c,d,n,q)) ↔ OriginalMixedFormulaSubst(...)) ∧
    ∀P' (Code_fixed(P') → P'=P)).
```

ObjectFormulaTransformProgram.native_existsCorrectProgram（例如 m=1、w=0 的闭句实例）给出原 nativeZF 中 ∀w(Omega(w)→existsProgram(w)) 的证书。程序码 P 是在对象量词内实际取得的自然数；程序本身是外部固定有限常量，DSL 标签与原运行时 SyntaxEncode 标签各有明确用途，不能当作已实现通用内部程序解释。

30组闭句都有 Source 推导、sourceZF 原核证书和 nativeZF 原核证书。程序核心的8个源模块另有直接引用审计，禁止调用旧完整公式 judgment／criterion／operator／evaluator 或旧项代入判断；对照证明和规格公式可以引用旧判断。该静态门只证明直接源码引用约束；库子程序的对象正确性由既有推导和本批组合证明承担。

## 实际验收

- 全仓 lake --no-cache --wfail build：1164 jobs，退出0；九条验收命令及五个 --trust=0 入口均退出0。
- 声明审计：13102项，357项无公理依赖、12745项符合记录依赖，零警告；禁止补洞标记检查通过。
- 本批18模块、288条显式声明、30组闭句；累计10758条 Internal 显式声明全部纳入审计。
- 30组新证书与累计1417对 core/native 证书逐项匹配：core恰为 propext/Classical.choice/Quot.sound；native恰为该三项加原固定七项。原独立 Choice 桥额外依赖未扩散。
- 核心8模块的直接旧判断引用门通过；1062份工作区文件独立 SHA-256 全部一致。
- 七项锁文件不变；YesMetaZFC固定在039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
- 五项 fixed_pure_formula_program 细分门及全内部公式程序统一正确性门置真；通用内部程序解释器、原规则兼容、专用证明检查器、完整内部解释与最终Con等总门保持未完成。

命令：LEAN_NUM_THREADS=1，C:\Python314\python.exe -X utf8 scripts/verify.py。全仓构建与所有 Lean/Lake 入口串行运行。verification/ 日志、独立读回与 .local/ 生成器只保留本地；没有推送或创建 PR，没有运行原 OpenAI 全构建或 Comparator。

## 后续工程门

| 单元 | 下一步输入与实现 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S3.4c.2b.2c.1 | 独立固定纯项程序 | 全内部等价、精确合法域、实际有类型唯一输出、统一码句子 | 上批完成 |
| S3.4c.2b.2c.2 | 固定十一分支公式程序及实际递归 | 全内部执行／规格等价、实际图／求值／输出、拒绝性质和统一码句子 | 本批完成 |
| S3.4c.2b.2c.3 | 原 substituteFree／weakenFree 的完整编码及新程序接口 | 规则5／4在全部内部上下文、非单射替换及量词下的检查兼容 | 下一步 |
| 5 | 专用 ProofZF/U 纯 AST，原六规则／27模式和完整模式公理 | 全部内部 ω 证明码的检查／编译正确性 | 待完成 |
| 6 | 完整 L／对称扩张及目标理论内部解释 | 原 ZF 内所有目标公理及证明翻译；不添加标准性或选择前提 | 待完成 |
| 7 | 原内部 Con_ZF 与 Con_target | FirstOrder.Derives nativeZF [] (Con_ZF → Con_target) | 未证明 |

与原宿主 SyntaxSubstitution 操作的直接 quotation 仍保留此前外部有限有效模式的验收边界；不得仅因本批新程序／原内部规格等价，就把更宽的原操作接口、任意内部程序解释器、Proof检查器或最终 Con 总门置真。
