# 固定纯项程序的全内部运行时正确性验收

2026-10-23；S3.4c.2b.2c.1；基点 c15e759511bff7d3f7f7c39fccd05800422144c9。

本批只完成固定纯项程序单元。背景仍为原 nativeZF（完整 Collection），对象语言仍为纯等词／成员语言，证书仍使用原 FirstOrder.Derives。最终目标仍是 nativeZF 中的 Con_ZF → Con_target，目标理论 ZF+PP+ACwo+¬AC；Con 遍历全部内部 ω 证明码。完整公式程序、检查器、内部解释与最终 Con 蕴含尚未完成。

## 本批实际证明

TermTransformProgramSyntax 给出独立有限程序 DSL：按顺序识别 bound/free 变量，从实际数值像表读取原索引对应字段，未识别时复制输入。run 由 DSL 组合编译成纯对象公式，核心没有调用旧 CodedMixedTerm 判断；checked 额外检查原纯项类型和实际像表环境。TermTransformProgramControl/Variable 用对象存在消去恢复实际索引、原变量解码唯一性及分支互斥证明有序执行行为。

TermTransformProgramCorrectness.checked_iff 在 Omega(w) 下证明：

```text
∀R S a b c d n q,
  Checked(w,R,S,a,b,c,d,n,q) ↔ OriginalCodedMixedTerm(w,R,S,a,b,c,d,n,q).
```

这里所有八个运行时参数都是对象变量，没有外部原生项、标准自然数索引、模型标准性或深度上界。合法输入的实际输出存在，具有原目标项类型、内部自然数范围，并与全部 checked 输出候选比较唯一。fiber_iff_input 给出实际有类型唯一输出纤维与完整合法输入检查的精确双条件。环境或源类型不成立时拒绝；目标类型或输出自然数范围不成立时也不能接受。

TermTransformProgramCodeSyntax.uniform 把上述八个参数放在同一个对象公式的八层全称量词内。existsProgram 是真正的对象存在句：

```text
∃P (P∈w ∧ Code_fixed(P) ∧
    (∀R S a b c d n q,
       (Code_fixed(P) ∧ Checked(...)) ↔ OriginalCodedMixedTerm(...)) ∧
    ∀P' (Code_fixed(P') → P'=P)).
```

TermTransformProgramCode.exists_correct_program 从原树编码存在性实际取得 P，通过对象存在消去构造上述证明。ObjectTermTransformProgram.native_existsCorrectProgram（例如 m=1、w=0 的闭句实例）返回原 FirstOrder.Derives nativeZF []；19 组闭句均有 source、sourceZF 原核证书和 nativeZF 原核证书。

## 必须保留的边界

这是固定外部有限 DSL 的组合编译执行公式及其实际规范码。P 是实际对象自然数，运行时参数全部内部量化；尚未实现读取任意内部程序码并执行的通用解释器，也未证明 DSL 序列化／通用解释器之间的普遍编译正确性。程序树的 DSL 标签是程序自身约定，运行时项的解析仍沿用原 SyntaxEncode／结构数值编码，两者不能混同。

纯签名没有函数符号，有效纯项只有 bound/free 变量。因此 checked 的源类型守卫排除扩展签名 app 输入。本批没有声称未受检核心在所有原始树上与原递归 app 分支相同；copy_default_iff 仅说明本 DSL 在两个变量识别均失败时的复制行为。完整十一构造器公式程序仍须处理递归、量词下双像表提升及全部内部子码，不能由此前外部有限 quotation 模式直接宣布完成。

没有新增对象公理、宿主见证抽取、替换推导核、完备性捷径或退役反射实现。

## 实际验收

- 全仓严格构建：1146 jobs，退出 0；全部九条验收命令退出 0，五个 trust=0 入口通过。
- 声明审计：12814 项，351 项无公理依赖，12463 项符合记录依赖；零警告，禁止补洞标记检查通过。
- 本批 9 模块、144 条显式声明、19 组新闭句；累计 10470 项 Internal 显式声明全部纳入审计。
- 19 组新证书及累计 1387 对证书逐项匹配：sourceZF core 恰为 propext/Classical.choice/Quot.sound，nativeZF 恰为该三项加原固定七项证书；隔离 Choice 桥的额外依赖没有扩散。
- 独立读回 1044 份工作区文件 SHA-256 全部一致；七项锁文件与固定 YesMetaZFC 提交 039c8e132cc19671d73a3933c66b4799d2599dd6 不变，依赖工作区干净。
- 仅四项 fixed_pure_term_program 细分门置真；完整内部公式程序、通用内部程序解释器、规则兼容、检查器、内部解释与最终 Con 等总门保持未完成。

严格命令：LEAN_NUM_THREADS=1，C:\Python314\python.exe -X utf8 scripts/verify.py。该入口串行运行来源规则／理论核查、版本核查、全仓 lake --no-cache --wfail build 和五个 --trust=0 Lean 入口。verification/ 下日志及独立读回只保留本地；没有运行原 OpenAI 全构建或 Comparator，没有推送或创建 PR。

## 下一步工程门

| 单元 | 输入／实现 | 必须取得的对象推导验收 | 状态 |
|---|---|---|---|
| 2c.1 | 独立固定纯项 DSL、实际表字段、完整类型守卫 | 所有内部运行时等价、精确输入域、实际唯一输出、实际唯一程序码与统一闭句 | 本批完成 |
| 2c.2 | 独立十一分支公式程序、双表提升、实际内部递归历史 | 全部内部有效公式码上的原操作等价；无效候选处理；实际输出 | 待完成 |
| 2c.3 | 完整原操作接口及纯语言编码 | substituteFree/weakenFree 原规则5/4兼容，保留上下文及非单射替换 | 待完成 |
| 5 | 原六规则／27逻辑模式、完整 Separation/Collection | 专用 ProofZF/U 纯 AST、全部内部码的检查／编译正确性 | 待完成 |
| 6 | 完整 L／对称扩张构造与目标理论解释 | 原 ZF 内的完整内部解释及证明翻译；禁止附加标准性或选择前提 | 待完成 |
| 7 | 原内部 Con_ZF 与 Con_target | 原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target) | 未证明 |
