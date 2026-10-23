# 首槽公式判断与原核证书验收

2026-10-23；分支 migration/yesmeta-step3；本批基点 7d17141bcf691e748b8158dcac4cc9cb35ce058a。
S3.4c.1 已验收：首槽公式判断的数值环境见证完全由对象量词绑定，实际输出总唯一，并取得完整 11 构造端点。
S3.4c.2 的原操作数值 quotation 对应、专用内部证明检查器及最终 Con 主句尚未完成。

## 对象合同

对象语言仍是 YesMetaZFC 原单排序纯等词/成员语言。背景是原 nativeZF 的完整 Collection 呈现；完整源 Replacement 已经对象互导接入。
目标理论仍为 ZF+PP+ACwo+¬AC。最终交付必须是原核：

```text
YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)
Con_T := ¬∃p (p∈ω ∧ Proof_T(p,code(⊥))).
```

此处 Con 是锁定数学规格，ProofZF/U 的完整有限纯 AST 尚未实现。
证明量词必须遍历全部内部 ω 码，保留原六条规则、27 模式及完整 Separation/Collection；不得改成宿主一致性或标准深度有界版本。
本批实际提供的对象推导是以下语法操作闭句实例，并不声称已经取得最终 Con 推导。

## 无外部环境见证的公式判断

以下全部是有限纯对象公式的缩写；R、S、q 以及其隐藏图见证均为内部对象。

```text
Instantiate(w,a,b,A,t,n,q) :=
  ∃R∃S (InstantiateCoded(w,a,b,A,t,R,S) ∧
         MixedSubst(w,R,S,A,b,a,b,n,q)).
InstantiateInput(w,a,b,A,t,n) :=
  Term(w,a,b,t) ∧ Succ(A,a) ∧ FormulaCode(w,n,A,b).

Abstract(w,a,b,A,B,n,q) :=
  ∃R∃S (AbstractCoded(w,a,b,A,B,R,S) ∧
         MixedSubst(w,R,S,a,B,A,b,n,q)).
AbstractInput(w,a,b,A,B,n) :=
  Contexts(w,a,b) ∧ Succ(A,a) ∧ Succ(B,b) ∧ FormulaCode(w,n,a,B).
```

实现中合取按明确 AST 括号结合。Instantiate 源范围为 (A,b)、目标为 (a,b)；Abstract 源范围为 (a,B)、目标为 (A,b)。
任一实际合法码对 R/S 都与同一对象判断双向等价；证明先按原对象相等对齐候选环境码，再在实际 MixedSubst 判断中执行对象等词替换。
由此两份判断的输出唯一性不依赖外部选定 R/S，也不从求值集合唯一直接推断公式输出唯一。

已证明：准确环境输入、源/目标 FormulaCode、源/目标自然码守卫、实际输出存在、任意两输出相等、实际唯一输出纤维。
在 omega(w) 下，存在输出及唯一输出纤维分别恰等价于准确合法输入；非法输入没有输出。
这些推导覆盖全部内部候选；空范围按准确输入判断，不暗加非空域或外部标准性条件。

## 完整构造端点

在准确输入及已知原源/目标构造的守卫下，两种操作都具有以下精确双条件：

| 原构造 | 已证明的对象端点 |
|---|---|
| ⊥、⊤ | 父判断 ↔ 输出码等于输入码 |
| 等式 | 父判断 ↔ 同一内部环境码对下两项操作数判断 |
| 成员关系 | 父判断 ↔ 原成员符号码及两项操作数判断，保留原符号对应 |
| 否定 | 父判断 ↔ 同一首槽操作的子判断 |
| 合取、析取、蕴含、双条件 | 父判断 ↔ 两个首槽子判断的合取 |
| 全称、存在 | 父判断 ↔ 实际双表提升后的子公式查询 |

量词查询内部绑定实际后继源/目标范围和实际提升后的两份原环境码。
新 bound0 保留，旧 bound 源索引后移，free 源索引保持；两张像表的目标 bound 分量都位移。
这是真实混合 binder 递归端点；它尚不能替代与原 instantiate/abstract 操作的完整数值 quotation 对应。

## 原核传输与实际验收

ObjectTopFormula 的 40 组闭句模式分别给出 Source.Derives、原 sourceZF 像核证书和原 nativeZF 核证书。
最后一类实际返回 FirstOrder.Derives nativeZF [] (Translation.sentence φ)，不是语义模型假设。
有限外部 Bool/Fin 4 只索引构造模式，每个实例均有闭句及原核推导；不引入内部统一真值断言。

执行 `C:/Python314/python.exe -X utf8 scripts/verify.py` 并独立回读：

- 1002 构建任务；11877 项审计，其中 308 项无公理依赖、11569 项仅记录内允许依赖；0 警告。
- 九条命令全部退出 0；其中五个 `--trust=0` 入口全部退出 0。
- 本批 10 模块、274 显式声明、40 组闭句；累计 9562 项 Internal 显式声明全覆盖。
- 971 份源哈希独立一致；累计 1244 对核心/native 证书足迹精确匹配。
- 每组核心精确为 propext、Classical.choice、Quot.sound；native 精确增加未修改原底座的七项固定句子证书依赖。独立选择桥的额外范围保持隔离。
- 七份理论/规则/可信基/工具链锁文件逐字节规范化核对不变。
- YesMetaZFC 固定 039c8e132cc19671d73a3933c66b4799d2599dd6 且依赖工作区干净。

没有新增对象公理、宿主数据选择、模型前提或深度界。原 OpenAI 全构建及 Comparator 未运行。未推送、未建 PR；辅助生成器、日志及独立回读留在本地忽略目录。

## 后续 agent 工程流程

| 单元 | 输入/前置 | 必须交付与验收 | 状态 |
|---|---|---|---|
| S3.4a/b | 原变量项码、真实环境表、原列表码 | 完整实际表与码对的存在唯一、准确类型/输入、六字段律 | 已验收 |
| S3.4c.1 | 实际码对、一般混合公式总唯一 | 无环境见证的首槽公式判断、全内部总唯一、准确输入/纤维双条件、11 端点和原核闭句 | 本批已验收 |
| S3.4c.2a | 固定原语法和编码实现 | 明确纯语言嵌入、源末槽/native 头槽映射、11 构造树与 Hilbert 规范码间的编码接口；逐条锁定待证对应，不能按名字认同编码 | 下一步 |
| S3.4c.2b | 上一接口和实际双表 binder | 原数值操作与本判断的对象对应；原 instantiate/abstract 全部构造及嵌套 binder 保护，不能只交付宿主 quote 等式 | 待完成 |
| S2.4/F2.4b.3 | 原 substituteFree/weakenFree 操作 | 原数值对应，以及规则 5/4 对任意内部码的检查兼容 | 待完成 |
| 5a | 原六规则、27 模式、完整 ZF/U 公理 | 专用 ProofZF/U 有限纯 AST；精确原标量/列表元数据，0 合法及域检查准确 | 待完成 |
| 5b | 内部语法操作及内部编译器 | 全内部 ω 码上的编译/检查正确性，覆盖完整 Separation/Collection | 待完成 |
| 6 | 内部解释、上述检查器和锁定 Con | 原 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

原库 ProofT.SyntaxEncode/SyntaxSubstitution 的 11 构造树使用 Variable.here=0 的列表头约定，但其签名是扩展 BasicSetTheory。
QuineEncoding.AbstractFreeTopFormulaCorrectness 使用 expression_encoding_theory、quote_hilbert 的六结构节点和 abstractFreeTopLast；不能将它直接当纯 nativeZF 中本批头槽操作的证明。
既有 SyntaxTransport 的源末槽到 native 头槽 AST 等式可作为编码接口的中间材料；最终对应仍须形成对象推导。
原 Con、原操作 quotation、任意内部证明码检查与相对一致性总门保持未完成。
