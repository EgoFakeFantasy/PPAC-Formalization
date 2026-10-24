# 原逻辑0–19／22／26完整纯关系节点验收（2026-10-24）

本批完成不含变换查询的22个原逻辑模式：原准确arity、有序Bool查询表、全部赋值搜索界、嵌套数值头和完整对象存在赋值块。67组闭句沿既有传输返回原YesMetaZFC推导核。结合上一批20／23／25，目前27模式中25个具备完整纯关系节点对应；21／24、共享原quotation／Bool、理论节点、专用Proof、内部编译／解释及最终Con仍未完成。

## 背景、最终目标及验收层次

对象语言为纯等号／成员；背景为原nativeZF与完整Separation／Collection，不加入对象Choice。目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

内部Proof_T须覆盖原六规则／27逻辑模式、完整理论模式及全部内部ω证明码。当前节点对应覆盖任意内部赋值候选，外部模式号／参数个数是有限定理模式索引，不假定内部ω标准。局部纯关系checker与数值／类型规格的对象双条件，仍需后续共享quotation／Bool及内部Proof桥；本批不宣称已经证明完整Proof_T正确性或最终相对一致性。

## 原模式覆盖

| 原模式 | arity | 查询数 | 零绑定界查询类型 | 对象EX头部子码数 |
|---|---|---|---|---|
| 0 | 4 | 3 | Formula | 7 |
| 1 | 2 | 1 | Formula | 3 |
| 2 | 3 | 2 | Formula | 3 |
| 3 | 3 | 2 | Formula | 4 |
| 4 | 2 | 1 | Formula | 4 |
| 5 | 3 | 2 | Formula | 4 |
| 6 | 3 | 2 | Formula | 6 |
| 7 | 1 | 0 | Formula | 2 |
| 8 | 2 | 1 | Formula | 3 |
| 9 | 2 | 1 | Formula | 5 |
| 10 | 2 | 1 | Formula | 5 |
| 11 | 3 | 2 | Formula | 4 |
| 12 | 3 | 2 | Formula | 3 |
| 13 | 3 | 2 | Formula | 3 |
| 14 | 3 | 2 | Formula | 3 |
| 15 | 3 | 2 | Formula | 3 |
| 16 | 4 | 3 | Formula | 7 |
| 17 | 3 | 2 | Formula | 6 |
| 18 | 3 | 2 | Formula | 4 |
| 19 | 3 | 2 | Formula | 4 |
| 22 | 2 | 1 | Formula | 3 |
| 26 | 2 | 1 | Term | 2 |

规则7没有参数查询，但仍有表示自由界的赋值变量；其空列表合取为原truth，nullary头构造器及根变量界都已处理。规则22使用零绑定界公式查询，规则26使用零绑定界项查询。这里证明它们的局部接受／数值结构对应，并未据此跳过后续逻辑公理在内部证明解释中的正确性。

## 对象推导和实际表对应

LogicalStaticQueries从原grammar(isTerm,literal0,var0,var(i+1))取得准确表达式，并由已验收的原语法查询对应证明FormulaCode或Term规格，最终仅需Ω、赋值自然性与empty。任意固定有限查询的conjoin由原合取规则递归构造，包括零查询；bundle只含实际查询，类型条件单列于types，未把期望类型作为接受程序定义。

LogicalStaticQueryList直接解释实际原List(Bool×Expr)：false调用PureSyntaxExprQuery，true调用OriginalTransformExprQuery。通过有限列表归纳证明原List.finRange有序查询表与bundle相等。LogicalStaticPatterns逐个给出22个实际原模式的arity、查询列表、全部head变量覆盖及actual_list_bundle证书；这些rfl／decide证明核对的是固定源AST，所有码值仍在对象语言内。

22个LogicalRule*Head模块按实际树结构将Expr.node还原为SyntaxNodeSyntax.constructor。全部88个中间子码由对象存在性构造并消去；数值规格atValues不含Expr.graph、FormulaCode或待证头部断言。每个实际head的双条件均只需Ω和赋值自然性，包含常量、重复字段及nullary节点。

LogicalStaticNodeSyntax的独立接受式为赋值自然性、全部赋值界、实际head图和原查询bundle的合取，再由existsMany绑定完整arity。normalized使用实际数值头和独立类型规格。LogicalStaticNode从原head变量覆盖推出每个赋值界，通过原existsMany_congr处理完整赋值块。通用源证明接收数值头证书；ObjectLogicalStatic逐个实例化已经编译通过的实际head_iff及head_variables，最终原核闭句不留下这些源证明参数。

```text
对每个r∈{0,…,19,22,26}：
Ω(w), empty(z) ⊢ staticNode_r(w,row) ↔ numericSpecification_r(w,z,row)
```

最终闭句没有赋值自然性、输入类型、搜索界、head结构、数值子码、IH、Promise、模型或前驱证明有效性前提。对象empty与Ω条件保持明确。67组原核闭句包括22个完整节点、22组全部赋值界、22组嵌套数值头及1组通用有限查询规格；22个完整节点在CheckStep4中全部展开检验。

## 实际验收

| 验收项 | 实测结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 28／996／67组 |
| 定向完整native构建，含实际列表桥 | 1549项，通过、零警告 |
| 全仓构建 | 1852项，通过 |
| 声明审计 | 20602：417无公理、20185允许依赖；0警告 |
| 检查命令 | 9条退出0，含5个trust=0入口 |
| 独立工作区SHA256 | 1687份一致 |
| 全部core/native精确足迹 | 2335对一致 |
| Internal显式声明覆盖 | 18258项 |
| 上游与锁基线 | pin039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

新增core证书依赖恰为propext、Classical.choice、Quot.sound，native另含上游原有七项锁定证书依赖。仅逐个枚举本批67项native审计例外，未放宽命名空间或增加对象公理。此前全部PPAC证明及接受／类型／程序AST保持Git字节不变。

证据：verification/logical-static-readback.json、summary.json、commands.json、.local/logical-static-native-list-directed.log与logical-static-full-verify.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点6e252ed01490c7cfebd0a77b9fcf9a70d1eac9b8；本地提交及Git字节回读记录于accepted_commit。

## 清理与后续工程表

已确认本批定向编译全部终止，未发现失效工作区编译进程；无新增无用脚本或待删除垃圾。列表桥的失败诊断日志已由最终成功构建覆盖，保留实际生成、回读、验收证据和Lean缓存。清理核对后执行串行全仓验收，收据.local/workspace-cleanup-logical-static-result.json；未清理其他项目或应用。C盘空间已恢复，编译不再受原空间障碍阻止。

| 顺序 | 下一工作单元 | 对象层验收要求 |
|---|---|---|
| 1 | 剩余21／24逻辑节点 | 实际mode1 AbstractFreeTop，正确源／目标自由及绑定界，两条或一条真实变换；内部后继、Num1和码表见证消去，原准确head／查询／全部赋值界 |
| 2 | 原共享quotation／Bool与理论节点 | 语言、上下文、参数及数值编码准确；完整ZF/U理论模式，不局限外部标准码或有限重放 |
| 3 | 专用内部Proof与检查正确性 | 原六规则／27逻辑模式、完整Separation／Collection、全部内部ω证明码；保持原接受定义 |
| 4 | 内部编译、源推导传输及数学解释 | 核内证书转换与检查／编译正确性，ZF+PP+ACwo+¬AC实际内部解释 |
| 5 | 最终内部Con蕴含 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，仍未证明 |

Agent广场状态和经验只在API成功返回后才算同步；服务不可用不影响本地证明验收。不恢复已退役反射实现。
