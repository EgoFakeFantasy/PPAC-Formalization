# 逻辑节点、对象理论测试接口及参数化六规则局部表验收（2026-10-24）

本批完成原logicalShape的完整对象节点，将其实际逻辑查询接入已验收27模式表；同时完成theoryShape的对象一元公理测试接口，保留test : Formula 1这一显式外部模式索引。随后直接读取原ObjectProofNode.shapes，逐项传输全部六类局部节点，得到参数化准确原局部表与独立规格的原核双条件。

这里没有实例化ZF/U专用公理测试，没有证明整棵证明树的递归有效性或实际Bool接口，也没有完成内部Proof、编译／数学解释和最终Con。六类局部表的参数化结构正确性不替代这些目标。

## 背景与最终目标

对象语言仍为纯等号／成员；背景为原nativeZF与完整Separation／Collection，不添加对象Choice。目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

Proof_T须覆盖完整理论模式、六规则／27模式以及全部内部ω证明码。当前结果属于对象推导核中的局部接受式传输；test是对象公式AST，既不是宿主Nat→Bool谓词，也不是“测试正确”或“公理可证”的未证假设。外部模式索引不被误写为内部统一真值断言。

## 逻辑节点与准确字段换位

原logicalShape的arity为3，头部为node0[free,formula,axiomCode]，唯一.logical查询为node0[free,axiomCode,formula]。ProofLogicalSyntax保留原查询及字段换位的rfl证书，接受bundle只引用OriginalLogicalExprQuery。

LogicalTableRenaming证明实际27模式表在捕获规避重命名下交换，包含原有序Bool列表、完整赋值EX和析取。OriginalLogicalExprQuery用对象EX取得实际查询行码，接受条件直接是LogicalOriginalNodeSyntax.table，未把数值／类型规格嵌入接受程序。query_constructor_iff把实际Expr查询双向变成数值三字段构造器加原表；ProofLogicalQueries再在原ex／conj规则下使用已证明的全27表双条件。

ProofLogicalNode的全部三赋值界由实际头的变量覆盖推出；两种字段次序分别用于证明头和逻辑查询行。完整existsMany 3规范化端点只有Ω(w)、empty(z)前提，没有输入类型、搜索界、head、查询行码、前驱有效性或模型假设。查询行码作为内部EX见证处理，没有抽取宿主Type数据。

## 理论节点的显式对象测试接口

AxiomTestSyntax.holds(test,row)把一元对象公式的唯一自由变量赋为row，并证明重命名交换。OriginalAxiomExprQuery保留实际Expr行码EX与holds(test,row)，在对象推导中传输到真实数值行构造器。整个接口没有假定holds成立；同一个test同时出现在接受端和规格端。

原theoryShape的头为node1[free,formula,axiomCode]，查询依次为Formula(0,free,formula)与.axiom的node0[axiomCode,formula]。ProofTheoryQueries由原语法查询推出FormulaCode，并处理准确二字段公理行；全部三赋值界仍由实际头推出。最终规范式包含公式类型、数值头与显式对象测试。接口对任意固定test : Formula 1给出对象证明，但没有声称该test已经识别完整ZF/U公理。

实际专用ZF/U测试还必须构造完整Separation／Collection等模式的内部编码识别与正确性，随后才能用于所需Proof_ZF/U。当前保留其未完成门，不能把参数化接口当作完整理论公理测试。

## 原六类局部表的逐项组合

| 原Shape顺序 | 局部赋值arity | 有序查询数 |
|---|---|---|
| logical | 3 | 1 |
| theory | 3 | 2 |
| MP | 5 | 6 |
| forall | 4 | 4 |
| strengthening | 4 | 4 |
| substitution | 6 | 5 |

ProofAllQuerySyntax按原五种Kind分别分派projection、syntax、transform、logical、axiom查询；axiom分支明确使用对象test参数。ProofAllQueryBundles证明每个实际原有序查询列表与既有接受bundle双条件，使用原合取规则消去末尾truth，不改写查询顺序或关联。

ProofAllNodeSyntax直接读取shape.arity、head、queries，对实际全部赋值作自然性、搜索界、头部图及列表查询检查，再按原六Shape表析取。接受定义不引用数学规格。ProofAllNodes分别处理六个完整存在赋值块，连接此前MP、forall、strengthening和substitution的对象规格，最后组合：

```text
对每个固定对象一元公式test：
Ω(w), empty(z) ⊢ ExactSixLocalTable(test,w,row)
                  ↔ IndependentLocalSpecification(test,w,z,row)
```

原表传输不要求调用方提供查询正确性、类型或合法前驱假设。这里仍只是局部节点表；递归子证明检查及根结论连接属于下一层，不能因本式通过而认定p是有效完整证明。

## 实际验收

| 验收项 | 实测结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 17／152／16组 |
| 定向完整native构建 | 1682项，通过、零警告 |
| 全仓构建 | 1882项，通过 |
| 声明审计 | 21011：421无公理、20590允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立工作区SHA256 | 1717份一致 |
| 全部core/native精确足迹 | 2366对一致 |
| Internal显式声明覆盖 | 18667项 |
| 上游与锁基线 | pin039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core证书依赖恰为propext、Classical.choice、Quot.sound，native另含上游原有七项锁定证书依赖。新16项native均逐名枚举，没有新增对象公理、命名空间通配放行或信任锁变更。此前PPAC证明、接受／类型／程序AST均保持Git字节不变。

扫描器修正了原枚举构造子Kind.axiom与axiom声明的词法区分：带点的构造子不再被当成新公理声明；裸axiom／protected axiom、sorry／admit／unsafe／native_decide仍被拒绝。独立回读同时核对该区分、实际声明足迹和原锁定基线。

证据：verification/proof-base-readback.json、summary.json、commands.json，.local/proof-base-native-directed.log及proof-base-full-verify.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点1a22b1a43a28d45352650fd310b218066b4d07ea；提交后accepted_commit由独立Git字节回读写入本地验收JSON。

## 清理与后续实现流程

清理前确认无失效工作区编译进程；删除一份被成功构建替代的失败诊断日志1445逻辑字节，盘面实测增加4096字节，然后恢复串行全仓编译。收据.local/workspace-cleanup-proof-base-result.json；保留有用生成／回读脚本、成功证据、正式源码和Lean缓存，未清理其他项目或应用。

| 顺序 | 实现单元 | 必须证明的对象端点 |
|---|---|---|
| 1 | 原ObjectProofTree的12分支递归外壳 | 区分局部测试辅助赋值与payload字段；处理真实子证明位置、全部内部轨迹与根结论连接，不能以局部表代替递归有效性 |
| 2 | 完整ZF/U专用对象公理测试 | 实际内部模式编码及成员正确性，完整Separation／Collection，明确实例化当前Formula1接口 |
| 3 | 共享扩展quotation／实际Bool与专用Proof | 核查语言、上下文和参数，对全部内部码证明检查对应；保留原六规则／27模式和精确非法候选处理 |
| 4 | 内部检查／编译与数学解释 | 原核内证书转换／源推导传输，目标ZF+PP+ACwo+¬AC实际内部解释 |
| 5 | 最终Con蕴含 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，仍未证明 |

下一层需注意：原ProofTree payload arity为[3,3,4,3,3,5]，与本地节点检查arity [3,3,5,4,4,6]不同，后者含辅助公式码。原根守卫(var0,literal1)是严格小于，表示free=0；不可误读成free=1。上游ObjectProofTreeSpec.root_iff已明确这两点，迁移时须给出对应对象推导。

Agent广场状态和经验仅在API成功返回后算同步；不得直接修改其JSONL数据。不恢复已退役反射实现，不以宿主一致性或模型语义替代最后原核推导。
