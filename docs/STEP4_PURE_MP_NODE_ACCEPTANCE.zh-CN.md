# 原 MP 六查询与完整有界纯关系式节点验收

基点：fcb2673b4df679afeaa9b5bfb4484b6efb060b07。单元3f.2c.3b.2d.4，8模块131项显式声明、16组闭句。

## 对象合同

沿用固定 YesMetaZFC 的纯等词／成员语言、完整 Separation／Collection 的 nativeZF 和原 FirstOrder.Derives。内部 Con 仍对全部内部 ω 证明码量化，覆盖原六条证明规则、27个逻辑模式及完整 ZF 模式；不假定内部 ω 外部标准。最终目标仍未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批的终点是原固定 MP 描述符的完整纯关系式局部节点双条件，经 Source→TheoryTransport→ZFReplay 返回原 nativeZF。共享扩展签名条件、原数值 quotation／Bool 对应、完整 Proof／Con 继续待证。

## 原表与实际查询

ProofMPSyntax 的六个查询逐一直接取 mpShape.queries[0…5].2；actual_* 用 rfl 同时核查其原查询种类和 Expr：

| 索引 | 实际原查询 | 本批取得的对象对应 |
|---|---|---|
| 0 | formula(v0,v1) | FormulaCode(w,v1,z,v0) |
| 1 | formula(v0,v4) | FormulaCode(w,v4,z,v0) |
| 2 | projection(v2,0,v0) | RawField(w,v2,z,v0) |
| 3 | projection(v2,1,v4) | atOne(w,v2,v4) |
| 4 | projection(v3,0,v0) | RawField(w,v3,z,v0) |
| 5 | projection(v3,1,node7[v4,v1]) | 内部存在蕴含码 q，实际 constructor2tag7(w,[v4,v1],q) 且 atOne(w,v3,q) |

atOne 是内部 ∃one [Num1(one) ∧ RawField(w,p,one,y)]，实际取得并消去对象数码见证。通用 ProofProjectionExpr 直接读原投影 Expr，把实际输入／输出 Expr 图组合到已验收的原七规则 field 查询；不以宿主 Expr.eval 代替运行值。

第5项输出不是单个赋值变量。ProofMPQueries.implication_graph_iff 证明真实 node7 图与蕴含构造器的对象等价；rightImplication_iff 使用 SyntaxConstructors.exists_constructor 实际构造 q，再经原对象 exE 消去。双向均不预给解码结果或蕴含码见证。

ProofMPAllQueries.bundle 按原0…5顺序合并六项真实查询，接受定义不引用 FormulaCode、RawField、implicationRead 或其他比较规格。bundle_iff 在 Ω／五项自然赋值／空集零值下，等价于两个公式码合法性及四项前驱元数据读取条件。

## 全部五赋值界与完整节点

原 MP arity=5，实际头为 node2[v0,v1,v2,v3]，只有四个字段。前四赋值从真实头 Expr 图取得界。隐藏的 env4 由实际第3查询得 env4≤env2，再用 env2≤row 的传递性取界；没有假定左／右前驱是合法证明码。

ProofMPNodeSyntax.node 保留原五变量的有界对象存在块：

```text
∃env0…env4 [env∈ω^5 ∧ env≤row ∧
  Graph(originalMPHead,env,row) ∧ AllSixActualQueries(env)].
```

specification 是相同的五变量对象存在块，保留自然赋值、实际原头与上述两个公式／四投影规格。反向所需的全部搜索界由 ProofMPBounds.environment_bound 推导。ProofMPNode.node_iff 通过原五个 EX 规则传递矩阵双条件：

```text
Ω(w) → Empty(z) → [PureMPNode(w,row) ↔ MPSpecification(w,z,row)].
```

最终接口没有 envNat、bounds、给定查询、合法前驱、解码／轨迹见证或归纳假设。16组闭句覆盖六个实际查询、复合蕴含图、给定构造器推论、四投影、两公式、六查询、赋值界、四字段原头、完整矩阵和节点。

## 实际验收

1675构建任务、18016项审计（398无公理／17618允许依赖）、零警告；九命令及五trust=0入口全部退出0；1510份独立哈希一致、2056对精确证书足迹、15672项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail、九命令和五个 trust=0 入口实际退出0；131项新增声明全部纳入 Audit。
- 16组新增核心证书精确依赖三项标准公理；native 证书额外继承既定七个基础句子证书，未增加自定义公理。
- CheckStep4 核查原 arity=5、四字段头、六查询数量及第5项复合输出，并展开最终五个对象 EX 的原核合同。
- 独立读回检查最终前提集合、实际蕴含码构造／消去、隐藏赋值界来源和接受定义无比较预言机；已有替换节点及原查询引擎保持基点 Git 字节不变。
- 七份锁、YesMetaZFC 固定提交和上游干净状态不变。未改宿主选择数据、底座或退役反射代码。
- 首轮全仓验收在新增 CheckStep4 示例的 namespace 作用域处失败；修正后重新运行完整验收，以最终退出0的一轮为准。

机器证据：verification/proof-mp-node-readback.json、verification/summary.json、verification/commands.json。日志保留在 verification；本地工作脚本保留在 .local，不作为证明源码。

## 后续工程流程

| 单元 | 实现动作 | 必须通过的对象验收 | 当前状态 |
|---|---|---|---|
| 替换与 MP 节点 | 精确原查询、实际头、全部有界赋值 EX | Ω／空集零值下完整纯关系式节点双条件 | 已验收 |
| strengthening | 原两投影、succ自由界、mode0完整公式操作和全部四赋值 | 无合法前驱假设的完整局部节点双条件 | 下一批 |
| forall | 原嵌套量词头、投影、mode1完整公式操作 | 全内部候选的完整局部节点双条件 | 待完成 |
| logical／theory | 原27逻辑模式及完整 ZF／U 公理检查 | 不以不透明 logical／axiom 查询作为最终正确性 | 待完成 |
| 共享原条件 | 纯关系式合同与原扩展条件、quotation、Bool／Option | 实际定义间的对象推导 | 待完成 |
| 内部 Proof／编译 | 全内部证明序列、原六规则、完整公理及编译 | 任意内部码的 ProofZF／U 正确性 | 待完成 |
| 内部解释／Con | 逐公理解释与证明传输 | Derives nativeZF [] (Con_ZF→Con_target) | 未证明 |

旧通用 checker／最终 Con 门禁继续为 false；新增 MP 精确纯关系式门禁为 true。构建成功或本节点合同均不替代最终 Con 主句。
