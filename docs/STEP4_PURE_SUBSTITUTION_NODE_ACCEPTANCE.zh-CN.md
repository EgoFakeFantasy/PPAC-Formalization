# 原替换节点投影、全部查询与完整有界纯关系式节点验收

基点：f23f9c7b0b6d779529e870c07da252860582e12f。单元3f.2c.3b.2d.3，14模块148项显式声明、19组闭句。

## 对象背景与最终目标

固定原YesMetaZFC纯等词／成员语言、完整Separation／Collection的nativeZF及原FirstOrder.Derives。最终主句仍是：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con继续覆盖全部内部ω证明码和原六规则／27模式。本批完成原固定替换描述符的纯关系式局部合同，不证明最终Con，也未证明共享扩展签名原条件的数值quotation／Bool对应。

## 直接引用原第2／3项查询

ProofSubstitutionProjectionSyntax.freeProjection与formulaProjection分别直接取原substitutionShape.queries[2／3].2；actual_free／actual_formula以rfl核对原种类和表达式：

```text
2: projection(v4,0,v2)
3: projection(v4,1,v5)
```

ProjectionExprQueryTyping.field_iff使用真实Expr图、真实行构造器和已验收七规则field双条件，取得原投影表达式与实际RawField数值关系的对象等价。运行值的自然性由实际表达式图推出，不由宿主计算或类型规格预言机给定。

free_query_iff在真实空集零值z处得到Q2↔RawField(w,env4,z,env2)。formula_query_iff在对象EX中实际取得并消去Num1的一值，得到：

```text
Q3 ↔ ∃one [Num1(one) ∧ RawField(w,env4,one,env5)].
```

两项合取与前驱元数据规格对象等价，前提只有Ω、六项自然赋值及空集零值；不预给投影查询或合法前驱。

对给定实际有限构造器，ProofSubstitutionProjectionSlots进一步证明两查询等价于env2／env5分别等于该构造器第0／1字段。这里arity／合法slot为外部有限模式索引，运行码和值全部在对象层量化；该条件式推论没有被当作任意前驱码已经合法。

## 全部五查询按原顺序合并

ProofSubstitutionAllQueries.bundle严格按原0／1／2／3／4顺序合并真实语法、参数列、两个投影及mode3变换查询。接受定义只使用原独立查询，不使用RawField、FormulaCode或FreeSubstProgram作为接受预言机。

bundle_iff把全部五项对象等价为：输入公式码合法、实际自由替换程序执行，以及两个原前驱字段读取条件。语法及程序前提全部在结论内部，最终只有Ω、自然赋值和空集零值。

## 全内部数值界与真实六赋值搜索界

PairingProjectionBounds证明裸配数／原始外壳分量不超过自然输入，包含实际补零分支。RawCodeProjectionBounds组合载荷及裸配数图，证明head／tail不超过输入。

RawCodeGetBounds以对象∀输入／∀输出的值界公式为矩阵，用原完整Separation与内部ω归纳消去索引IH，取得全部内部自然索引的get值界。RawCodeFieldBounds实际消去载荷EX，并以传递性组合载荷界与get界，得到：

```text
Ω(w) → x∈w → i∈w → RawField(w,x,i,y) → (y=x ∨ y∈x).
```

此合同不假定输入是合法证明码、规范Cons或任何给定有限构造器；内部ω不假定外部标准。

原substitutionShape的arity是6，head确为node5[v0,v1,v2,v3,v4]，是五字段头。前五赋值从真实原头表达式图取得界；只有env5不直接出现在头中。ProofSubstitutionBounds从真实第3查询得到env5≤env4，再由头中env4≤row传递到env5≤row，实际证明全部六项搜索界。head_constructor_iff另核对该头与真实原五字段构造器的双条件。

## 完整有界纯关系式局部节点

ProofSubstitutionNodeSyntax.node为真实对象六变量存在块：

```text
∃env0...env5 [env∈ω^6 ∧ env≤row ∧
  Graph(originalSubstitutionHead,env,row) ∧ AllFiveActualQueries(env)].
```

specification为同一六变量对象存在块，保留自然赋值、实际原头和上面的公式／替换程序／前驱元数据规格。反向需要的搜索界由上一节定理实际推导，不作为输入假设。

ProofSubstitutionNode.node_iff最终返回：

```text
Ω(w) → Empty(z) → [PureSubstitutionNode(w,row) ↔ SubstitutionSpecification(w,z,row)].
```

最终没有预给envNat、bounds、查询成立、输入类型、合法前驱或解码／轨迹见证。HornApplicationBounds.existsMany_congr把局部矩阵双条件逐原对象EX规则传过全部六绑定。该闭句经Source→TheoryTransport→ZFReplay进入原nativeZF推导核。

这是固定原描述符的完整纯关系式局部节点合同；它尚未与共享扩展签名原条件及其数值quotation／Bool判定建立对应。因此新增精确门禁标记纯关系式节点已证明，原完整共享检查器门禁仍保持false。

## 实际验收

1667构建任务、17885项审计（397无公理／17488允许依赖）、零警告；九命令及五trust=0入口全部退出0；1502份独立哈希一致、2040对精确证书足迹、15541项Internal显式声明覆盖

- scripts/verify.py完成全仓--wfail及五trust=0入口；148项新增声明全部列入Audit。
- 19组核心／native闭句证书保持精确既有依赖足迹；独立复核全部2040对证书。
- CheckStep4显式展开原arity=6、五字段head、第2／3查询的位置与种类、一般内部field值界，以及包含全部六EX的最终节点合同。
- 独立读回核查get界的原Separation／ω归纳、一般field界无合法前驱前提、全部搜索界从真实head／查询推导、节点最终只有Ω／空集零值两个前提。
- 接受定义守卫排除数值／类型／程序／宿主求值预言机；已有七规则接受AST、数值关系以及旧三查询／变换接受定义逐字节保持基点Git内容。
- 七锁文件和固定上游提交不变，上游工作树干净；新增代码无sorry／admit、占位公理、对象AC或Type层内部集合选择。

证据：verification/proof-substitution-node-readback.json、verification/summary.json、verification/commands.json、verification/build.log及verification/audit.log。生成器、探针与独立读回脚本留本地。提交后核对Git原始字节，并保留17份既存CRLF-only blob。

## 后续工程路线

| 单元 | 实现动作 | 必须交付的对象合同 | 状态 |
|---|---|---|---|
| 替换节点第2／3投影、五查询及搜索界 | 原固定Expr、真实数码、一般内部数值界 | 两查询／五查询／六赋值界，均不预给查询或合法前驱 | 本批验收 |
| 完整替换纯关系式节点 | 原五字段头、全部五查询、全部六有界存在赋值 | Ω／空集零值下完整节点双条件 | 本批验收 |
| 其余原证明模式与共享条件 | 原logical／theory／mp／forall／strengthening描述符及查询；数值quotation／Bool对应 | 各完整局部节点及固定内部条件对应 | 下一阶段 |
| 完整ProofZF/U | 原六规则／27模式、完整公理表、内部序列与编译 | 全内部证明码检查／编译正确性 | 待完成 |
| 内部解释与最终Con | 完整内部解释及锁定Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

没有把当前局部节点、编译成功或公理审计当作最终Con完成；目标保持active。
