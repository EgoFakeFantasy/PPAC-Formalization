# 原12分支带局部检查闭轨迹方程验收（2026-10-24）

本批直接采用原ObjectProofTree.rules的12分支，建立带局部检查的纯关系闭轨迹。原ZF分离公理构造全部轨迹根的实际集合，并证明闭合性；最终轨迹方程在对象EX中构造并消去该集合见证。全部12分支的赋值界与正向组合、node0[code]和root1[code,conclusion]入口展开均已有原核闭句。

这证明的是闭轨迹展开方程及组合，不是秩归纳后的完整检查器正确性。根关闭性、实际Bool桥、ZF/U专用公理测试、内部Proof／编译／数学解释及最终Con仍未完成。test : Formula 1继续是显式对象公式参数，没有假定其识别ZF/U。

## 背景及最终目标

对象语言保持纯等号／成员；背景为原nativeZF与完整Separation／Collection，不增加对象Choice。最终要求仍为：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

专用Proof_T须覆盖原六规则／27模式、完整理论模式与全部内部ω码。当前轨迹允许任意内部ω子集，不假设外部有限、标准ω或有效前驱证明。外部有限分支索引与对象码严格区分。

## 实际12分支与行处局部检查

ProofAllTableRenaming证明全部五Kind查询及准确六类局部表的捕获规避重命名。ProofTreeRowLocalSyntax以真实PairingProjectionSyntax.step(true,true)取得裸tag；tag为empty时，用真实field0查询取payload并调用准确六类局部表。非零tag分支保留原条件蕴含结构。没有以“行有效”或期望执行结果定义接受条件；其与原共享Bool函数的最终对应仍须后续证明。

原ObjectProofTree.rules有12分支，6种形状各有node／root两种入口。payload arity及子证明位置均有rfl证书：

| 原形状 | payload arity | children |
|---|---|---|
| logical | 3 | 空 |
| theory | 3 | 空 |
| MP | 4 | 2、3 |
| forall | 3 | 2 |
| strengthening | 3 | 2 |
| substitution | 5 | 4 |

局部节点检查的arity [3,3,5,4,4,6]包含辅助公式码，不能用于替换本表payload。根守卫仍按原Rule.guards解释为严格小于；var0<literal1表示free=0，本批没有把它误写为free=1，也没有跳过后续根关闭性推导。

## 闭轨迹、实际分离集合与展开

ProofTreeTraceSyntax的接受条件独立定义为：

```text
Step(test,w,r,R) = 原12规则的一步应用(w,r,R) ∧ RowLocal(test,w,r)
Closed(test,w,R) = ∀r∈R. Step(test,w,r,R)
Trace(test,w,r) = ∃R. R⊆w ∧ r∈R ∧ Closed(test,w,R)
```

接受式不引用递归方程、秩正确性或Proof有效性结论。ProofTreeTraceMonotone由原规则对前提成员的正向依赖证明轨迹单调，并保持每行实际局部检查。ProofTreeTraceExtension用原Pairing／Union实际插入根行，在对象推导内取得新闭轨迹，不抽取宿主Type中的轨迹函数。

ProofTreeUniversalSyntax／Value使用完整原Separation构造V={r∈w | Trace(test,w,r)}。任意内部闭轨迹R的每个成员都由同一个R作见证进入V，因此R⊆V。ProofTreeUniversalClosed再用单调性把每个真实一步应用传到V，证明V本身闭合；这些证明没有把“V已闭合”留作未证合同。

ProofTreeTracedStep逐个保留实际原Rule的完整arity、全部赋值界、原guards和原premises；每个递归前提改写为实际Expr行码EX与其自身Trace。与V中的真实成员关系的双条件，经完整existsMany赋值块和原12规则析取组合。ProofTreeTraceEquation最后构造并消去V，得到：

```text
Trace(test,w,r) ↔ r∈w ∧
  (原12分支的真实有界赋值、头、守卫及各子行Trace) ∧ RowLocal(test,w,r)
```

最终闭句没有轨迹集合V、输入自然性、IH、模型、局部测试正确性或外部有限证明前提；自然域r∈w在结论中明确保留。即使此方程没有额外对象前提，它也仅陈述闭轨迹的展开，尚未证明由原秩下降归纳取得完整Bool／证明树可靠性。

ProofTreeBranchConstruction对原12分支从实际头变量覆盖推导全部赋值界，由头图推出根行自然性，再用原guards、真实子行Trace与行处局部条件构造父行Trace；不存在额外轨迹见证或有效前驱证明假设。

## 节点与根入口

ProofTreeEntrySyntax的node入口是实际数值node0[code]行加Trace；root入口是实际root1[code,conclusion]行加Trace。两者在原EX／conj规则下取得对应展开方程，所有实际内部code与候选conclusion都在范围内。尚未从12分支的原守卫、投影与秩下降推出最终关闭根规格或专用Proof_T正确性，验收门明确保持false。

ObjectProofTreeTrace提供10组源／core／native闭句，沿既有TheoryTransport.sentence和ZFReplay.replay返回原FirstOrder.Derives；CheckStep4包含展开后的无轨迹见证方程和实际根入口契约。

## 实际验收

| 验收项 | 实测结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 13／122／10组 |
| 定向完整native构建 | 1703项，通过、零警告 |
| 全仓构建 | 1904项，通过 |
| 声明审计 | 21133：422无公理、20711允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 独立工作区SHA256 | 1730份一致 |
| 全部core/native精确足迹 | 2376对一致 |
| Internal显式声明覆盖 | 18789项 |
| 上游与锁基线 | pin039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core依赖恰为propext、Classical.choice、Quot.sound，native另含上游原七项锁定证书依赖。新10项native逐个枚举，没有扩展信任锁或对象理论；此前全部PPAC证明及接受／程序AST保持Git字节一致。本批首次导入原ProofTree所需的既有上游模块，原上游源码与pin未改动。

证据：verification/proof-tree-readback.json、summary.json、commands.json，.local/proof-tree-equation-directed.log、proof-tree-native-directed.log与proof-tree-full-verify.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点fbd264fe1deada7e60d55267c5f2b6ead9dfc735；提交后accepted_commit由独立Git字节回读写入本地验收JSON。

## 清理与继续流程

定向编译终止后确认无失效工作区Lean／Lake进程；删除2份被成功构建替代的失败诊断日志，共5202逻辑字节，盘面实测增加8192字节，然后执行串行全仓验收。收据.local/workspace-cleanup-proof-tree-result.json。保留有用生成／回读脚本、成功证据、正式源码和编译缓存，未清理其他项目或应用。

| 顺序 | 下一实现工作 | 对象层验收边界 |
|---|---|---|
| 1 | 原根关闭性及节点／根精确方程 | 用真实数值头、tag／field唯一性与guards排除错误分支，推出free=0、结论一致和完整子节点条件；不预设有效根 |
| 2 | 秩下降与内部可靠性归纳 | 对全部内部码证明原2*payload+phase或等价双层归纳，连接真实递归／拒绝行为；闭轨迹方程不替代此步 |
| 3 | ZF/U实际公理测试及共享Bool桥 | 完整Separation／Collection等理论模式，明确实例化Formula1参数；核查纯EqMem／扩展签名与上下文的准确对应 |
| 4 | 专用Proof与内部编译／数学解释 | 原六规则／27模式及全部内部ω，证书转换／源推导传输，目标ZF+PP+ACwo+¬AC实际解释 |
| 5 | 最终内部Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，仍未证明 |

不把编译成功、任意对象测试的参数化结果或模型语义作为最终Con交付。不恢复已退役反射实现。Agent广场同步只在API成功回执后计为完成，不直接修改其JSONL数据。
