# 原七规则投影的get／field全内部数值双条件验收

基点：c42b727c8627cd88affc3ef07f695223b9a3099a。单元3f.2c.3b.2d.2c.2b，13模块175项显式声明、24组闭句。

## 固定对象背景与最终目标

仍使用原YesMetaZFC纯等词／成员语言、完整Separation／Collection的nativeZF及原FirstOrder.Derives。最终目标保持：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con仍覆盖全部内部ω证明码和原六规则／27模式。本批完成原七条固定投影描述符的独立纯轨迹数值桥，未完成内部Con主句，也未完成共享扩展签名检查器的数值quotation／Bool／Option对应。

## 最终对象合同

RawTag、RawGet、RawField分别缩写既有PairingProjectionSyntax.step true true、RawCodeGetSyntax.get、RawCodeFieldSyntax.field。每个运行码和候选值均为对象变量：

```text
Ω(w) → [TagQuery(w,x,y) ↔ (x∈w ∧ RawTag(w,x,y))]
Ω(w) → [GetQuery(w,x,i,y) ↔ (x∈w ∧ i∈w ∧ RawGet(w,x,i,y))]
Ω(w) → [FieldQuery(w,x,i,y) ↔ (x∈w ∧ i∈w ∧ RawField(w,x,i,y))]
```

三个合同联合为一份原nativeZF闭句证书。get／field最终前提只有Ω，没有IH、输入合法性、输出自然性、标准索引或外部给定轨迹／解码见证。输入及索引的自然域位于对象结论中，覆盖全部内部候选，保留零码和任意非规范自然外壳。内部ω不假定外部标准。

## 真实子前提与原始外壳

ProjectionTracePremises证明：在原Separation实际构造的全部根集合V处，HornRuleSyntax.premise的成员条件与独立七规则Expr查询双向对应；任意原变量三字段get子表达式再对应实际GetQuery。

ProjectionRawPairExpr对任意内部原始标签和裸配数载荷构造真实Expr图，取得实际head／tail数值；配数值存在见证在对象EX内取得和消去。没有改用规范Cons标签，也没有调用宿主ObjectCodeProjection／Expr.eval。

ProjectionGetConstructors直接取原getZero／getHead／getTail头与前提，构造自然赋值、有界应用及真实父查询；tail分支要求真实GetQuery子查询。根行和赋值存在块由原接口构造并消去。

## 全内部get归纳

ProjectionGetZeroIndex在空索引处完整消去三条原规则：零输入／头规则给出原数值关系，尾规则的实际后继索引与空索引矛盾。反向对零／正输入分类，正输入的标签、载荷和裸配数两分量四个见证全部在对象EX内构造并消去。

ProjectionGetInductionSyntax.correct(w,i)为对象公式：

```text
∀x ∀y [GetQuery(w,x,i,y) ↔ (x∈w ∧ RawGet(w,x,i,y))].
```

ProjectionGetSuccessorSound从真实V的一步展开消去getTail原赋值块与子前提，用共同后继的前驱唯一性将原规则的前驱对齐归纳索引，再实例化correct。这里使用V的真实成员／闭轨迹，不把ω成员关系当作子查询接受性。

ProjectionGetSuccessor的反向取得原节点／裸配数四个内部解码见证，用原get后继方程退回尾／前驱；correct的反向构造真实子查询，再由原getTail构造父查询。correct_successor实际返回全输入／全输出的对象ALL公式。

ProjectionGetInduction使用完整Separation对上述correct矩阵实例化原OmegaInduction.induction_on_omega，得到∀i∈ω correct(w,i)。at_index、checked_sound、checked_complete和checked_iff的最终接口均已消去IH。输出唯一性由真实数值get函数性得到，索引自然性从查询本身推出。

## 完整field

ProjectionFieldConstructors直接构造原fieldZero／fieldPositive查询。正码使用真实get子查询，索引与输出自然性由该子查询推出。

ProjectionFieldCases实际消去原arity=1／4赋值块，从真实V取出get子查询，使用完整get定理转为数值关系；实际字段等词对齐输入／索引／输出。ProjectionField反向消去实际标签／载荷两个解码见证，由既有RawField↔载荷后RawGet方程及完整get定理构造子查询，再构造父field查询。

最终field双条件不保留get正确性假设或共同轨迹见证。独立七规则接受定义、原数值关系定义及原表均未修改。

## 实际验收

1653构建任务、17737项审计（395无公理／17342允许依赖）、零警告；九命令及五trust=0入口全部退出0；1488份独立哈希一致、2021对精确证书足迹、15393项Internal显式声明覆盖

- scripts/verify.py完成全仓--wfail与五trust=0入口；175项新增声明全部列入Audit。
- 24组闭句经Source→TheoryTransport→ZFReplay返回原nativeZF；独立读回逐对核查全部核心／native证书精确足迹。
- CheckStep4显式展开只有Ω前提的get和field全候选双条件、内部ALL索引正确性，防止仅通过一个命名包装掩盖残留IH。
- 独立复核原ω归纳确实使用correct矩阵的完整Separation，后继可靠性确实从真实V取子查询并使用前驱唯一性，正向／反向真实行、赋值与解码见证均对象构造和消去。
- 六份执行接受AST／数值关系源码与基点Git blob逐字节一致；原接受定义未引入correct／类型／宿主求值预言机。七锁文件及固定上游提交不变，上游工作树干净。
- 新增代码无sorry／admit、占位公理或Type层内部集合选择，未增加对象AC或新推导核。

证据：verification/projection-get-field-readback.json、verification/summary.json、verification/commands.json、verification/build.log与verification/audit.log。生成器、探针和读回脚本留本地。提交后核查Git字节并保留17份既存CRLF-only blob。

## 接下来的最终目标路线

| 单元 | 输入与动作 | 必须交付的对象合同 | 状态 |
|---|---|---|---|
| 原七规则数值桥 | 原固定七规则、真实根集合、原数值方程、内部ω归纳 | 全候选tag／get／field双条件，保留自然域、消去全部IH | 本批验收 |
| 原替换节点投影 | substitutionShape第2／3项固定Expr查询、前驱实际有限构造器槽位 | 两项真实投影查询的数值等价；不得预给查询成立 | 下一步 |
| 完整替换节点 | 已证第0／1／4项、两项投影、实际head及有界赋值存在块 | 五查询与完整局部节点双条件 | 待完成 |
| 原完整ProofZF/U | 原六规则／27模式、完整公理表、内部证明序列／编译、quotation／Bool／Option对应 | 全内部证明码检查及编译正确性 | 待完成 |
| 内部解释／最终Con | 完整内部解释及锁定内部Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

本批true门禁仅指原固定七规则的独立纯关系式轨迹到数值规格的桥。原共享扩展签名条件的quotation、实际证明节点查询、完整ProofZF/U、内部解释及最终Con门禁仍为false。
