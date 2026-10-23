# 纯参数列的闭轨迹合并与nil／cons局部步骤验收

基点：f6209428247174fc3c9723ae4f70a917eb0e19cd。完成3f.2c.3b.2b.1；7模块83项显式声明、10组闭句。

## 对象合同

对象语言为原YesMetaZFC单排序等词／成员语言，背景nativeZF保留完整Separation／Collection，正式推导关系为原FirstOrder.Derives。最终目标保持：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con涵盖全部内部ω证明码、原六规则／27模式。该主句仍未证明；本批不增加对象AC、标准ω、外部良基或新推导核。

## 已证明的对象步骤

BinaryUnionSyntax定义全成员双条件U=R∪S，由原Pairing和Union在对象存在量词内构造U。成员分类、两个包含关系和共同上界均为Source.Derives推导，没有宿主集合选择。

PureSyntaxTraceExtension复用实际Horn应用的单调性，对纯十五规则闭轨迹实际插入父行。PureSyntaxTraceMerge.two_conditions从两条原condition取得同一个包含两个根行的内部闭轨迹：

```text
Condition(w,r) → Condition(w,s) →
  ∃U (U⊆w ∧ ClosedPure15(w,U) ∧ r∈U ∧ s∈U).
```

该接口仅以前两条真实接受条件为前提；不预给公共轨迹。R、S和U均在对象存在量词内取得并消去。每个旧成员的规则应用经实际包含关系移到U，证明U闭合。

PureSyntaxNilRule.nil_iff比较原Expr.list []的实际图与纯Nil码，对任意内部候选成立。matrix_sound及application_sound恢复空长度、实际上下文和完整纯TermList；matrix_complete及application_complete按真实四字段构造原有界规则应用，搜索界由实际head变量界推出。

PureSyntaxNilComplete.checked_nil从Ω、Empty(k)、内部上下文和NilCode实际构造编码查询行及单点闭轨迹，得到完整PureSyntaxTrace.arguments查询。typed_nil_checked接已有TermList的nil分解。不假设宿主自然数长度或预给轨迹。

PureSyntaxConsRule精确保留原consRule.head及其头项／尾参数列两个前提。matrix_complete和application_complete使用实际表达式图、真实前提行成员关系及原有界赋值。condition_complete以前提两行的实际condition为输入，调用two_conditions取得公共闭轨迹，再实际插入父行，消去该公共轨迹。它仍要求Ω、内部自然赋值、长度后继、Cons码及三条实际行构造；不是任意列表的全查询等价定理。

ObjectPureSyntaxListSteps将上述十组闭句沿Source→TheoryTransport→ZFReplay返回原nativeZF。CheckStep4还直接展开轨迹合并和nil完整查询的闭句，以trust=0核对实际对象合同。

## 实际验收

1533构建任务、16606项审计（389无公理／16217允许依赖）、零警告；九命令及五trust=0入口全部退出0；1395份独立哈希一致、1876对精确证书足迹、14262项Internal显式声明覆盖。

- scripts/verify.py实际退出0；全仓--wfail和全部五trust=0入口通过。
- 83项新增声明显式列入Audit；十组kernel证书精确保持三项标准依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核核对了所有源哈希、所有证书对、展开原核合同及轨迹接口的实际前提。
- 七锁文件和YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变；上游工作树干净。
- 无新增sorry／admit或占位公理；原类型与执行关系定义不变。
- 编译期间修正了嵌套提升等式及Fin.cases赋值的展开方式。封装中先绑定明确类型的局部env，再应用原定理，未扩大推导前提或关闭检查。

证据：verification/pure-list-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另查Git原始字节，保留17份既存CRLF-only blob。

## 下一实现流程

| 顺序 | 具体实现 | 对象验收条件 | 状态 |
|---|---|---|---|
| 1 | 真实闭轨迹合并、插入 | 原Pairing／Union构造公共见证，保留十五规则闭合 | 完成 |
| 2 | nil完整查询与cons局部构造 | 实际规则赋值、搜索界、前提成员及父行接受 | 完成 |
| 3 | cons字段／前提恢复 | 由实际应用恢复子类型与尾参数查询，保留内部长度 | 待证明 |
| 4 | 全参数列表的成员归纳 | kind1查询↔TermList，消去IH与预给轨迹，涵盖非法候选 | 待证明 |
| 5 | 十一种公式构造与绑定后继 | kind4查询↔FormulaCode，全部内部码 | 待证明 |
| 6 | 原substitutionShape及数值操作 | 纯查询推出mode3守卫；quotation／Option／顶层mode1／2 | 待证明 |
| 7 | ProofZF／ProofU与内部解释 | 六规则／27模式、完整ZF模式、全内部证明码 | 待证明 |
| 8 | 最终Con推导 | 原nativeZF中的Con_ZF→Con_target | 待证明 |

cons查询健全性归纳、完整参数查询桥、公式桥、最终检查器适用性及内部Con验收门均保持false；总体目标保持active。
