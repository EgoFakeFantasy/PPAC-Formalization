# 否定及两量词的原规则与内部绑定后继验收

基点：57b971c9fdce240daa8a8de79c2274a1b6e6aa2b。单元3f.2c.3b.2c.3b，4模块47项显式声明、7组闭句。

## 对象合同

固定原YesMetaZFC等词／成员语言、完整Separation／Collection背景nativeZF和原FirstOrder.Derives。最终对象主句仍是：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con覆盖全部内部ω证明码和原六规则／27模式。本批不证明主句，不增加对象选择、标准ω、外部良基或新核。

统一IH仍为实际对象公式：

```text
correct(w,n) := ∀b ∀f (PureFormulaQuery(w,b,f,n) ↔ FormulaCode(w,n,b,f))
allIH(w,n) := ∀x (x∈n → correct(w,x)).
```

## 实现

PureSyntaxUnarySyntax固定三条原规则：tag4／advance=false（否定）、tag9／advance=true（全称）、tag10／advance=true（存在）。Fin3仅索引这三条外部模式，运行码、上下文、闭轨迹仍为内部集合。actual_head及actual_premises由rfl核对原规则。

boundExpr false是var0；boundExpr true是succ(var0)。step_from_premise通过实际表达式存在定理在对象EX中取得量词绑定界，恢复Successor(B,b)，在实际严格子码与实际B／f上下文实例化统一IH，构造原advancedCode。没有用宿主Nat的加一模拟内部界。

PureSyntaxUnaryRule的matrix_sound／application_sound从实际原应用恢复字段，用原构造的child_member证明严格子码关系，再实例化上述对象IH；不预给父FormulaCode。matrix_complete／application_complete从实际父／子行、绑定界图和轨迹成员构造完整原有界规则应用，界来自原head变量。

PureSyntaxUnaryComplete.condition_from_row消去子闭轨迹见证并实际插入父行；from_row在对象EX中取得父编码行。checked_from_child进一步消去子行和父行；其输入明确保留子FormulaCode、真实子查询和实际绑定图。

checked_from_step处理原stepCheck：否定保持绑定界；量词消去advancedCode中的实际后继值B，在B／f处取得子查询，构造succ图并返回父查询。最终typed_unary_checked使用原已知构造类型双条件得到此stepCheck，闭句合同为：

```text
Ω(w) → allIH(w,n) → FormulaCode(w,n,b,f) → SingleCode(tag(kind),w,x,n) →
  PureFormulaQuery(w,b,f,n).
```

该合同明确保留IH。ObjectPureSyntaxUnary提供七组source／kernel_certificate／native闭句；CheckStep4同时展开此合同并检查确切原head及前提，未把闭句回放包装当作主Con证明。

## 实际验收

1566构建任务、16947项审计（392无公理／16555允许依赖）、零警告；九命令及五trust=0入口全部退出0；1428份独立哈希一致、1921对精确证书足迹、14603项Internal显式声明覆盖。

- scripts/verify.py退出0，全仓--wfail及五trust=0入口实际通过。
- 新增47项声明全部显式列入Audit；七组核心证书精确保持标准三项依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核全部哈希、全部1921对证书、实际接口前提、内部EX后继和父轨迹构造，并确认最终IH／数值检查器／Proof／Con门仍为false。
- 七锁文件、YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6、原纯接受定义及十五规则表未改；上游工作树干净。
- 新增源码无sorry／admit、占位公理或宿主选择数据抽取；有限规则分类不假定Rule可判定相等。

证据：verification/pure-unary-readback.json、verification/summary.json、verification/commands.json、verification/build.log及verification/audit.log。验证材料和生成探针保留本地；提交后另核对Git原始字节及17份既存CRLF-only blob。

## 下一步与未完成范围

下一单元为完整十五规则分派、十一公式构造合并以及原ZF集合归纳。完成后应得到只有Ω前提的全内部公式查询双条件，再处理原数值quotation与实际检查器调用。完整ProofZF/U检查和编译、内部解释及最终内部Con仍未完成。
