# 实际完整程序与根执行方程验收

基点：ea058dcafd63c1cb57fde261f3ef40b9c3d25a88。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.3a.1。原 Run₃ 的十一情况汇总尚未完成；本批只完成真实完整程序与根 executed 的连接。

## 对象合同

使用 YesMetaZFC 原纯等词／成员语言、原 nativeZF（完整 Collection）及原 FirstOrder.Derives。最终目标仍为 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 覆盖全部内部 ω 证明码、原六规则／27模式及完整 Separation／Collection。未增加对象 AC、标准 ω、外部良基或新推导核。

## 实际证明

FormulaTransformRootStep.recursive_target_type 在内部 Ω、合法输入和任一递归 Cases 成立时推出目标 FormulaCode。源 Cases 的全部十一分支分别调用已有对象类型定理，再通过原析取消去汇总；没有预先假定目标合法。

program_target_type 把真实完整程序转换到递归 Cases；使用 FormulaTransformRecursionCorrectness.graph_iff 将实际递归图传到原递归图，再以 LocalTransfer.all_iff 消去历史参数。所有历史字段与候选输出仍为任意内部对象。

execution_iff_guarded_step 在内部 Ω、根序数和实际递归图下取得：

```text
executed(w,R,S,a,b,c,d,n,q)
  ↔ n∈ω ∧ (legal(w,R,S,a,b,c,d,q) ∧ step(w,R,S,a,b,c,d,h,n,q)).
```

legal 是实际项像表合法性与目标 FormulaCode 的合取。这里显式保留它，因为原 recursive_iff 的 criterion 本来包含该守卫。

execution_iff_step 从合法输入得到根自然数和合法项像表，由实际程序的目标类型定理推出 legal，消去上述守卫。execution_iff_program 再从输入提取源 FormulaCode，得到：

```text
Ω(w) → Input(w,R,S,a,b,c,d,n) → ActualGraph(w,h,n) →
  (executed(w,R,S,a,b,c,d,n,q)
    ↔ run(formulaProgram,w,R,S,a,b,c,d,h,n,q)).
```

这两条定理不要求原运行的统一归纳前提；尚未证明的是原 Run₃ 与该完整程序在所有内部源公式上的对应。

ObjectFormulaTransformRootStep 提供五组闭句的实际 Source.ZF 推导、sourceZF 核证书及 nativeZF 原核重放。所有 w、n、q、像表及上下文界通过对象全称闭包量化，未通过宿主层选取历史或输出见证。

## 实际验收

1507构建任务、16321项审计（385无公理／15936允许依赖）、零警告；九命令及五trust=0入口全部退出0；1371份独立哈希一致、1840对精确证书足迹、13977项Internal显式声明覆盖。

- 全仓 --wfail 构建及五个 --trust=0 入口实际退出0。
- 新增25项声明均显式列入 Audit，五组核心证书只依赖标准三项，native证书为标准三项加固定原七项依赖。
- 七份锁文件与 YesMetaZFC 固定提交039c8e132cc19671d73a3933c66b4799d2599dd6均未改变；上游工作树干净。
- 无新增 sorry／admit／占位公理。Choice桥仍隔离，未扩大本批依赖。
- 逐源码哈希、累计证书精确足迹及全部Internal显式声明覆盖均复核。

独立证据：verification/root-step-readback.json；完整入口：verification/commands.json；构建／审计：verification/build.log、verification/audit.log。提交后另复核Git原始字节：保留17份既存CRLF-only blob，所有本批文件字节须与Git提交完全一致。

## 下一工程流程

| 顺序 | 实现任务 | 必须通过的验收 |
|---|---|---|
| 1 | 原Run₃的原子、否定、四个二元及两个量词情况接到同一完整程序 | 在真实frame、源FormulaCode、实际图和统一内部IH下的全十一情况双条件 |
| 2 | 以全参数correct公式进行原核内部成员归纳 | 消去allFramesIH，保留全部内部ω根码和候选输出 |
| 3 | 验证模式3自由变量像合同适用于实际原证明检查器 | 对六规则／27模式的实际所有使用点给出对象证明 |
| 4 | 完成数值quotation、Option及ProofZF/U | 全部内部证明码双向检查，不以外部标准码替代 |
| 5 | 对象理论内部解释与一致性传输 | 原nativeZF的Derives [] (Con_ZF → Con_target) |

原十一情况装配和内部归纳尚未完成。本批不是最终内部Con定理，也不构成最终迁移已完成的声明。
