# 空绑定界参数与原模式3整条公式运行验收

基点：a79cdc4c36a66241e63953243c721c1bbbf8d87b。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.3b.1：纯成员语言的实际替换输入合同与不带预给码表的原mode3全公式接口。

## 原对象目标

保持原 YesMetaZFC 等词／成员语言、原 nativeZF 的完整 Separation／Collection，以及原 FirstOrder.Derives。最终目标仍是 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 必须涵盖全部内部 ω 证明码、原六规则／27模式和完整公理模式。本批没有完成该目标；未增加对象 AC、标准 ω、外部良基或新核。

## 对象证明

EmptyBoundFreeInputs.term_free 由空绑定界排除 bound 分支。纯成员签名没有函数符号，因此任意内部合法项必须落在 free 分支；该推导使用原对象析取消去和 empty 关系。

values_free、graph_free 将实际混合项像图转换为自由变量项图；values_mixed、graph_mixed 给出反向转换。list_free、list_mixed 在对象存在量词内构造／消去真实列表解码图，取得精确双条件：

```text
Ω(w) → Empty(z) →
  (MixedTermList(w,a,z,c,L) ↔ FreeVariableTermList(w,a,c,L)).
```

conversion_exists 对每个内部合法空绑定界列表实际取得索引转换码 J；不要求宿主层给出解码函数或把内部长度当成标准数。

OriginalFreeSubstFormulaRun.at_codes_iff 用上一批的全公式原运行正确性、真实索引重命名程序和原自由替换关系连接得到运行双条件。from_list_iff 在原对象存在量词内依次取得恒等码 I、自由索引码 J 及绑定项像码 R，然后消去全部见证。最终接口 program_iff 只有 Ω、模式数码3、实际元数据、源 FormulaCode 和原自由变量项列表五个前提。

empty_bound_arguments_iff 直接从纯成员语言空绑定界参数列表推出：

```text
Ω(w) → Num3(mode) → Metadata(w,depth,L) → FormulaCode(w,n,b,a) →
  Empty(z) → MixedTermList(w,a,z,c,L) →
    (OriginalRun₃(w,mode,depth,L,n,q) ↔ FreeSubstProgram(w,b,a,c,L,n,q)).
```

所有对象变量均通过 close 全称闭合。这里没有预给 frame、identityCode、codeConversion、项像表、实际历史或 IH 前提。CheckStep4 直接展开上述闭句检查 nativeZF 原核推导类型。

output_type、unique 和 actual_output 分别取得准确目标 FormulaCode、任意两原运行候选相等、以及全部内部合法输入的实际输出存在性。实际输出来自已有内部递归纤维，并经双条件返回原 Run₃；并未把宿主程序执行成功当作对象存在证明。

ObjectOriginalFreeSubstFormula 提供九组闭句的 Source.ZF 推导、TheoryTransport 核证书和 ZFReplay 原 nativeZF 重放。

## 原检查器调用位置及签名边界

固定上游源审查记录在 MODE3_CHECKER_SCOPE.json。全仓验证检查四份上游文件的精确SHA、六个证明节点形状、27个逻辑模式及调用守卫：

| 原位置 | 实际语法变换调用 | 结论 |
|---|---|---|
| forallShape | mode1 | 顶层自由变量抽象；本批mode3接口不代替此义务 |
| strengtheningShape | mode0 | 自由上下文加强；完整Pure检查桥仍需核查 |
| substitutionShape | mode3 | 参数为values3，输入values5，输出values1；先检查bound=0的项列表 |
| 27个logical shapes | mode1／2，共七个调用 | 没有mode3调用；顶层抽象／实例化的全内部对应仍需完成 |

共享 ObjectTermSyntax.termRules 还包含 BasicSetTheory 的函数应用规则；其语言显式含 emptySet、powerSet 等函数符号。空绑定界的扩展签名项可以是函数项，不能直接视为本批纯语言的自由变量像。

因此本批只证明上述纯成员类型守卫下的全内部合同。最终专用纯语言语法检查关系仍须与这些守卫对象等价，才能接入 ProofZF/U。源码调用清单是可复核审查证据，不是该对象桥的证明。最终检查器适用性和纯语法检查桥的门保持false。

## 实际验收

1515构建任务、16436项审计（385无公理／16051允许依赖）、零警告；九命令及五trust=0入口全部退出0；1380份独立哈希一致、1858对精确证书足迹、14092项Internal显式声明覆盖。

- 新增53项声明显式列入Audit，九组新增核心／native证书的精确依赖均复核。
- 全仓 --wfail 构建、五个 --trust=0 入口及展开的无预给frame合同检查实际退出0。
- 七份既有锁文件和 YesMetaZFC 提交039c8e132cc19671d73a3933c66b4799d2599dd6未改变；上游工作树干净。
- MODE3_CHECKER_SCOPE.json 纳入独立源码哈希；四份上游源文件和实际调用守卫通过验证。
- 无新增sorry／admit／占位公理；标准三项及固定原七项依赖保持原口径，Choice桥隔离。

证据：verification/checker-free-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另复核本批Git字节，保留17份既存CRLF-only blob。

## 下一工程流程

| 顺序 | 实现任务 | 对象验收目标 |
|---|---|---|
| 1 | 专用纯成员语法检查规则：变量、项列表和完整公式 | 不允许扩展函数符号；全部内部原kind0／1／4检查查询分别与纯Term／TermList／FormulaCode对象等价 |
| 2 | 对接原节点的模式3调用 | 由实际纯语法查询得到本批EmptyBound输入守卫，再接原Run；不缩小纯语言内部Proof码范围 |
| 3 | 原数值quotation及mode0／1／2／3、Option | 任意内部输入／输出候选的准确成功／失败及顶层实例化／抽象对应 |
| 4 | 专用ProofZF／ProofU | 原六规则／27模式、完整Separation／Collection、全部内部证明码的检查和变换正确性 |
| 5 | 内部解释与一致性传输 | 精确原nativeZF推导Con_ZF → Con_target，核对全部对象量词与背景依赖 |

本批完成了实际纯参数输入下的mode3全公式接口；完整检查器、ProofZF/U和最终内部Con均未完成，目标保持active。
