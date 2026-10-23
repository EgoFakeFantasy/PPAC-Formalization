# 有类型内部列表分支与原数值项桥验收

基点：a19f118bb2dad7528cccccd19175d9600b824b56。完成S3.4c.2b.2c.3c.2c.2b.3a，仅为有类型列表内部归纳的分解／重建基础及原数值项桥；不通过整个列表变换总性／唯一性／正确性门。

## 对象理论合同

对象语言为原YesMetaZFC纯等词／成员签名，背景为原nativeZF完整Collection呈现，正式推导为原FirstOrder.Derives。最终目标保持Derives nativeZF [] (Con_ZF → Con_target)，目标理论ZF+PP+ACwo+¬AC。内部Con仍要求全部内部ω证明码、原六规则／27模式及完整Separation／Collection；当前没有该最终推导。

本批所有句子由Source公式close构造，并经实际Source.Derives、TheoryTransport与ZFReplay取得原核闭句。外部Bool只索引固定mode0／3两模式；长度k、前驱ell、索引、头尾及候选输入／输出均是对象变量，不以Lean Nat或List替代内部ω。没有增加对象AC、标准ω或模型前提，也没有恢复退役反射。

## 完整类型分支

沿用既有TermList(w,k,a,b,n)：k∈w、合法上下文、n∈w、实际HasLength(n,k)和全部内部索引的typedFields。

```text
Parts(w,k,a,b,h,t) := ∃ell
  ((ell∈w ∧ Successor(k,ell)) ∧
   (Term(w,a,b,h) ∧ TermList(w,ell,a,b,t))).
NilCase := NilCode(w,n) ∧ (Empty(k) ∧ Contexts(w,a,b)).
ConsCase := ∃h ∃t
  ((h∈w ∧ t∈w) ∧ (ConsCode(w,h,t,n) ∧ Parts(w,k,a,b,h,t))).
Cases := NilCase ∨ ConsCase.
```

在Omega(w)下，对所有内部k,a,b,n，实际证明TermList(w,k,a,b,n) ↔ Cases。顶层不预给长度自然性或输入合法性：它们包含在两边的对象条件中。Cons的内部前驱长度是实际存在量词的见证，并非从外部标准长度取前驱。

分解方向用实际HasLength恢复合法结构轨迹；Cons步的自然头码来自实际原轨迹见证，尾码自然性来自合法尾轨迹。实际长度前驱引出头的零字段合法性与尾列表的全部字段类型。这里没有把ConsCode单独当成组件自然性的来源。

重建方向对任意内部索引使用对象零／后继分解；零字段经实际等词替换取得头类型，后继字段正式转到尾字段。对象前驱／后继序关系保证范围，原HasLength构造取得准确长度。不存在对宿主有限列表的归纳捷径。

## 原数值项运行桥

在实际Num0／Num3(mode)下，原五字段数值Run₁与既有布尔模式原项运行双向对应。消去原根行及其实际模式见证，用内部数码唯一性对齐mode，再在原行上正式等词替换。该桥对所有内部候选输入／输出成立，不额外假定Omega或输出自然性。

对有类型源项，在Omega、深度／参数自然守卫及实际环境图／转换列表前提下，mode3替换和mode0弱化分别接到独立TermProgram.run。mode3使用同一个原参数列表L，mode0允许任意自然参数；全部环境前提在闭句中显式保留。此双条件没有单独声称原Run₂列表变换已经存在唯一输出。

## 源码与闭句

| 模块 | 本批对象产物 |
|---|---|
| OriginalTermModeBridge | 数值模式根行、完整Run₁与既有原项运行双条件 |
| OriginalNumericTermProgram | 原mode3／mode0有类型项到独立项程序 |
| TypedArgumentListElimination | 实际内部前驱长度、合法头项、有类型尾列表 |
| TypedArgumentListConstruction | 对象Nil／Cons构造；全部内部字段的合法性 |
| TypedArgumentListCases | 完整内部Nil／Cons分支及两个方向 |
| ObjectTypedArgumentList | 11组Source→原核→原nativeZF闭句 |

11组模式为numericTermModeRunIff、numericReplaceOnTypedTerm、numericWeakenOnTypedTerm、typedNilListIntroduction、typedConsListIntroduction、typedConsActualPredecessor、typedConsHead、typedConsTail、typedNilListIff、typedConsListIff、typedWholeListCasesIff。每组均有明确Sentence、源推导、sourceZF原核证书及nativeZF证书；不是仅有AST。

## 实际验收

- 定向lake --wfail build PPAC.Migration.Internal.ObjectTypedArgumentList退出0；随后C:/Python314/python.exe -X utf8 scripts/verify.py退出0。
- 全仓1392构建任务、15271项审计（378无公理／14893记录允许依赖）、零警告。九条命令及五个trust=0入口全部退出0。Lean/Lake严格串行，LEAN_NUM_THREADS=1。
- 新增6模块76显式声明，11组核心／原生证书的依赖精确匹配既有基线；核心为标准三项，native为标准三项加原七固定证书依赖。全仓1692对证书足迹精确匹配、12927项Internal显式声明覆盖。
- 独立回读1256份工作区哈希，无差异；七份锁文件、隔离Choice桥及底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变。原45项执行／分支定义直接oracle检查全部保留；本批类型Cases是类型分解规格，不伪装为新的独立执行器。
- 命令、审计与独立回读分别在本地verification/commands.json、verification/audit.log、verification/typed-list-readback.json。未运行OpenAI全仓构建／Comparator，未推送或创建PR。

## 未完成门与下一步

本批仅将数值项桥、类型构造、实际前驱／头尾分解、全内部类型分支方程四个细门设为true。原全内部列表运行归纳和完整变换正确性门保持false。实际项输出纤维需接回原Run₁；再用原Separation／Foundation对内部列表码归纳，取得Run₂实际合法输出及对所有候选的唯一性，最后完成全索引逐字段对应。

原十一公式、原扩展语言quotation总桥、原规则5／4兼容、专用ProofZF/U及全内部证明检查／编译、解释和最终内部Con蕴含仍未完成。不能以本批编译或闭句验收称原定理迁移完成。
