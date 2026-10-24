# 原 mode1 任意内部深度的项／参数列表程序传输验收

基点：754b0e95ac039c289bb424d9d6152d7d008c4072。单元3f.2c.3b.2d.6g；4模块50项显式声明、10组原核闭句。

## 对象背景及未完成的最终目标

继续使用原YesMetaZFC纯等词／成员对象语言、完整ZF经Project.fo_theory的像，以及原FirstOrder.Derives。固定上游提交039c8e132cc19671d73a3933c66b4799d2599dd6及七份锁定文件均未改变；不增加AC、不可达或一致性假设。

内部Con规格仍是 `¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))`：ω由唯一最小归纳集的纯成员公式消去，Proof_T覆盖全部内部证明码、六条原规则、27逻辑模式和完整Separation／Collection。它不是宿主Lean可证明性，也不限制外部标准ω。专用ProofZF/U完整实现和最终对象句仍待完成，详见[对象目标](OBJECT_TARGET.zh-CN.md)。

```text
最终未证明：Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批将上一批已证明真实根实例及实际binder闭包的兼容frame，接到原Run1／Run2和实际项／参数列程序；完整mode1公式及forall尚未证明。

## 任意内部深度的项传输

AbstractFrameTerm.at_variable从frame取Num1、metadata及三内部全称变量兼容性，合并原AbstractVariableRun.run_iff、独立数值关系与实际字段对应、TermTransformProgramVariable.at_variable，证明原Run1与独立项程序的全候选双条件。

program_iff对两个真实纯项分支消去内部源索引。这里纯成员签名的函数符号表为空，合法纯项是bound／free变量；不把扩展签名的任意原始application码当作合法纯项。源／目标上下文界a/b与c/e保持独立，depth为任意内部自然数，不限制零深度。

coded_iff再接既有TermTransformProgramCorrectness和真实frame.termLists，得到原SyntaxCodedMixedTermSyntax.substituted。guarded_coded_iff将源项类型放进结论内部，反向从实际混合项操作恢复真实源类型：

```text
Ω(w), Frame(w,mode,depth,P,a,b,c,e,R,S)
  ⊢ [Term(w,a,b,n) ∧ Run1(w,mode,depth,P,n,q)]
       ↔ CodedMixedTerm(w,R,S,a,b,c,e,n,q).
```

候选输出q始终是任意内部对象，不额外要求给定输出自然性／类型。

## 实际唯一纤维与 Promise 消去

AbstractFrameTermFiber.agreement在对象ALL下覆盖全部候选输出。fiber调用实际独立程序的有类型唯一输出定理，再经已证agreement传到原Run1。promise在对象ALL／IMP下覆盖每个合法源项，实际推出OriginalNumericTermValueSyntax.promise。

因此后续列表接口使用的Promise是由原核证明取得的中间结论，而不是新的外部前提；没有通过宿主选择函数挑选输出。

## 任意内部长度的参数列表传输

AbstractFrameArguments.fields_iff在三个内部全称变量（列表索引、输入项、输出项）下，先由真实源列表取得输入项类型，再调用上述任意深度项程序双条件。它比较的是原字段Run1关系与独立ArgumentProgramFieldSyntax.fields，保留原字段语义。

run_iff调用每个固定模式编号小于4的原列表归纳完成接口，在mode1实例上使用刚刚实际证明的Promise，得到：

```text
Ω(w), Frame(w,mode,depth,P,a,b,c,e,R,S), TermList(w,k,a,b,n)
  ⊢ Run2(w,mode,depth,P,n,q) ↔ Mapped(w,R,S,k,c,e,n,q).
```

k、字段索引、n/q和depth均为内部对象变量，列表长度没有外部上界。归纳及Promise均未保留为最终前提。

guarded_iff最终只保留Ω与frame两个前提：

```text
Ω(w), Frame(w,mode,depth,P,a,b,c,e,R,S)
  ⊢ [TermList(w,k,a,b,n) ∧ Run2(w,mode,depth,P,n,q)]
       ↔ [TermList(w,k,a,b,n) ∧ Mapped(w,R,S,k,c,e,n,q)].
```

右侧也明确保留源TermList，因为独立Mapped本身只包含目标列表类型与逐字段程序，不能从它单独推出源列表合法。最终没有逐项Promise、列表IH、给定输出类型、原行码／轨迹、赋值或一致性前提。frame中使用的实际码表是操作参数；真实Top根实例和实际binder下的frame保持性已在上一批证明。

## 原核证书及实际验收

ObjectAbstractFramePrograms的10组闭句覆盖变量／全项程序、混合项操作、内部守卫、有类型唯一输出、全部输入Promise、字段／列表程序及最终守卫接口。它们经已验收源传输及ZFReplay，返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF []` 证书。

1739构建任务、18660项声明审计（399无公理／18261允许依赖）、零警告；九条命令及五个trust=0入口全部退出0；1574份工作文件独立哈希一致、2155对精确核／native证书足迹、16316项Internal显式声明覆盖。

证据：`verification/abstract-frame-program-readback.json`、`verification/commands.json`、`scripts/verify.py`。独立复核检查新声明覆盖及每组核证书的三项标准依赖、native证书的同三项加既有七项固定依赖；展开最终native列表合同，核查前提集合以及源守卫在两侧结论内；检查实际唯一纤维、Promise内部证明、原小模式列表归纳调用及全部内部字段比较。

原frame／binder闭包、原Run／参数列接受AST、独立程序、纯项语法及通用列表归纳源码均保持Git字节不变。未添加新公理或改变接受规格。

旧argument-map状态门现在精确表示“在已证兼容frame下，任意内部深度的合法列表映射”，该门及对应scope已更新为完成。它不表示完整mode1公式或最终证明检查器已完成；相应全公式／forall／Proof／Con门仍为false。

## 继续实施表

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 任意深度项／参数列 | 取frame变量对应、实际唯一纤维、Promise证明及原列表归纳 | 上述两个源守卫内部化双条件 | 本批完成 |
| 原小模式完整公式方程 | 将常量规则的模式小于4守卫及其原矩阵／应用／trace／Run方程覆盖真实mode1 | 原Run3↔原11分支outcomes，不能调用Bool false充当mode1 | 下一步 |
| 四原子分支与统一公式归纳 | 接实际项／列表对应、原原子程序、逻辑分支及已证binder闭包；内部化全部变化frame | 全部内部合法公式的完整mode1原运行正确性 | 待完成 |
| forall节点 | 原node9嵌套头、四查询及所有赋值界，接完整mode1变换 | 完整原纯关系节点双条件 | 待完成 |
| logical／theory／Proof／Con | 原27模式、完整ZF/U、共享quotation／Bool、内部编译及解释 | 原nativeZF内部Con_ZF→Con_target | 未证明 |

当前源里的OriginalFormulaRunEquation及其常量路径仍以旧mode0／3 Bool接口给出，必须先真实推广到mode1；其余大量公式局部分支已是通用内部参数接口，可在核对合同后复用。不得把本批项／列表结果表述为完整公式或最终Con证明。
