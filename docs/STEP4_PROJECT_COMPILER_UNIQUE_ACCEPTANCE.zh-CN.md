# Project实际编译产出的全内部标量唯一性验收（2026-10-25）

本批以原Foundation消去全部对象成员归纳假设，证明同一输入、同一作用域的任意两个实际Compiled产出码相等；并结合此前实际存在性与独立目标类型，取得全部内部合法源码的有类型唯一产出。16个新模块、109项显式声明、10组闭句返回原nativeZF核。

此处的唯一性是输出码q的标量唯一性，不再只是求值集合V唯一。实际产出反推源合法性、原NatPacket／Horn对应、完整schema测试、Proof／解释及最终内部Con仍未完成。

## 对象背景与完整目标

纯等号／成员对象语言、Contract.nativeZF与完整Separation／Collection背景均不变；正式推导仍为原YesMetaZFC.Logic.FirstOrder.Derives。完整目标保持：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

完整Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式及全部理论公理模式。本批结构树关系的唯一性不能替代这些尚未完成的桥接与最终Con推导。

## 实际原核结论

ObjectProjectCompilerUnique.native_compilerAllInternalOutputsScalarUnique返回以下对象闭句的翻译：

~~~text
close(Ω(w) → ∀n,b,q,r
  (Compiled(w,n,b,q) → Compiled(w,n,b,r) → q=r))
~~~

n、b、q、r均为对象变量，覆盖全部内部集合候选。结论不假设SourceCode、目标类型、历史、载体或成员IH；无效候选由实际Compiled的原守卫处理，未限制在模型外部标准自然数。

native_compilerAllInternalSourceTypedUniqueOutputExists同时给出：

~~~text
close(Ω(w) → ∀n,b,f,z
  (Empty(z) → SourceCode(w,n,b,f) →
    ∃q ((Compiled(w,n,b,q) ∧ FormulaCode(w,q,b,z)) ∧
      ∀r (Compiled(w,n,b,r) → r=q))))
~~~

源上下文f仍为任意内部参数；目标零元z由对象Empty约束。唯一性比较所有实际Compiled产出，而不限于已知有类型的产出。全部产出见证都位于对象EX中，没有提取宿主选择函数。

## 固定对象性质和真实分支比较

UniqueSyntax定义functional(w,n)=∀b,q,r(Compiled(w,n,b,q)→Compiled(w,n,b,r)→q=r)，以及内部成员IH=∀x(x∈n→functional(w,x))。这是一条固定对象公式上的原集合归纳，不是宿主Nat或有限quotation归纳。

UniqueTransport只用原等词替换，传输实际原子字段、实际子查询输入、目标构造字段与局部零元。UniqueQueries对真实守卫查询应用成员IH；对两份独立EX后继作用域先用原Extensionality得到后继唯一，再将实际Compiled的bound字段对象替换到相同作用域。

UniqueMatrixSyntax的十二个Mode是固定有限证明模板，字段与码仍为内部对象变量；它们没有作为新的对象码域或新推导核。UniqueMatrixHead从每张实际程序矩阵恢复准确源构造头，以原SyntaxConstructors.disjoint排除异标签。

UniquePadding只在对象EX4里补齐未使用字段槽，原实际Compiler和接受条件不改。常量／原子／一元分支的补齐由原规则实际推出，二元分支保留原EX4。完整十二分支被传输为这些对象存在式的析取；没有用padding关系重新定义Compiled。

UniqueAtoms在同原子分支用原构造器注入性恢复两份源字段，再调用已验收原子标量唯一性。UniqueLogical对同一元／二元分支恢复源子字段，以实际子码IH得到目标子码相等，最后用原目标构造器唯一性得到q=r。UniqueMatrices／Pairs合并异分支排除，并消去两份独立EX4字段块。

UniqueStep从两份实际Compiled的递归方程取得各自局部空集见证；由原Extensionality对齐两份空集，再比较准确实际分支。ProjectCompilerUnique将固定functional矩阵交给原SetInduction，使用Foundation、该矩阵否定的完整Separation及已有对象TransitiveCover，实际消去全部成员IH。

UniqueFiber结合已验收ProjectCompilerComplete.typed_output_exists与本批真实标量唯一性，构造对象typedFiber和全内部ALL4联合定理。10组闭句经TheoryTransport.sentence进入原核，再由ZFReplay.replay返回nativeZF；CheckStep4逐组以实际返回类型验收。

## 门禁和审计边界

109项新增显式声明逐一#print axioms；10组core精确依赖既定propext、Classical.choice、Quot.sound，native精确再继承原七项固定证书。未新增自定义axiom、对象Choice背景、宿主求值oracle、预算提升或linter豁免。

scripts/verify.py逐名锁定10组native入口与精确足迹，核查十二模板完整覆盖、源头注入／不交性、真实后继／零元对齐、两份EX4消去、原Foundation及最终仅Ω前提。旧构造阶段守卫已明确命名为该阶段本身的证明范围，避免与当前全局唯一性状态混淆。

object_Project_compiler_all_source_inputs_output_typed_unique_proved本批从false改为true，依据是上述实际原核联合闭句，不是改验收口径。新增标量功能性及Foundation消去门为true。实际产出反推SourceCode、完整十二构造迁移联合门、原字节包／Horn、schema、Proof及Con门继续false。

## 实际验收

- 全仓2128构建任务通过；九命令及五个--trust=0入口全部退出0，零警告。
- 22867项声明审计：452项无公理、22415项仅含记录的允许依赖；109项新增显式声明全部覆盖。
- 1911份文件SHA256独立回读一致；累计2537对core／native精确公理足迹一致；20523项Internal显式声明全覆盖。
- 10组新增原核／native闭句精确足迹一致；1933任务native定向构建零警告。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净；此前跟踪的PPAC证明及AST保持原Git字节。
- 唯一一次既有全局门禁变化为合法源有类型唯一输出false→true；实际源合法性反向、完整迁移联合门、schema、Proof／解释及最终Con门禁继续false。

验收前基点c66f545f6b1c368ff6242db84dd6793523b7bb8e。此前跟踪的PPAC证明及AST不改；本批只新增16模块、改4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,project-compiler-unique-readback.json}及.local/project-compiler-unique-native-directed.log；复验C:/Python314/python.exe -X utf8 scripts/verify.py。未推送远端。

全仓编译前按单文件白名单删除一份已被成功native构建替代的命名空间查询失败日志，保留SHA256并回读确认删除。逻辑删除1571字节，盘面实测差额4096字节，含系统并发活动。残留编译进程0、停止进程0；有效源码、缓存和有用生成／回读脚本保留。收据.local/workspace-cleanup-project-compiler-unique-result.json。

## 后续agent工程表

| 单元 | 实现职责 | 必须交付及实际验收 | 状态 |
|---|---|---|---|
| T1.2c.2 源判断／实际编译方程 | 两套独立关系及原递归图 | 完整递归方程、Read↔Compiled、历史／载体消去 | 前批已验收 |
| T1.2c.2a／b 类型与存在性 | 全十二实际分支及原Foundation | 全实际产出有目标类型，全合法源实际取得产出 | 前批已验收 |
| T1.2c.2c 标量唯一 | 实际源构造器不交／注入性、真实子码IH | 全实际产出码唯一；全合法源有类型唯一纤维；IH消去 | 本批已验收 |
| T1.2c.2d 输入合法性反向 | 实际Compiled、独立SourceCode及原Foundation | 对任意内部f∈ω，Compiled(w,n,b,q)→SourceCode(w,n,b,f)；与存在性合成精确输入接受双条件 | 下一步，未完成 |
| T1.2c.3／d | 原NatPacket字节包、Horn、正文、重命名和闭合 | 全内部schema准确载荷／模板／公理测试对应 | 未完成 |
| T1.3／T2 | 完整公理测试及原六规则／27模式 | 共享实际Bool、Proof_ZF／Proof_target、内部证明编译传输 | 未完成 |
| T3 | 完整数学解释及T2 | 原nativeZF内解释正确性与最终内部Con蕴含 | 未完成 |

下一步保留完整对象域，证明实际产出蕴含合法SourceCode，并准确处理源上下文f∈ω守卫；不能由目标FormulaCode或输出唯一性直接推断源输入合法。
