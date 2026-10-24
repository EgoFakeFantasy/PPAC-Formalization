# 全内部参数全称闭合及准确作用域类型验收（2026-10-24）

本批完成schema公理测试所需的任意内部次数全称闭合：次数n是对象ω元素，输出由原对象递归图取得，零点／后继、存在唯一及准确类型均有原核证明。类型律将bound作用域从n+b精确降至b，剩余b和候选输出在对象ALL2中变化，ω归纳假设已消去。11组闭句传入原nativeZF。

完整Project schema正文翻译、模式模板装配、实际原Horn条件对应、完整理论测试及最终Con仍未完成；本批不得据此置其门禁为true。

## 背景与最终目标

纯等号／成员ℒ；背景仍为Contract.nativeZF，含完整Separation／Collection；原FirstOrder.Derives。最终要求：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Con必须覆盖全部内部ω、原六规则／27模式及完整公理模式。这里保留最终规格；实际完整Proof_T／内部数学解释与最终主句仍未构造并证明。宿主编码模式或编译成功均不替代该目标。

## 实际对象公式及结论

Unary(tag,w,a,n,y)由NaturalEvaluationSyntax.evaluation定义：真实后继域、完整原递归图和末值边均在对象EX中。自然输入的步进是原一字段构造器；ω外输入总化为对象零，以满足原递归定理的全域总单值义务。tag是固定有限公式模式索引，n、a、y都是对象槽。

~~~text
Step(tag,w,x,y) =
 (x∈w ∧ Ctor(1,tag,w,[x],y)) ∨ (¬x∈w ∧ Empty(y))
Close(w,a,n,y) = Unary(9,w,a,n,y)
~~~

存在唯一性、自然值域和准确零／后继关系已证明，递归存在唯一证据由ZFContext.closed和原NaturalRecursion.source_uniqueness取得；最终接口不保留假定递归图、语义模型或正确性证书。

~~~text
nativeZF ⊢ close(Ω(w) → a∈w → ∀n∈w. ∃!y∈w Unary(tag,w,a,n,y))
nativeZF ⊢ close(Ω(w) → a∈w → Empty(z) →
                  (Unary(tag,w,a,z,y) ↔ y=a))
nativeZF ⊢ close(Ω(w) → a∈w → n∈w → Succ(s,n) → Unary(tag,w,a,n,u) →
                  (Unary(tag,w,a,s,y) ↔ Ctor(1,tag,w,[u],y)))
~~~

存在唯一纤维保留候选输出的对象全称量词。没有把次数换成外部Nat，也没有施加固定长度上界。

主要类型出口是：

~~~text
Ω(w), a∈w, f∈w, n∈w, b∈w, Sum(w,n,b,source), Close(w,a,n,y)
  ⊢ FormulaCode(w,y,b,f) ↔ FormulaCode(w,a,source,f)
~~~

这覆盖全部内部合法纯语言码和任意内部n／b，不要求输入是外部AST的quotation。原FormulaCode仍是完整11构造关系；没有把“合法”改成宿主可解码或标准码。

取b=f=对象零z得到闭句类型律。更强的接受纤维接口只需Ω、Empty(z)及FormulaCode(w,a,n,z)：类型守卫实际提供a∈w和n∈w，输出y自然、Close(w,a,n,y)、FormulaCode(w,y,z,z)以及全部候选输出的唯一性均在结论中，所有见证对象消去。

## 模块与归纳核查

| 模块 | 工作 |
|---|---|
| SyntaxUnaryIterationStep | 真实一字段原构造器、ω外总化；全域总单值、自然范围 |
| SyntaxUnaryIterationSyntax／Core | 对象EX递归关系、自然输出纤维、ZF消去递归义务、存在唯一 |
| SyntaxUnaryIterationLaws | 精确零点／双向后继、显式ALL覆盖全部内部次数 |
| SyntaxForallClosureTypingSyntax | correctAt及ALL2；b和输出在IH内部变化，固定参数为w／输入／source／f |
| SyntaxForallClosureTypingHelpers | Sum(s,b,source)与Sum(n,Succ(b),source)的对象转换；原∀构造的准确FormulaCode类型律 |
| SyntaxForallClosureTypingPoint | 零点类型及后继IH组合；新bound后继和前阶段代码均在对象EX内取得／消去 |
| SyntaxForallClosureTyping | 原完整Separation支持的对象ω归纳，消去IH，得到全部n的类型双条件 |
| SyntaxForallClosureOutput | 由输入类型推出自然守卫，构造唯一闭公式输出 |
| ObjectForallClosure | 11组source／sourceZF原核／nativeZF闭句；展开主验收公式 |

后继步并非在固定b上使用IH：先在对象层取得c=Succ(b)，用算术转换取得Sum(n,c,source)，再将IH实例化到c。原∀构造器把前阶段bound=c的类型精确转为当前bound=b；输入和输出数码不变换成宿主对象。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句组 | 10／112／11 |
| 定向native构建 | 1789项，退出0、零警告 |
| 清理后全仓构建 | 1994项，退出0 |
| 声明审计 | 21669项：427无公理、21242允许依赖；0警告 |
| 验收命令 | 9条全部退出0，含5个trust=0入口 |
| 独立SHA256 | 1777份一致 |
| 精确core／native足迹 | 2431对，含本批11对 |
| Internal显式覆盖 | 19325项 |
| 上游／锁 | YesMetaZFC 039c8e132cc19671d73a3933c66b4799d2599dd6干净，7锁不变 |

本批core恰含propext／Classical.choice／Quot.sound；native另含原7项锁定证书。前批固定公理测试中core也继承7项的6对足迹继续逐名精确检查，没有扩大许可。没有新的自定义公理、Choice证书或数据选择函数。

新增全部112声明纳入Audit。sourceguard检查对象ALL次数、ALL2的变化参数、实际ω归纳及原递归证据、闭纤维只有Ω／Empty／输入类型前提；CheckStep4逐组检查并展开两项主公式。展开验收式曾有一个多余括号，已修正并完整重跑；失败运行未计为通过。

以前跟踪的PPAC证明及AST保持Git字节。本批仅10新模块、4接入文件及6文档。验收前基点5cb4fe646f1a539a65845e713e1b527caff4b6d8；提交后逐文件字节和accepted_commit记录于verification/forall-closure-readback.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py。

本地证据verification/{summary.json,commands.json,build.log,audit.log,forall-closure-readback.json}及.local/forall-closure-native-directed.log、forall-closure-full-verify.log。未推送远端。

## 清理与流程衔接

全仓编译前确认无残留Lean／Lake，停止失效进程0；按白名单删除5份已由成功运行替代的失败日志，记录SHA256并逐项删除回读。逻辑删除23098字节，盘面实测增加28672字节；有效源码、构建缓存及有用生成／回读脚本保留。收据.local/workspace-cleanup-forall-closure-result.json；清理后已实际完成完整验收。

| 单元 | 具体实现及出口 | 状态 |
|---|---|---|
| T1.1 | 固定7+3部分公理测试、原行码及小标签包算术 | 已验收，完整测试false |
| T1.2a，本批 | 全内部次数闭合、准确n+b→b作用域及唯一闭公式输出 | 已验收 |
| T1.2b，下一步 | 原unaryUnderTwo、binaryUnderOne／Two对应的全部内部参数索引图，证明真实作用域与完整map／binder兼容；接已有全公式重命名器 | 未完成 |
| T1.2c | 原Project十二构造正文到纯十一构造编码；成员字段补原关系标签、等号保持原始等号、subset展开∀／→／∈并正确移动bound | 未完成 |
| T1.2d | 真实Separation／Collection模板、正文图及本批闭合；核对实际原Horn条件与准确行／证书码 | 完整理论测试false |
| T1.3 | 既有源Replacement／原Collection对象互导的数值证书编译与全内部正确性 | 未完成 |
| P1 | 实际共享Bool／Proof_ZF／Proof_target方程，六规则／27模式及全部内部ω；实例化已证Foundation唯一性 | 未完成 |
| I1 | 普通ZF中的逐公理数学解释、强迫／对称名、PP全秩及ACwo／非AC见证；核对universe与背景 | 未完成 |
| C1 | 实际内部Con主句及原核Derives nativeZF [] (Con_ZF→Con_target) | 未完成 |

本批Close是明确的纯对象递归关系；尚未证明它与上游ObjectUnaryIteration.condition的全内部码对应，不能引用上游ZFC中对外部Nat的positive／negative证书代替这条桥。完整schema测试前仍须核对Project原格式、纯语言格式、参数数目和闭合算子，既有外部AST等式不能独自消去该缺口。
