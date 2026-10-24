# Project实际编译器全内部递归方程验收（2026-10-25）

本批将真实父历史中的子查询迁移为实际Compiler关系，得到全部内部候选上的十二分支递归双条件。9个新模块、80项显式声明、12组闭句返回原nativeZF核。最终闭句仅需Ω前提；历史、载体、状态和求值见证均已在对象推导中消去。

这是一条实际递归方程。合法源的输出存在、所有产出的目标类型及标量输出唯一性仍需内部Foundation归纳；完整schema测试、Proof、解释及最终Con均未完成。

## 对象语言、背景理论与最终目标

对象语言仍为纯等号／成员；背景仍为Contract.nativeZF及完整Separation／Collection，正式推导仍为原YesMetaZFC.Logic.FirstOrder.Derives。完整目标不变：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖全部内部ω、原六规则／27逻辑模式和完整理论公理模式。当前结构树码还未与全部原NatPacket字节包／Horn查询对应。对象Con的这个规格仍待实际完整Proof_T和最终推导，不以宿主Consistent或语义模型替代。

## 本批实际获得的闭句

ObjectProjectCompilerRecursive.native_compilerAllInternalRecursiveLaw返回原nativeZF内以下句子的翻译：

~~~text
close(Ω(w) → ∀n,b,q
  (Compiled(w,n,b,q) ↔
    n∈w ∧ b∈w ∧ q∈w ∧
      ∃z (Empty(z) ∧ Cases_Compiled(w,b,z,n,q))))
~~~

Cases_Compiled使用前批实际十二分支模板。每个子查询保留严格界x∈n，并调用真实Compiled(w,x,B,Q)；量词分支以内部存在量词取得实际后继作用域B，所有候选作用域和产出码仍为对象变量。q是输出码，不是自由变量作用域长度。空集z也是内部见证。

∀n,b,q遍历全部内部对象。对非自然输入由真实Compiled守卫及criterion守卫双向拒绝；没有把结果限制到模型外部标准自然数、有限quotation实例或事先已知合法的源码。

## 推导链与见证消去

1. ProjectCompilerQueryBridge：由实际父图、载体和严格子界，证明Read(h,x,b,q)与真实Compiled(w,x,b,q)等价。子自然性由父自然性及成员下降实际推出；不假设目标类型或编译正确性。
2. ProjectCompilerQuerySyntax／QueryTransport：对象ALL3统一所有子码、作用域和候选输出；将守卫查询双向对应传入真实后继作用域的EX查询。Bool仅是两个固定检查模板的外部模式索引。
3. ProjectCompilerCaseTransport：在原推导规则内穿过EX2／EX4和全部十二分支。保留两个常量、三类原子、否定、四个二元联结及两个量词的原输入／输出构造条件。
4. ProjectCompilerLocalBridge：将实际历史依赖局部程序等价替换为直接Compiler criterion。
5. ProjectCompilerRecursivePoint：由真实状态边得到criterion，并从实际求值构造父历史／状态，将产出码双条件接回真实Compiled。
6. ProjectCompilerRecursive：内部取得并消去求值和幂集载体，处理全部无效候选；最终只保留Ω前提，再引入对象ALL3。
7. ObjectProjectCompilerRecursive：12组source闭句经TheoryTransport.sentence进入原核，ZFReplay.replay回放到nativeZF；CheckStep4逐组使用实际返回类型验收。

Query等价的ALL3是已经由实际父图证明的对象公式；最终递归方程不额外假设这个公式。任何辅助阶段保留的图／载体前提均在最终闭句中消去。

## 审计与实现边界

新增声明全部逐项#print axioms。12组core精确依赖既定propext、Classical.choice、Quot.sound；native精确再继承原七项固定证书。没有新增对象Choice公理、自定义axiom、目标类型oracle、宿主递归正确性替代或预算／linter豁免。

scripts/verify.py逐名登记12组native入口和精确足迹；检查全十二模板、真实子查询传输、全部见证消去和最终仅Ω的前提。保留前批所有门禁与18份实际递归重新实例化严格比较。全部源码正确性／schema／Proof／Con完成门禁保持false。

## 实际验收

- 全仓2092构建任务通过；九命令及五个--trust=0入口全部退出0，零警告。
- 22601项声明审计：448项无公理、22153项仅含记录的允许依赖；80项新增显式声明全部覆盖。
- 1875份文件SHA256独立回读一致；累计2509对core／native精确公理足迹一致；20257项Internal显式声明全覆盖。
- 12组新增原核／native闭句精确足迹一致；1897任务定向构建零警告。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且依赖仓干净；既有PPAC证明及AST保持原Git字节。
- 全源输入输出类型唯一、全十二构造正确性、完整schema测试、Proof／解释及最终Con门禁继续false。

验收前基点c8ad4af66ab0129047216efd4f251774362e766f。既有PPAC证明及AST不改；本批只新增9模块，改4个接入文件和6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,project-compiler-recursive-readback.json}及.local/project-compiler-recursive-native-directed.log；复验C:/Python314/python.exe -X utf8 scripts/verify.py。没有推送远端。

完整编译前重新检查进程及本批临时产物：残留Lean／Lake为0、停止进程0、确认无用脚本／被替代失败日志0、删除0。本批各定向运行成功，保留有效生成／回读脚本、源码和缓存；检查收据.local/workspace-cleanup-project-compiler-recursive-result.json。编译前C盘约92 GiB可用，已解除此前空间阻塞；无删除带来的空间回收可报告。

## 修订后的agent工程流程

| 单元 | 输入与工作 | 必须交付及验收 | 状态 |
|---|---|---|---|
| T1.2c.2 源判断 | 独立十二构造源语法及原递归图 | 对象ALL3源递归方程，消去全部载体 | 前批已验收 |
| T1.2c.2 编译构造／基步 | 十二分支实际编译算子、Separation状态和原递归图 | 实际Compiler；常量／原子实际产出及原子类型 | 前批已验收 |
| T1.2c.2 查询迁移／递归方程 | 实际父图、严格子界、真实后继作用域 | Read↔Compiled；十二分支传输；仅Ω的全内部递归双条件 | 本批已验收 |
| T1.2c.2a 产出类型 | 本批递归方程、目标构造器类型律、对象成员IH | Foundation归纳消去IH，所有实际产出均有准确FormulaCode；空集见证对齐 | 下一步，未完成 |
| T1.2c.2b 源输入完备 | 源递归方程、实际Compiler方程及构造器存在性 | 全内部合法SourceCode实际取得目标产出；全部见证在对象EX内取得并消去 | 未完成 |
| T1.2c.2c 标量唯一 | 实际源构造器不交／注入性及子产出唯一 | 全内部合法源的唯一输出码q；与求值集合V唯一明确区分 | 未完成 |
| T1.2c.3／d | 原NatPacket字节包、Horn、正文、重命名和闭合 | 全内部schema准确载荷／模板／公理测试对应 | 未完成 |
| T1.3／T2 | 完整公理测试与原六规则／27模式 | 共享实际Bool、Proof_ZF／Proof_target、全内部证明编译传输 | 未完成 |
| T3 | 完整数学解释及T2 | 原nativeZF内解释正确性及最终内部Con蕴含 | 未完成 |

下一单元首先固定对象归纳性质，再证明十二分支的类型保持；不得把递归方程、唯一状态集合、条件IH或成功构建当作输入完备／标量唯一／完整Con的证明。
