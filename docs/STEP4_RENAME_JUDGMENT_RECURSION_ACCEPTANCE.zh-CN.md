# 纯对象RenameFormula判断与完整递归双条件验收

2026-10-22；分支 migration/yesmeta-step3；基点 1ddc88f0cf8cf148021d592d6064a8099c70e0ad。
F1e.1、F1e.2 已验收。全部合法输入的实际唯一目标公式码仍未证明，完整重命名总关卡保持未完成。

## 对象背景与证书

语言仍是原 YesMetaZFC 的纯等词/成员语言，背景固定原 nativeZF，即原 Collection 版 ZF 的纯语言像。
没有加入 AC、不可达或 Con(ZF)，没有更换原六条 Hilbert 规则、27 类逻辑模式或完整公理模式。
新增 12 模块、150 项显式声明及 21 个完整闭句模式。
每个模式经 Source.Derives、TheoryTransport 和 ZFReplay 返回真正的
FirstOrder.Derives nativeZF [] (Translation.sentence ...)。
所有内部码、作用域、图和目标候选都在对象量词范围内，包括内部非标准自然码。

## F1e.1：实际纯对象判断

RenameFormula(w,R,S,a,b,c,d,n,q) :=
n∈w ∧ ∃V(Evaluation(w,n,V) ∧ Contains(w,V,R,S,a,b,c,d,q))。
R/S 是 bound/free 自然映射码，a/b 为源作用域，c/d 为目标作用域。
Contains 实际存在量化原七字段状态码，并检查该状态码属于实际集合值 V。
Evaluation 保留实际后继域、完整原递归图和真实输出边。
自然码守卫是内部 n∈ω，不是外部标准自然数界；非自然候选被正式拒绝。

原核证明：

- 对给定内部原序数 n 和实际求值 V，RenameFormula 精确等价于 Contains(w,V,...)。
- 对任意完整原序数前段 Recursor(w,H,D) 及任意内部 x∈D，原 Read 精确等价于对应的 RenameFormula。
- 上条没有另加 x∈w 前提；从实际求值的状态成员及原 Separation 方程正式恢复该事实。
- RenameFormula 推出两个实际 MapCode 及目标 FormulaCode；Ω(w) 下也推出源 FormulaCode。

关键证书：native_atValue、native_read、native_legal、native_targetType、native_sourceType、native_rejectCode。
判断及所有见证均是有限纯成员公式，没有宿主选择函数、模型满足关系或新谓词公理。

## F1e.2：全部11类不带历史的递归判据

原子四类分支保持原样，继续消费实际解码的两个完整图及实际项重命名。
membership 保留同一个内部零符号码。七类逻辑/量词分支把 Read 换成 RenameFormula。
严格子源码 x∈n、y∈n 保持原对象守卫，存在字段仍由原存在量词量化。

量词的 AdvancedRename 仍实际绑定 u、v、L：
CodedLift(w,a,c,R,u,v,L) ∧ RenameFormula(w,L,S,u,b,v,d,x,q)。
两个真实后继、实际 bound 提升码和不变的 free 码/作用域全部保留。
原存在量词同余给 AdvancedRead↔AdvancedRename，并逐字段、逐分支组合全部11类。
关键证书：native_advanced、native_check、native_singleFields、native_binaryFields、
native_singleCase、native_binaryCase、native_allCases、native_local。

HistoryFreeLocal 实际绑定两个完整解码图，并采用上述不带历史的11类 Cases。
Criterion := n∈w ∧ (Legal(w,R,S,a,b,c,d,q) ∧
  (FormulaCode(w,n,a,b) ∧ HistoryFreeLocal(w,R,S,a,b,c,d,n,q)))。
给实际状态值，原七字段同码单射和实际状态构造给出精确 Contains 双条件。
再使用原递归图实际前段与求值，把所有 Read 消去为子判断。
对象 ω 成员/非成员分类实际关闭求值和前段存在前提，得到：

Ω(w) → (RenameFormula(w,R,S,a,b,c,d,n,q) ↔ Criterion(w,R,S,a,b,c,d,n,q))。

只有 Ω(w) 是对象前提；n、两个映射码、四个作用域及 q 均是任意内部候选。
非法码、非法作用域和非自然候选没有被外部索引排除。
关键证书：native_containsCriterion、native_recursiveAtValue、native_recursive。
这里证明的是完整递归判据的双条件；给定单个原构造器的精确重命名律和实际唯一输出另在 F1e.3/F1e.4 验收。

## 内部统一定律及实际系统

UniversalLaw(w) 以八个对象全称量词量化 R,S,a,b,c,d,n,q，正文是同一递归双条件。
它只涉及固定 RenameFormula 关系，不是任意公式的统一真值谓词。
原核还实际联合构造 ω、其原幂集载体、完整唯一递归族和 UniversalLaw。
关键证书：native_universal、native_actualSystem、native_existence。
该存在闭句没有额外载体、递归族或 ω 的存在前提。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py 退出 0。
两份源锁、版本、全仓 wfail 构建及五个 trust=0 入口共九条命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 732 jobs，退出 0 |
| 声明审计 | 7944 项；284 项无公理依赖，7660 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 12 模块、150 项，全覆盖 |
| Internal 累计显式声明 | 5629 项，无漏审 |
| 新增闭句模式 | 21 对核心/native 精确足迹 |
| 累计闭句模式 | 691 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 701 份，差异 0 |
| 九命令/五 trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

核心证书精确依赖 propext、Classical.choice、Quot.sound；
native 证书另含原七个固定 ZF 定义证书的既有依赖，没有原 choice 的额外证书。
原 choice 额外证书继续只限既有桥接范围，没有新增自定义公理。
字段排列检查额外固定普通子判断的参数顺序；双字段分支分别把 x/X 与 y/Y 对齐。
独立复核见忽略目录 verification/rename-judgment-recursion-readback.json。
原 OpenAI 完整构建/Comparator 本批未运行；生成辅助和日志留本地；未推送。

## 剩余对象义务

下一步 F1e.3 先冻结合法输入和实际输出纤维，证明固定实际 CodedLift 下的量词判断双条件，
再完成四类原子的实际唯一输出和七类逻辑的对象归纳步骤。
归纳性质必须量化全部内部映射码和作用域，量词提升后仍能实例化同一归纳假设。
最后关闭全内部成员归纳并验收单构造精确律，才提升完整 FormulaRename 总门禁。

实际唯一公式输出、公式映射代数、捕获规避替换、ProofZF/U、任意内部证明码正确性、内部编译器和解释仍未完成。
最终仍要求原 FirstOrder.Derives nativeZF [] (Formula.imp Con_ZF Con_target)，内部 Con 量化全部内部 ω 证明码。
