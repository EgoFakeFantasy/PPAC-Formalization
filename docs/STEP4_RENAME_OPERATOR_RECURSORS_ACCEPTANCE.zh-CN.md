# 实际重命名状态算子及全内部递归验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 4713d81ff84a8630bb22995e961b07f0772ba43e。
F1c、F1d 的实际状态算子与递归基础已验收。完整公式重命名正确性和唯一公式输出仍未证明。

## 对象语言、背景及交付

语言仍是原 YesMetaZFC 的单排序纯等词/成员语言；背景为原 nativeZF，即 Collection 版 ZF 的纯语言像。
不加入 AC、不可达或 Con(ZF)，不修改原六条 Hilbert 规则、27 类逻辑模式或完整公理模式。
新增 18 模块、326 项显式声明及 42 个完整闭句模式。
每个闭句模式都有实际 Source.Derives，经 TheoryTransport 和 ZFReplay 返回
FirstOrder.Derives nativeZF [] (Translation.sentence ...)。
有限 Bool/Fin 4 只索引原固定构造分支，内部码、长度、作用域、图及字段候选仍是全部内部对象。

## F1c.1：实际历史查询和11类矩阵

Contains(w,V,R,S,a,b,c,d,q) := ∃p(p∈V ∧ State(w,R,S,a,b,c,d,q,p))。
Read(w,H,x,R,S,a,b,c,d,q) := ∃V(Edge(H,x,V) ∧ Contains(w,V,R,S,a,b,c,d,q))。
R、S 是两个自然映射码；a,b 是源 bound/free，c,d 是目标 bound/free。
原七字段 State 保留实际原 Forest(7)、两个 MapCode 和目标 FormulaCode。

给定完整 FunctionOn(H,D) 及真实 Edge(H,x,V)，Read 精确等价于 Contains(w,V,...)。
再给 Ω(w) 和实际 State(...,p)，Read 精确等价于 p∈V；
原完整图单值性和状态码唯一性对齐两个实际存在见证，没有宿主数据选择。
量词 Advanced 实际存在量化 u、v、L：
CodedLift(w,a,c,R,u,v,L) ∧ Read(w,H,x,L,S,u,b,v,d,q)。
CodedLift 内含真实两个后继及实际完整提升图；S、b、d 原样保留。
原核证明 Advanced 的实际见证引入与原 free 映射码保持。
关键证书：native_containsAtState、native_queryAtValue、native_queryAtState、native_advancedIntro、native_advancedFreeMap。

Cases 的原构造和检查如下：

| 原标签 | 对象分支 |
|---|---|
| 0、1 | 源与目标的同标签原零字段构造，保留两端上下文 |
| 2：membership | 同一个实际零符号码 z 同时作为源/目标原关系符号；两个项使用解码后的实际完整图重命名 |
| 3：equality | 源/目标原等词构造及两个实际项重命名 |
| 4：negation | 源/目标原单字段构造，源子码 x∈n，按原两个映射码读取历史 |
| 5、6、7、8 | 源/目标原双字段构造，两源码均严格属于 n，分别读取相同映射及作用域的历史 |
| 9、10 | 源/目标原量词构造，源码严格属于 n，Advanced 实际提升 bound 自然码并保留 free 码 |

两个原图 r、s 在 LocalRename 内实际存在量化，分别满足 Encoded(w,r,a,c,R)、Encoded(w,s,b,d,S)。
原子分支消费这两个完整图；逻辑分支消费自然码历史查询。
没有直接把宿主 AST 重命名函数当作对象关系。
六个分支族的原核接入模式覆盖上述全部11类；没有宣称已证明全部构造的最终重命名双条件。

## F1c.2：原Separation实际给出唯一状态集合

Content := FormulaCode(w,n,a,b) ∧ LocalRename(w,R,S,a,b,c,d,H,n,q)。
Row(w,n,H,p) 实际存在量化七字段，并要求 State(...,p) ∧ Content。
Value(w,n,H,V) 使用一个明确的原 Separation 实例，精确规定：
∀p(p∈V ↔ (p∈w ∧ Row(w,n,H,p)))。

原核实际证明：

- 对全部内部 w、n、H，实际存在唯一 V；无需任何未证的算子总单值前提。
- V⊆w；给定原 PowerOf(U,w)，有 V∈U。
- 给定实际 State(...,p) 和 Ω(w)，p∈V 精确等价于同一七字段上的 Content。
- 任意行的候选七字段通过同码单射全部对齐；该转移使用对象等词替换。
- p∈V 实际推出状态被识别；源码 n∈w。若 n∉w，V 为空。

关键证书：native_valueExists、native_valueUnique、native_valueFiber、native_valueSubset、native_valueUniverse、
native_valueMember、native_rowAtState、native_valueAtState、native_memberRecognized、native_offNatural。
状态集合唯一不等于其中目标公式码唯一；后者是 F1e 的待证明结论。

## F1d：实际原递归图、值和前缀方程

递归矩阵以 w 为唯一固定参数，末三槽是索引 n、完整历史 H 和集合值 V，正文为 Value(w,n,H,V)。
原 Separation 与 Extensionality 消去原超限递归接口的 total/deterministic 两个前提。
对每个内部原序数 D，实际存在唯一完整 Recursor(w,F,D)。

Evaluation(w,n,V) 实际存在量化后继域 s 和完整递归图 F：
Succ(s,n) ∧ Recursor(w,F,s) ∧ Edge(F,n,V)。
原核证明每个内部原序数 n 都实际取得唯一 V；因而 Ω(w) 下每个内部 n∈w 亦如此。
任意实际原序数前段图的每条域内边精确等价于该索引的 Evaluation。
实际 Evaluation 又产生实际完整前段 H，满足 Recursor(w,H,n) ∧ Value(w,n,H,V)。
所以前缀是完整原递归图，分离方程保留真实历史，不能用任意关系或语义函数代替。
求值结果 V⊆w；给定真实幂集 U 则 V∈U；非自然序数输入得到空状态集合。

关键证书：native_operatorTotal、native_operatorDeterministic、native_recursors、native_graphFiber、
native_evaluationFiber、native_naturalEvaluationFiber、native_graphEdgeValue、native_prefix、native_evaluationSubset、native_evaluationUniverse。
native_carrierRecursors 实际取得原幂集载体及全内部唯一递归族。
native_existence 进一步联合构造实际 ω、原幂集载体和完整递归族；不残留这些对象的存在前提。

## 实际机器验收

C:/Python314/python.exe -X utf8 scripts/verify.py 退出 0。
两份源锁、版本、全仓 wfail 构建及五个 trust=0 入口共九条命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 720 jobs，退出 0 |
| 声明审计 | 7794 项；284 项无公理依赖，7510 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 18 模块、326 项，全覆盖 |
| Internal 累计显式声明 | 5479 项，无漏审 |
| 新增闭句模式 | 42 对核心/native 精确依赖足迹 |
| 累计闭句模式 | 670 对核心/native 精确依赖足迹 |
| 源码 SHA256 独立回读 | 689 份，差异 0 |
| 九命令/五 trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

核心证书精确依赖 propext、Classical.choice、Quot.sound；
native 证书另含原七个固定 ZF 定义证书的既有依赖，不含原 choice 的额外证书。
原 choice 额外证书仍只限既有桥接模块；没有新增自定义公理。
独立复核记录在忽略目录 verification/rename-operator-recursors-readback.json。
原 OpenAI 完整构建/Comparator 本批未运行；日志和生成辅助留本地；未推送。

## 下一关：完整FormulaRename

先把实际求值中的 Contains 包装为有限纯成员 RenameFormula 关系，
证明实际前段查询与该关系的双条件，再将11类局部方程转成不带历史参数的递归双条件。
随后对包含全部内部映射码和作用域参数的性质作对象成员归纳，
构造每个合法内部输入的实际唯一目标公式码，关闭所有原构造和量词分支。
工程流程见 AGENT_WORKFLOW.zh-CN.md 的 F1e.1 至 F1e.4。

完整 FormulaRename、捕获规避替换、ProofZF/U、任意内部证明码正确性、内部编译器及解释仍未完成。
最终仍要求原 FirstOrder.Derives nativeZF [] (Formula.imp Con_ZF Con_target)，
其中内部 Con 量化全部内部 ω 证明码。
