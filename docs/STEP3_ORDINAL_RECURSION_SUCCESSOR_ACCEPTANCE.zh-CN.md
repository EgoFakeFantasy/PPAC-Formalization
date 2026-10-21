# 任意参数算子的实际后继递归扩展及唯一纤维验收
日期：2026-10-21；基点3b7ba9772d9bd296acdc08a5a17694a792a51516。
分支migration/yesmeta-step3；全内部前段图收集/合并、全部内部序数上的递归存在和最终Con仍未完成。

## 原对象合同与总性
每个p : Source.Formula(n+3)给任意参数递推矩阵Φ(x,h,y)，原Recursor仍是完整FunctionOn及
∀x∈d∀y[Edge(f,x,y)→∃h(Restrict(h,f,x)∧Φ(x,h,y))]。
Ord严格保持原Source.ordinal；Kuratowski边、全部内部量词和原完整functionOn不变。
Total(p,ρ) := ∀x,h[(Ord(x)∧FunctionOn(h,x))→∃y Φ(x,h,y)]。
仅要求有效内部输入上的对象总性，不假定宿主函数、外部标准序数或外部良基。
Deterministic是上批相同有效输入上的对象单值性，作为明确的对象蕴含前提，不是新增理论公理。

## 新鲜扩展的精确旧域限制
GraphInsertRestriction对任意完整旧图f、旧域d、新输入x∉d、码c=〈x,y〉和Insert(g,f,c)
逐成员证明Restrict(f,g,d)。旧成员由完整entriesOn给合法旧域输入，并由插入进入新图。
反向对新图成员按旧成员或等于c分类；若等于c且输入属于d，Kuratowski输入唯一性给x∈d，违反新鲜性。
所以旧图本身就是实际旧域限制，未用Separation重新选择限制图。
GraphInsertElimination同步消去实际码、域和新图三个见证，只由原exE/rename/weaken组成。

## 旧/新位置完整递推条件
给定原Ord(d)、Recursor(f,d)及实际下一值Φ(d,f,y)，原序数不自属给d∉d。
Pairing/Union和既有图插入构造实际取得后继域s、Kuratowski码c及完整新图g。
对任意内部j∈s和任意输出Edge(g,j,v)，按后继成员j∈d或j=d分类：
- 旧位置：精确旧域限制给Edge(f,j,v)。f的递推条件提供实际历史h，d传递给j⊆d，
  RestrictionAlgebra.compose将同一个h证明为g在j上的限制，保留Φ(j,h,v)。
- 新位置：精确新值唯一性给v=y，原等词规则将Φ(d,f,y)转成Φ(d,f,v)；
  以旧图f及其精确旧域限制作为实际历史见证，取得新位置方程，再沿j=d替换。
OrdinalRecursionExtension以此证明全部递推方程，而非只验证新边；完整FunctionOn由实际图扩展见证提供。
原后继保持性同时给Ord(s)。实际构造的完整扩展结论为
∃s∃g[Succ(s,d)∧Ord(s)∧Recursor(g,s)∧Restrict(f,g,d)]。

## 实际后继图与唯一纤维
SuccessorGraph(p,ρ,d,g) := ∃s[Succ(s,d)∧Recursor(p,ρ,g,s)]。
SuccessorExists := ∃g SuccessorGraph；旧图存在加Total和Ord(d)实际给出该存在句。
若两个图各有实际后继域s,t，原Extensionality给s=t，原等词规则对齐递归域，
原后继序数性及上批给定递归图同域唯一给两个图相等。
UniqueFiber(p,ρ,d) := ∃g[SuccessorGraph(d,g)∧∀h(SuccessorGraph(d,h)→h=g)]。
这是真实存在唯一图，不是将唯一性当存在，也不从存在证书抽取宿主数据。
successorMatrix(p)的原Replacement relation、unique、fiber分别与SuccessorGraph、UniqueAt、UniqueFiber逐式相等，
接口已就绪，但本批尚未调用Replacement收集所有前驱图。

## 六个模式与实际理论
对每个任意矩阵p及参数数目，ObjectOrdinalRecursionSuccessor关闭全部参数和显示变量：

| 模式 | 完整对象结论概要 |
|---|---|
| evaluationSentence p | Total→Ord(d)→Recursor(f,d)→∃y Φ(d,f,y) |
| preservationSentence p | Ord(d)→Recursor(f,d)→实际原图插入见证→Φ(d,f,y)→Recursor(g,s) |
| extensionSentence p | Total→Ord(d)→Recursor(f,d)→∃s∃g[Succ(s,d)∧Ord(s)∧Recursor(g,s)∧Restrict(f,g,d)] |
| successorSentence p | Total→Ord(d)→RecursorExists(d)→SuccessorExists(d) |
| uniqueSentence p | Deterministic→Ord(d)→SuccessorGraph(d,g)→SuccessorGraph(d,h)→g=h |
| fiberSentence p | Total→Deterministic→Ord(d)→RecursorExists(d)→UniqueFiber(d) |

每个实例有source_*、*_kernel_certificate、source_ZF_*及native_*，后者返回真实
FirstOrder.Derives nativeZF [] (Translation.sentence 相应闭句)。
统一有限理论只含Extensionality、Foundation、Pairing、Union及separation(agreementMatrix.neg)。
实际扩展存在只需前四句；唯一纤维沿用对象归纳矩阵的一个分离实例。未声称五句是每个模式的最小必要公理集。
未输入Replacement、Collection、PowerSet、Infinity、EmptySet或对象AC；Total/Deterministic是明确对象前提。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成223个任务。
19源规则、9类源ZF及锁定SHA检查通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1538个声明：131个无公理依赖，1407个记录允许依赖；0条Lean警告。
新增87个审计声明，其中5个无公理依赖；六个有限理论kernel_certificate依赖均逐项核对为propext/Classical.choice/Quot.sound。
原生ZF回放仍继承底座七个固定公理句子FreeClosed证书的native_decide.ax_1基线，未新增自定义公理。
190个验收文件哈希重新核对一致；没有新增sorry/admit、unsafe或外部良基/标准性输入。
CheckStep3检验任意矩阵六模式、两个参数交错量词矩阵、无参数实例、旧域限制及原Replacement纤维接口。
verification/保留实际命令、日志、依赖和源码哈希；未推送远端。

## 全目标仍未完成
本批从给定实际旧图或旧图存在证明构造后继图；没有证明全部内部序数域上已经存在递归图。
下一项在P(α):=Ord(α)→RecursorExists(α)的对象集合归纳步里，Replacement收集所有β∈α的实际唯一后继图，
再以相容图族并校验精确域α与每个历史方程。该收集、合并和全归纳尚未实现。
秩/累积层、反向完整Collection、两种AC等价、内部ProofZF/U/Con完整AST、任意内部码的编译器正确性、
对象解释/对称强迫以及最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建和Comparator仍未运行；PP/AC相对一致性最终定理未完成。
