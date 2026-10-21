# 内部自然递推及具体后继迭代的对象推导验收
日期：2026-10-21；基点e61c71e330811abf5e7b0e3685b9ac91de4bd3e3；分支migration/yesmeta-step3。

## 对象层终点与范围
对象语言仍为纯等词/成员语言，使用原FirstOrder.Derives/HilbertDerivation。
本批完成通用自然递推前置及真实后继迭代；最终Con_ZF→Con_target主句尚未完成。
没有把宿主递归函数、语义模型或结构字段中假定的递推存在作为交付。

ObjectNaturalRecursion.native_proof对每个任意参数纯公式p给出原nativeZF中的完整闭句证书，数学内容为：
∀参数,w,a[Omega(w)→Total(p)→Functional(p)→∀n∈w∃!y Eval(p,w,a,n,y)]。
Total(p)与Functional(p)量化全部内部集合，不是Lean函数类型。
外部模式索引只描述固定有限公式及其参数数目；每个实例量化全部内部自然索引，含非标准ω成员。
这不是统一内部真值谓词，也不是全部内部语法码的检查正确性。

## 算子及实际原递归图
OmegaOrdinals通过对象ω归纳证明全部内部ω成员满足原完整ordinal定义，
仅需Foundation与一个正文ordinal的完整Separation实例，提供有限背景及原核闭句。

对任意内部索引x、任意完整历史图h与初值a，NaturalRecursionSyntax.operation定义：
- 若存在t∈w且Succ(x,t)，则实际取得u使Edge(h,t,u)，并要求原p(u,y)；
- 若不存在这样的内部前驱，则y=a。

NaturalRecursionTotal由原FunctionOn取得真实历史输出，再由对象Total(p)取得真实下一值。
没有假定历史已经符合递推；算子总性在每个有效序数/完整历史上均已证明。
NaturalRecursionDeterminism由内部ω成员传递性、后继消去、原图单值性及Functional(p)证明算子单值。
前驱和历史值全部通过原exE消去，没有抽取宿主选择函数。
默认分支与前驱分支由同一对象前驱公式严格排斥。

NaturalRecursion实际消去两项义务，再实例化已验收ObjectTransfiniteRecursion：
取得全部内部原序数域上的实际完整Recursor存在唯一。
Total、deterministic、existence、uniqueness四个完整模式都有源ZF与原核证书；
不是只建立算子AST或保留未证算子字段。
源背景为原Replacement版ZF，nativeZF回放使用此前已证Collection/Replacement完整对应。
没有额外对象AC、不可达、外部良基或ω标准性前提。

## 每个内部自然索引的实际唯一末值
NaturalEvaluationSyntax.Eval显式存在量化实际域d和实际图f，并要求：
Succ(d,n) ∧ 原完整Recursor(f,d) ∧ Edge(f,n,y)。
原Recursor保留完整entriesOn/totalOn和每一步实际前段限制历史。
NaturalEvaluationExistence从Omega(w)实际取得d∈w，再由其原序数性质及真实唯一递归图取得完整函数值。
NaturalEvaluationUniqueness对两组真实见证证明后继域相等，将原递归图传至同一域，
消去实际唯一递归图纤维并以原图单值性推出末值相等。
NaturalEvaluationFiber将真实存在与唯一性组合成完整内部唯一末值公式。
这些证明覆盖每个内部n∈ω，不局限于外部标准自然数实例。

NaturalRecursionLaws另外证明：零索引无自然前驱，故实际零点求值等于初值；
对真实后继索引和完整历史，算子严格满足原步进关系。
参数映射的抬升、投影及标准恒等映射均显式证明，避免靠展开巨大AST匹配参数。

## 实际具体实例
SuccessorRecursion.stepMatrix严格为原Succ(output,input)关系。
Pairing和Union实际证明其对任意内部集合输入的输出存在，Extensionality证明输出唯一。
因此具体实例不再接受待证Total/Functional字段，直接给出：
∀w,a[Omega(w)→∀n∈w∃!y Eval(Succ,w,a,n,y)]。
其zeroSentence给Empty(z)与实际Eval(Succ,w,a,z,y)推出y=a。
两个完整原核闭句由SuccessorRecursion.native_proof/native_zero验收。

这批没有证明所有输出都属于ω，也没有把该实例改名为完整自然加法定理。
下一项仍须证明ω值域闭包、完整加法零/后继规律及乘法，再实现Gödel配数和结构码。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，9条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成326个任务。
Check、CheckStep2、CheckStep3、CheckStep4及Audit均以--trust=0通过。
2544项审计：194项无公理依赖、2350项记录允许依赖；0条警告。
新增110项显式审计，其中1项无公理依赖。295个验收文件SHA256实际复核一致。
八个新增源核心原核证书恰为propext/Classical.choice/Quot.sound；
对应原nativeZF端点仍按七个既有闭性证书基线审计，没有新增活跃证书种类。
原choice额外证书仍仅限旧桥接命名空间及原声明，两份可信基JSON未修改。
无sorry/admit、unsafe或新增自定义公理；19条源规则和9类源ZF的原文锁定核对通过。
CheckStep4直接检查全对象总性AST、算子矩阵接合、通用原核模式及已消去义务的后继实例。
日志、依赖、哈希保留本地verification/；没有推送GitHub。

## 最终完成门保持不变
完整自然加法/乘法、内部Gödel/结构码正确性、专用ProofZF/U检查器AST与任意内部码正确性均仍为False。
内部解释、实际对称强迫、模型应用及最终Derives B [] (Con_ZF→Con_target)仍未完成。
原OpenAI构建和Comparator仍未运行；不据本批递推结果宣称PP/AC分离或最终相对一致性已经完成。
