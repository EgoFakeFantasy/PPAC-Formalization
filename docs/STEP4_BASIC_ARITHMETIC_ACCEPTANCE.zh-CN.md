# 全内部自然数基本加乘的对象推导验收
日期：2026-10-21；基点ff58995fc4c063762e24320c3e0a9b085a12e5c6；分支migration/yesmeta-step3。

## 对象语言、背景与交付端点
仍使用纯等词/成员语言；背景为原Replacement版源ZF，经已经证明的理论传输回放到原nativeZF。
原推导核FirstOrder.Derives/HilbertDerivation保持不变。最终Con_ZF→Con_target主句尚未证明。
本批完成工程流程4b.b.1：实际自然值、唯一性、ω闭包、零点、双向后继和左零律。
交换/结合/分配、抵消、次序和编码界性质属于4b.b.2，尚未完成。

两个完整接口分别为ObjectNaturalAddition和ObjectNaturalMultiplication。
每个接口均有fiber、closure、zero、successor、leftZero五个完整闭句，
并提供source_*、*_kernel_certificate及native_*实际推导。
原核端点类型为FirstOrder.Derives nativeZF [] (Translation.sentence sentence)。
句子中全部自然数参数、输出与递推图见证都是内部对象量词，覆盖非标准内部ω成员。
没有用Lean.Nat递归计算、有限样本或任意模型语义定理替代原核证书。

## 实际递推、值域和前段对齐
NaturalEvaluationRange证明：若初值属于b且原步进关系的全部输出属于b，
则每个实际递推末值都属于b。证明消去真实历史与算子见证，不增加范围结论假设。
NaturalSuccessorStep在内部ω输入上使用原Succ，ω外输入返回实际空集。
其对象总性、单值性、全输出在ω内，以及自然输入时严格给出原Succ均已证明。
总化是为了适配任意有效历史上的原递归定理；自然数上的算术方程仍严格为原后继。

NaturalEvaluationStep从实际后继图中构造原前段限制递归图，读取真实旧输出，
通过已经证明的唯一末值与独立旧求值对齐，取得两次实际求值间的步进关系。
没有假定两个独立存在量化的历史图直接相同。
ArithmeticContext.Evidence仅包装Extensionality/Pairing/Union/Foundation及三个明确Separation证书。
中间使用的完整递归证书另有hAdd/hMul参数，最终source_*端点通过已经证明的
NaturalRecursion.source_uniqueness闭句实际消去；不把算术/递归结论放入背景字段。
因此上述七个局部证书并不是声称足够证明全部递归存在的有限背景；最终源背景仍为完整ZF。

## 加法五个完整闭句
Add(w,a,n,y)由初值a和自然后继步进的实际原递归图定义。
在Omega(w)、a∈w及n∈w下：

| 闭句 | 数学内容 |
|---|---|
| fiberSentence | ∃y∈w Add(w,a,n,y)，且任何满足Add的输出等于y |
| closureSentence | a∈w且Add(w,a,n,y)蕴含y∈w；此范围结论不需要n∈w |
| zeroSentence | Empty(z)下，Add(w,a,z,y)当且仅当y=a |
| successorSentence | Succ(s,n)且Add(w,a,n,y)下，Add(w,a,s,z)当且仅当Succ(z,y) |
| leftZeroSentence | Empty(z)下，∀n∈w Add(w,z,n,n)，通过对象ω归纳证明 |

## 乘法五个完整闭句
Mul(w,a,n,y)显式定义为∃e(Empty(e)∧Eval(AddStep,w,e,n,y))。
AddStep在自然累积值x上严格为Add(w,x,a,y)，在ω外输入返回实际空集。
其对象总性和单值性由实际加法存在唯一性证明。
不同实际零见证先由原Extensionality证明相等，再通过原eqSubst传输初值；不固定宿主零对象。

| 闭句 | 数学内容 |
|---|---|
| fiberSentence | Omega(w)、a,n∈w下存在唯一实际自然数积 |
| closureSentence | Omega(w)及实际Mul蕴含输出在w中；公开闭句保留a∈w这一统一接口前提 |
| zeroSentence | Empty(n)下，Mul(w,a,n,y)当且仅当Empty(y) |
| successorSentence | Succ(s,n)且Mul(w,a,n,y)下，Mul(w,a,s,z)当且仅当Add(w,y,a,z) |
| leftZeroSentence | Empty(z)下，∀n∈w Mul(w,z,n,z)，通过对象ω归纳证明 |

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成341个任务。
Check、CheckStep2、CheckStep3、CheckStep4及Audit均以--trust=0通过。
2693项显式审计：197项无公理依赖，2496项记录允许依赖；0条警告。
本批新增15个模块及149项显式审计。310个验收文件的SHA256实际复核一致，差异0。
十个新增源核心原核证书的依赖均恰为propext/Classical.choice/Quot.sound；verify.py逐项强制检查。
十个nativeZF端点各依赖上述三项和原七个闭性证书，未扩大可信基。
这份Lean证明证书依赖清单不等于向对象理论增加AC。
两份可信基JSON、固定YesMetaZFC依赖及原核保持不变；原choice额外证书仍仅限旧桥接范围。
无sorry/admit、unsafe、native_decide或新增自定义公理；原19规则和九类源ZF锁定核对通过。
CheckStep4直接检查乘法内部零初值AST、两个总化步的自然输入接合及十个原nativeZF闭句类型。
日志、依赖与哈希仅保留本地verification/；没有推送GitHub。

## 后续完成门
基本加乘的六个精确进度标志为True；full_natural_addition_and_multiplication仍为False，
原因是代数、次序及编码界尚未完成，不能把基本递推律升级为所有算术义务已结束。
下一项为4b.b.2的加法/乘法代数与必要次序界，再实现4b.c原Gödel配数/结构码。
内部语法码正确性、专用ProofZF/U检查器、内部编译器、实际对称强迫与最终Con蕴含均未完成。
原OpenAI完整构建和Comparator仍未运行；本批不构成PP/AC分离主定理或最终相对一致性证明。
