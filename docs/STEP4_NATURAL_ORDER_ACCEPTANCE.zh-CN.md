# 自然差分、加乘顺序和基本数值界的对象推导验收
日期：2026-10-22；基点2623a200e79c46b0fb26140eab9107ffc3d9ad43；分支migration/yesmeta-step3。

## 对象背景与本批范围
沿用原纯等词/成员语言、完整Replacement版源ZF和原FirstOrder.Derives/HilbertDerivation。
所有最终闭句均实际传输到原nativeZF，未修改内核、固定依赖或可信基。
本批完成自然差分与次序、加乘顺序及基本因子/平方界，共二十六个完整闭句。
全部自然输入、差值、旧积、后继与中间值均为内部对象量词，包含非标准内部ω成员。
最终内部Con_ZF→Con_target、专用ProofZF/U及任意内部码正确性仍未实现。

## 四个顺序基础闭句
ObjectNaturalOrder提供total、transitive、antisymmetric和successor四个句子。
顺序below(a,b)始终严格为a=b∨a∈b。前三句覆盖内部自然数的全序、传递与反对称。
successorSentence对任意实际Succ(s,b)给a∈s↔below(a,b)，该逻辑刻画不额外假设自然性。
全序使用已证原序数比较；传递/反对称使用原成员传递和不自属，未用宿主比较或外部良基。

## 四个实际差分闭句
NaturalDifferenceSyntax.witness(w,a,b,d)严格为d∈w∧Add(w,a,d,b)。
existsDifference为该见证的内部存在量词；fiber还要求任何同样满足此见证的内部候选e等于d。
因此唯一性始终包含e∈w，不声称ω外索引也唯一。
positiveWitness另外要求¬Empty(d)。

| ObjectNaturalDifference端点 | 完整数学内容（均保留Omega及内部自然输入） |
|---|---|
| orderSentence | below(a,b)↔∃d∈w Add(a,d,b) |
| fiberSentence | below(a,b)下实际存在唯一自然差值；每个唯一性候选也属于w |
| strictSentence | a∈b↔∃d∈w(¬Empty(d)∧Add(a,d,b)) |
| zeroSentence | 实际自然差值Add(a,d,b)下，Empty(d)↔a=b |

存在性在内部上界b上作对象ω归纳。空上界排除成员分支；后继上界的成员分支先得到旧次序，
从归纳假设取得实际自然差值d，再实际取得Succ(e,d)，由加法后继律构造新差值e。
相等分支实际取得内部零差值。唯一性调用此前已证两侧加法抵消。
严格差分的非零性由原零点律和不自属推出；反向由实际正加数严格界取得。

## 四个加法顺序闭句
ObjectNaturalAdditiveOrder的rightWeak/rightStrict/leftWeak/leftStrict分别给出两侧平移对弱/严格顺序的等价。
例如Add(a,n,x)、Add(b,n,y)下，below(a,b)↔below(x,y)，且a∈b↔x∈y。
保持性实际取得自然差值d，三项重排证明Add(x,d,y)，再应用实际下界或正加数严格界。
反射使用原自然三歧比较；相反严格分支会在平移后形成非法成员逆序；相等分支以和值唯一性消去。
左右输入通过已证交换律连接，没有把结果降为宿主函数的单调性。

## 九个乘法顺序闭句
ObjectNaturalMultiplicativeOrder提供以下实际句子：

| 端点 | 对象结论与边界 |
|---|---|
| zeroSentence | 实际自然乘积p=a*n下，Empty(p)↔Empty(a)∨Empty(n) |
| rightMonotoneSentence、leftMonotoneSentence | 两侧弱单调，包含公共乘数为零的情况 |
| rightWeakSentence、leftWeakSentence | 公共乘数非零时，弱顺序保持且反映 |
| rightStrictSentence、leftStrictSentence | 公共乘数非零时，严格成员顺序保持且反映 |
| rightCancelSentence、leftCancelSentence | 公共乘数非零时，两个实际乘积相同推出两个因子相同 |

非零乘积证明实际取得非零自然乘数的前驱和旧积；后继乘积是旧积加非零因子，故有真实成员，不能为空。
乘法单调性实际取得输入差值d，再实际取得d*n；两侧分配给出乘积输出间的真实加法差值。
严格情形证明d*n非零，再取正差分严格界。反射利用原三歧比较排除相反严格分支。
公共乘数非零前提属于公开闭句；没有把零乘数纳入反射或消去等价。

## 五个数值基础界闭句
ObjectNaturalNumericBounds提供unit、factors、square、squareStrict、squareInjective。
实际Empty(z)、Succ(e,z)下，非零自然n当且仅当below(e,n)，即至少为内部一。
该证明实际取得n的前驱，使用0+t=t、加一后继式及加法单调。
两个因子都非零时，两者均不大于实际乘积；内部零/一见证在证明内实际取得并消去。
平方下界覆盖零；平方严格单调实际取得中间积a*b，通过弱/严格乘法单调和成员传递连接两个平方。
平方单射由原自然三歧比较与平方严格单调推出。
这些是原配数的数值基础，不是原配数本身的单射、解码或全部编码界已经证明。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成383个任务。
Check、CheckStep2、CheckStep3、CheckStep4与Audit均以--trust=0通过。
3134项显式声明审计：198项无公理依赖、2936项记录允许依赖；0条警告。
本批新增15个模块、185项显式审计；352个验收文件SHA256实际复核一致，差异0。
二十六个新sourceZF核心原核证书均恰为propext/Classical.choice/Quot.sound。
verify.py精确核对累计五十三个算术/顺序核心证书及其native端点：
源核心恰为标准三项，原nativeZF端点恰为这三项加七个原有闭性证书。
原choice额外证书限域、两份可信基JSON、固定依赖与原核未变；该可信基记录不向对象ZF增加AC。
未新增自定义公理、sorry/admit、unsafe或native_decide；原19规则及九类源ZF锁定核对通过。
CheckStep4显式核对自然差值见证和唯一候选的ω范围、正公共乘数公开前提以及二十六个原核闭句端点。
日志、依赖与哈希仅保留本地verification/；未推送GitHub。

## 原配数核对与下一项
已读取固定底座ProofT/ZFC/InternalPairingRules.lean的分支多项式：
a∈b时为b²+a，其余为(a²+a)+b。LanguageEncoding.lean的原结构列/节点均使用同一配数及后继封装。
这里只核对数值约定，未调用该文件的intrinsic_zfc_theory模型语义定理作为当前ZF证明。
下一项按流程4b.c建立纯ℒ配数关系，实际证明全内部自然数上的总单值、分量界、单射与唯一解码，
再构造原结构码及其正确性，保留空结构列数值1、叶0数值2约定。
原配数专门界、Gödel/结构码、专用ProofZF/U、内部编译器、构造解释与实际对称强迫仍待实现。
最终内部Con句仍未证明；原OpenAI完整构建和Comparator仍未运行。
