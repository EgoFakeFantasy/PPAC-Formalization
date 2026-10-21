# 加法代数与数值下界的对象推导验收
日期：2026-10-21；基点b9ec90e9760b643abb1026ee0ed3f4ef94dd377f；分支migration/yesmeta-step3。

## 对象层范围与背景
沿用原纯等词/成员语言、Replacement版源ZF及已证双向呈现对应后的原nativeZF。
结论均由原FirstOrder.Derives/HilbertDerivation验收；未修改原核、固定依赖或可信基。
本批完成流程4b.b.2a的加法代数及基本顺序界。乘法代数、次序差分、完整编码界仍待完成。
最终要求仍为Derives B [] (Con_ZF→Con_target)，内部ProofZF/U及该主句尚未实现。

## 九个实际原核闭句
以Add(w,a,n,y)表示此前已经证明存在唯一的内部自然数和。
所有句子保留Omega(w)、内部加数/输出及实际和值见证的完整对象量词。
表内自然数均指内部w的成员，含非标准内部自然数；不是Lean.Nat逐个标准实例。

| 接口 | 完整闭句的数学内容 |
|---|---|
| ObjectNaturalAdditionAlgebra.leftSuccessorSentence | 自然a,n及Succ(b,a)、Add(a,n,y)下，Add(b,n,z)当且仅当Succ(z,y) |
| commutativeSentence | 自然a,n下，Add(a,n,y)当且仅当Add(n,a,y) |
| associativeSentence | 自然a,b,n及Add(a,b,u)、Add(b,n,v)下，Add(u,n,y)当且仅当Add(a,v,y) |
| cancelRightSentence | 自然a,b,n下，Add(a,n,y)与Add(b,n,y)推出a=b |
| cancelLeftSentence | 自然a,b,n下，Add(n,a,y)与Add(n,b,y)推出a=b |
| ObjectNaturalAdditionOrder.boundsSentence | 自然a,n及Add(a,n,y)下，(a=y∨a∈y)∧(n=y∨n∈y) |
| zeroSentence | 在同样前提下，Empty(y)当且仅当Empty(a)∧Empty(n) |
| strictRightSentence | 在同样前提下，¬Empty(n)推出a∈y |
| strictLeftSentence | 在同样前提下，¬Empty(a)推出n∈y |

每个句子均有source_*、*_kernel_certificate和native_*实际证书。
核心类型为Derives ZFEquivalence.sourceZF [] (Translation.sentence sentence)，
最终接口为Derives nativeZF [] (Translation.sentence sentence)，没有未证分离、递归或算术假设参数。
顺序记号below(a,y)严格定义为对象等词/成员析取a=y∨a∈y，不是宿主比较。

## 实际归纳和见证工程
NaturalAdditionTransport给左参数/索引等词替换及三/四参数映射的原rename接口。
NaturalAdditionShift在全部内部n上归纳：后继步实际取得旧和t，
旧/新和的后继律给Succ(y,t)，由归纳假设取得b+n=y，再由下一后继得到新和。
逆向左后继刻画实际取得y的后继，并以原和值唯一性和eqSubst对齐。

NaturalAdditionCommutative的零点使用已证0+a=a；后继步实际取得旧和，
应用交换归纳假设，再用左参数后继律取得交换后的新和。
NaturalAdditionAssociative固定实际a+b=u，归纳第三加数n。
后继步实际取得b+n和u+n两个旧和，归纳假设给出正确括号后的旧和，
再由两个真实后继和值推出新的结合关系；逆向通过实际和存在与唯一性完成。

NaturalAdditionCancellation归纳公共右加数n，实际取得两个旧和x,z。
两个新和相等使x,z有同一个原后继；从x∈ω取得与原单射接口严格匹配的成员传递性，
Foundation/Pairing给不自属，由原后继单射得到x=z，再应用归纳假设。
原OrdinalSyntax.transitiveSet与OmegaStructureSyntax.transitive的AST不同，
实现明确使用已经证明的elements_transitive/element_transitive_at，不作未经证明的定义同一化。
左抵消由已证交换律和右抵消正式组合。

NaturalAdditionBounds以内部ω归纳证明左加数等于或属于实际和值。
后继步消去实际旧和见证，原Succ的精确成员关系将旧下界送入新和值；交换律给另一侧界。
NaturalAdditionOrderLaws对内部非零加数实际取得自然前驱，再取得旧和及其真实后继，给严格成员界。
和值为空的前向由两个下界排除成员分支，反向由原零点律及eqSubst得到。
这些证明只使用原源规则；中间递归闭句和每个明确Separation实例在source_*端点由原ZF消去。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成351个任务。
Check、CheckStep2、CheckStep3、CheckStep4与Audit全部以--trust=0通过。
2822项显式声明审计：198项无公理依赖，2624项记录允许依赖；0条警告。
新增10个模块、129项显式审计，其中1项无公理依赖；320个验收文件SHA256实际复核一致，差异0。
九个新核心证书依赖均恰为propext/Classical.choice/Quot.sound。
verify.py现逐项强制核对累计十九个算术核心证书及其native端点：
源核心恰为标准三项；原nativeZF端点恰为这三项加七个既有闭性证书。
未扩大原choice额外证书限域；两份可信基JSON与lake-manifest.json未改。
上述Lean证书依赖不是向对象ZF增加AC。未新增自定义公理、sorry/admit、unsafe或native_decide。
原19条源规则和九类源ZF原文锁定核对通过；CheckStep4直接检查顺序界AST与九个闭句端点。
日志、依赖与哈希仅保留本地verification/；未推送GitHub。

## 剩余主线
本批不把加法代数和基本下界升级为完整自然数算术或编码正确性。
下一项为4b.b.2b：乘法交换/结合/分配、进一步自然次序/差分和配数界，再实现原Gödel配数/结构列表码。
full_natural_addition_and_multiplication、专用ProofZF/U检查器、任意内部码正确性与最终Con标志仍为False。
内部编译器、实际对称强迫、构造模型和最终一致性蕴含仍未完成；原OpenAI构建及Comparator仍未运行。
