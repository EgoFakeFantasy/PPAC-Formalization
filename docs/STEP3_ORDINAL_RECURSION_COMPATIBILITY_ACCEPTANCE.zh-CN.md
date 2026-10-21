# 任意参数递归图的前段限制、相容与唯一模式验收
日期：2026-10-21；基点a1621d2d59e5ff16fa1a872da55ca128aa7637bc。
分支migration/yesmeta-step3；全部内部序数上递归图的实际存在和最终Con主句仍未完成。

## 对象目标和公式索引
每个p : Source.Formula(n+3)给一个递推矩阵Φ，n个参数及最后三槽x、h、y均为对象变量。
外部n仅描述有限公式的参数数目，p是合法模式索引；并非内部统一真值谓词或只枚举外部标准序数。
Operator(p,ρ,x,h,y)通过末变量重命名实例化p。
History(p,ρ,f,x,y) := ∃h[Restrict(h,f,x)∧Operator(p,ρ,x,h,y)]。
Equations(p,ρ,f,d) := ∀x[x∈d→∀y(Edge(f,x,y)→History(p,ρ,f,x,y))]。
Recursor(p,ρ,f,d) := FunctionOn(f,d)∧Equations(p,ρ,f,d)。
FunctionOn严格使用原完整entriesOn及总单值性；历史h是内部实际集合，不是宿主函数或假设给定的选择族。
Deterministic(p,ρ) := ∀x,h[(Ord(x)∧FunctionOn(h,x))→∀u,v(Φ(x,h,u)→Φ(x,h,v)→u=v)]。
Ord严格沿用原Source.ordinal；单值性只要求有效的原序数索引和完整前段图，不要求无效输入上单值。
本批未假定算子总性，也未宣称已经构造每个内部序数域上的递归图。

## 前段限制保持和实际存在
若x⊆b、Restrict(g,f,b)且Restrict(h,f,x)，RestrictionHistory.through逐成员证明Restrict(h,g,x)。
正向用x⊆b将合法输入编码从x传到b；反向由g成员必为f成员取得。无需重新构造或选择历史h。
若b传递且b⊆d，则每个x∈b满足x⊆b，g的输出边是f的输出边。
f的递推条件提供实际h及Φ(x,h,y)，同一h在g上仍是所需限制，因此g保留完整递推条件。
RestrictionFunction保留完整FunctionOn，得到Recursor(g,b)。
一个原Separation实例以entryOn为正文实际取得Restrict(g,f,b)的集合g，故实际取得
∃g[Restrict(g,f,b)∧Recursor(g,b)]。此处以前提中的实际Recursor(f,d)为条件。

## 历史相等、当前输出相等和全部内部位置相容
复用agreementMatrix的CommonAt(f,g,d,e,x)：x∈d→x∈e→AgreesAt(f,g,x)。
BelowAgreement是该矩阵在d中的有界成员归纳前提。
设h、k分别为f、g在x上的实际限制，来自h、k的任意输出边都转为f、g的边；
完整FunctionOn的精确域性质给其输入在d、e中，限制给输入属于x。
较小位置归纳前提因此给这两条输出相等。用完整图逐边外延性得实际集合h=k，不能省略entriesOn排除杂项的条件。
原等词规则把Φ(x,k,v)沿h=k转为Φ(x,h,v)，有效历史上的单值性与Φ(x,h,u)给u=v。
对原序数域d,e，任意共同x属于两个域且是原序数，两个实际历史均为x上的完整函数图，单值性的有效性前提因此实际成立。
OrdinalRecursionCompatibility以agreementMatrix在实际集合d上应用原BoundedInduction，
覆盖所有内部x∈d；再由边的精确域性质取得任意共同边相容，最后同域图外延性给f=g。
未使用宿主WellFounded、外部标准序数、可数性或宿主数据选择。

## 四个模式的完整对象闭句
对每个任意p及参数数目，ObjectOrdinalRecursion均关闭全部参数和显示的图/域变量：

| 模式 | 完整对象结论概要 |
|---|---|
| preservationSentence p | Transitive(b)→b⊆d→Restrict(g,f,b)→Recursor(f,d)→Recursor(g,b) |
| restrictionSentence p | Transitive(b)→b⊆d→Recursor(f,d)→∃g(Restrict(g,f,b)∧Recursor(g,b)) |
| compatibilitySentence p | Deterministic(p)→Ord(d)→Ord(e)→Recursor(f,d)→Recursor(g,e)→Agrees(f,g) |
| uniquenessSentence p | Deterministic(p)→Ord(d)→Recursor(f,d)→Recursor(g,d)→f=g |

每个实例都有source_*、*_kernel_certificate、source_ZF_*及native_*，后者返回实际
FirstOrder.Derives nativeZF [] (Translation.sentence 相应闭句)。
有限理论只含Extensionality、Foundation、separation(agreementMatrix.neg)及separation(RestrictionSyntax.matrix)。
限制保持本身只用原逻辑规则；实际受限图只用一个分离实例；相容/唯一使用外延、Foundation和归纳矩阵的分离实例。
没有把给定递归图、算子单值性或共同前段相容性加入新的理论公理，它们都是明确的对象蕴含前提或已经证明的中间结论。
没有Replacement、Collection、对象AC、Infinity或额外外部良基前提。

## 实际验收和信任边界
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1，LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成214个任务。
19源规则、9类源ZF及锁定SHA检查通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1451个声明：126个无公理依赖，1325个记录允许依赖；0条Lean警告。
新增68个审计声明，其中2个无公理依赖；四个模式的有限理论原核证书依赖逐项核对为propext/Classical.choice/Quot.sound。
原生ZF回放继续继承底座七个固定句子FreeClosed证书的native_decide.ax_1基线，未增加自定义公理。
181个验收文件哈希复核一致；没有新增sorry/admit、unsafe或外部良基/标准性输入。
CheckStep3检验全部任意矩阵接口、两个参数且有交错量词的矩阵实例、无参数实例及原完整FunctionOn对应。
定向编译补全显式RestrictionAlgebra导入；进步性大型对象公式化简局部使用maxHeartbeats=800000，
这只提高该证明的 elaboration 预算，不改变对象规则、信任等级或公理输入；最终完整验收通过。
verification/保留实际命令、日志、依赖和源码哈希；未推送远端。

## 未完成和下一项
全部内部序数上递归图的实际存在模式仍未完成。本批相容/唯一以前提中实际图为条件，不能替代存在唯一递归定理。
下一项需定义有效历史上的总性，实际取得当前输出、构造后继域图并检查全部递推方程；
再在对象集合归纳中用Replacement收集唯一扩展图，以已证相容族并构造任意内部序数域上的实际完整递归图。
秩/累积层、反向完整Collection、两种AC呈现、内部ProofZF/U/Con完整AST、任意内部码的编译器正确性、
对象解释/对称强迫及最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建和Comparator仍未运行；PP/AC相对一致性最终定理未完成。
