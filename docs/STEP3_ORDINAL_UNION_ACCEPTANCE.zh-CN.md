# 任意内部序数族的并、最小上界与严格上界验收
日期：2026-10-21；基点cee7d34cef5b40f4e023a0d3c5a4b6764474d6cb。
分支migration/yesmeta-step3；递归/秩及最终内部Con主句仍未完成。

## 全对象量词和原序数定义
Ord沿用与原Source.ordinal严格rfl相同的OrdinalSyntax.ordinal；原传递性、成员严格线性及全部内部非空子集极小元条件保持不变。
Ordinals(c) := ∀a(a∈c→Ord(a))；c是任意内部集合，允许为空，不要求外部有限、可数或已给序数界。
UpperBound(c,b) := ∀a(a∈c→a⊆b)。
LeastUpper(u,c) := UpperBound(c,u) ∧ ∀b(UpperBound(c,b)→u⊆b)。
最小性量化全部内部集合b，不把比较范围偷偷缩成原序数上界。
StrictUpper(c,b) := ∀a(a∈c→a∈b)，严格界要求成员关系，不以子集关系代替。
全部实际存在见证由源exI/exE处理，并回放为原YesMetaZFC FirstOrder.Derives证书；未使用宿主Ordinal或外部WellFounded。

## 序数集合的线性与传递装配
OrdinalFamilyOrder对任意Ordinals(c)证明原irreflexive、membershipTransitive、comparable三项。
成员x本身是原序数给x∉x；若x∈y∈z且z∈c，原Ord(z)的传递性给x∈z；
c的任意两个成员均为原序数，应用上批任意两序数比较取得原线性分支。
因此，若c还传递，由原Foundation给全内部子集极小元条件，得到完整原Ord(c)。
线性装配没有假设c非空，也未调用宿主集合论分类。

## 实际族并的对象证明
给定原UnionOf(u,c)及Ordinals(c)，若x∈u，原Union句子提供实际a∈c且x∈a。
原Ord(a)的成员闭包给Ord(x)；若再有y∈x，原a传递给y∈a，再用同一个Union见证得y∈u。
OrdinalUnion因此证明u传递且其成员全为原序数，并由上项装配原Ord(u)。
原Union公理提供实际u，故有完整对象∃u[UnionOf(u,c)∧Ord(u)∧LeastUpper(u,c)]。

UnionUpperBounds的最小性更一般：任意内部集合族的并都是最小包含上界，不要求族成员是序数。
a∈c给a⊆u；若UpperBound(c,b)，对x∈u消去实际a∈c、x∈a见证，由a⊆b给x∈b，故u⊆b。
两个LeastUpper见证互相包含，原Extensionality给实际集合相等。

OrdinalStrictBound以原Pairing/Union取得该实际u的后继s，再由上批后继保持性取得Ord(s)。
每个a∈c满足Ord(a)且a⊆u；原初段性质给a=u∨a∈u。
前者由u∈s和相等替换得a∈s，后者由后继旧成员包含得a∈s。
所以实际得到∃s[Ord(s)∧∀a∈c a∈s]。全族范围包含空族；不需要选择一个宿主上界。

## 六条完整闭句和实际理论
ObjectOrdinalUnion.assumptions只含Extensionality、Foundation、Union和正文x∉b的一个Separation实例。
strictAssumptions在这四句上只增加Pairing。

| 闭句 | 对象内容 | 有限理论 |
|---|---|---|
| familySentence | ∀c[Transitive(c)→Ordinals(c)→Ord(c)] | 四句理论 |
| unionSentence | ∀c,u[Ordinals(c)→UnionOf(u,c)→Ord(u)] | 四句理论 |
| leastSentence | ∀c,u[UnionOf(u,c)→LeastUpper(u,c)] | 四句理论 |
| uniqueSentence | ∀u,v,c[LeastUpper(u,c)→LeastUpper(v,c)→u=v] | 四句理论 |
| existenceSentence | ∀c[Ordinals(c)→∃u(UnionOf(u,c)∧Ord(u)∧LeastUpper(u,c))] | 四句理论 |
| strictSentence | ∀c[Ordinals(c)→∃b(Ord(b)∧StrictUpper(c,b))] | 加Pairing的五句理论 |

每句均有source_*、*_kernel_certificate、source_ZF_*及native_*。
有限理论证书未输入Replacement、Collection、PowerSet、Infinity、EmptySet或对象AC。
部分闭句只用该有限理论的更小子集；这里没有宣称四/五句是每个闭句的必要最小公理集。
六个kernel_certificate依赖清单均只有propext、Classical.choice、Quot.sound。
nativeZF回放仍继承原底座七个固定句子FreeClosed证书的native_decide.ax_1基线，不误报成仅三项标准依赖。
CheckStep3直接检查原Source.ordinal的族并闭句、全部内部集合上界量词、严格成员上界及四/五句理论证书。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1，LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成206个任务。
19源规则、9类源ZF公理、锁定源SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1383个声明：124个无公理依赖，1259个记录允许依赖；0条Lean警告。
新增71个审计声明，其中6个无公理依赖；六个新增有限理论kernel_certificate的依赖已逐项核对。
173个文件的实际验收哈希复核一致。没有新增sorry/admit、自定义公理或外部良基/标准性前提。
verification/保留实际命令、日志、依赖和源码哈希；未推送远端。

## 尚未完成
下一项是任意参数递推公式在全部内部序数初段上的实际完整函数图递归，须证明相容性和存在唯一；
这批实际上界没有替代递归、秩覆盖或Vα存在证明。
全局ω函数图、最小传递闭包、反向完整Collection、两种AC等价、内部ProofZF/U/Con完整AST及
任意内部码的编译器正确性、对象解释/对称强迫和最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建与Comparator仍未运行，PP/AC相对一致性最终定理未完成。
