# 任意原对象序数三歧比较验收
日期：2026-10-21；基点773fbada5dab4a27b4991cf565b0d20efc72a903。
分支migration/yesmeta-step3；内部递归/秩和最终Con主句仍未完成。

## 对象合同
对象语言仍为单排序纯成员/等词语言；ordinal沿用与原Source.ordinal严格rfl相同的OrdinalSyntax.ordinal。
原传递性、成员严格线性和对全部内部非空子集的成员极小元条件均保持不变。
本批新增的所有集合参数、差元、序数和子集均在对象公式中量化；不用宿主Ordinal、WellFounded或外部标准性。
终点是实际FirstOrder.Derives nativeZF [] (Translation.sentence 相应闭句)，不是模型语义或宿主分类定理。

## 有界差元与初段证明
OrdinalDifference.outsideMatrix : Formula 2精确为x∉b，参数b和正文变量x均是对象变量。
Difference(a,b,x) := x∈a ∧ x∉b。
Minimal(a,b,u) := Difference(a,b,u) ∧ ∀y(Difference(a,b,y)→y∉u)。
由¬(a⊆b)用原经典逻辑规则证明∃x Difference(a,b,x)；BoundedMinimal在实际界a上用
正文x∉b的一个原Separation实例和Foundation取得实际成员极小见证u。
若a传递，y∈u给y∈a；若y∉b，差性质与u极小性矛盾，因此u⊆b。
这是有界差性质，故没有调用已证传递覆盖或Replacement来获得无界极小元。

OrdinalInitialSegment假定Ord(a)、b传递且b⊆a。
若a⊆b，由Extensionality得到b=a；否则取差性质的成员极小元u。
已有u⊆b；对任意v∈b，v与u均属于a，使用a内部原比较条件：
- v=u会得到u∈b，违反差性质。
- v∈u是所需结论。
- u∈v由b传递且v∈b推出u∈b，同样矛盾。
因此b⊆u，由Extensionality得b=u，而u∈a给b∈a。
上述初段证明只比较同一个原序数内部的两个元素，未循环假设任意两序数比较。

## 任意两序数比较与排斥
对任意内部Ord(a),Ord(b)，若a⊆b则初段结论直接给a=b∨a∈b。
否则取a中不属于b的成员极小元u；u⊆b，且u∈a使u传递。
以Ord(b)和传递子集u再次应用初段定理，得到u=b∨u∈b。
u∈b与差性质矛盾；u=b与u∈a给b∈a。
OrdinalComparison.compare由此取得a=b∨(a∈b∨b∈a)。
OrdinalTrichotomy额外在同一个完整对象闭句内证明：
a=b排除两个成员分支；a∈b排除b∈a。相等替换和原序数不自属用于前者，
原传递性和不自属用于后者。没有仅把三歧当作未排斥的析取。

## 六个完整闭句与实际理论
ObjectOrdinalComparison.assumptions只含Extensionality、Foundation及separation(outsideMatrix)。
不存在对象AC、Collection、Replacement、PowerSet、Infinity或传递覆盖的额外输入。

| 闭句 | 完整对象内容 |
|---|---|
| differenceSentence | ∀a,b[¬(a⊆b)→∃u Minimal(a,b,u)] |
| initialSentence | ∀a,b[Ord(a)→Transitive(b)→b⊆a→(b=a∨b∈a)] |
| comparisonSentence | ∀a,b[Ord(a)→Ord(b)→(a=b∨(a∈b∨b∈a))] |
| trichotomySentence | 同一对序数的比较，加上相等排除两个成员方向及两个成员方向互斥 |
| subsetSentence | ∀a,b[Ord(a)→Ord(b)→(a⊆b↔(a=b∨a∈b))] |
| asymmetricSentence | ∀a,b[Ord(a)→a∈b→b∉a] |

每句均有source_*、*_kernel_certificate、source_ZF_*和native_*。
有限理论上的原核证书仅依赖propext/Classical.choice/Quot.sound；nativeZF回放沿用底座
七条固定公理句子FreeClosed证书的既有native_decide.ax_1基线，未宣称原生回放只有三项标准依赖。
Classical.choice未被用作对象选择公理或内部集合见证的宿主数据抽取。
CheckStep3直接检查原Source.ordinal的比较闭句及有限三句理论的三歧原核证书，避免只验内部别名。

## 实际检查
C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；8条正式命令退出码全部为0。
Lean4.33.1，LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成200个任务。
19条源规则、9类源ZF公理和锁定源码SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
审计1312个声明：118个无公理依赖，1194个记录允许依赖；0条Lean警告。
新增64个审计声明，其中6个无公理依赖；全部6个新增有限理论kernel_certificate的依赖均逐项检查。
167个已验收文件哈希重新核对，无不匹配。未新增sorry/admit、自定义公理或外部良基/标准性前提。
本批定向编译先修正了双层绑定矩阵的定义展开和嵌套假设的上下文类型；最终全验收通过。
verification/保存实际命令、日志、依赖和源码哈希；未推送远端。

## 接续与未完成内容
下一项以任意内部序数集合的实际Union见证证明其并仍为序数及最小包含上界，
然后推进内部序数递归、秩覆盖和累积层。任意序数对的比较已完成，不能据此声称递归或秩已完成。
全局ω函数图、最小传递闭包、反向完整Collection、两种AC呈现的等价仍未完成。
内部ProofZF/U及Con完整AST、任意内部码上的编译器正确性、对象解释/对称强迫和
最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建和Comparator仍未运行；本批不宣称PP/AC相对一致性定理已完成。
