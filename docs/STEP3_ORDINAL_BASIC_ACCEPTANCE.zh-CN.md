# 原对象序数定义、成员闭包和实际空/后继序数验收
日期：2026-10-21；基点4cd12224f5efb52ac26339ff2318f888c8d9b1c9。
分支migration/yesmeta-step3。任意两序数比较、递归/秩及最终Con仍未完成。

## 原定义和量词严格保持
OrdinalSyntax给出原Source.transitiveSet、membershipLinear、membershipWellFounded和ordinal的纯对象展开。
transitiveSet_original、linear_original、wellFounded_original、ordinal_original均由rfl证明，
不是通过弱化定义或只证明宿主语义对应取得。
Ord(a)为a传递、成员关系在a上严格线性、每个内部非空子集有成员极小元。
严格线性保留不自属、关系传递性和相等/两个成员方向的三分支比较，所有量词仍遍历内部集合。
内部良基条件精确为∀c[(c⊆a∧∃x x∈c)→∃x∈c∀y∈c y∉x]。
它没有被替换成Lean.WellFounded，也不假定模型成员关系在外部良基或序数外部标准。
此定义与原ACwo中使用的Source.ordinal严格相同。

## 实际基础推导
OrdinalFoundation从原Foundation的正规元条件（x∈c且没有y∈x∩c）逐点转换为
∀y∈c y∉x，证明每个a都满足原内部子集极小元条件。该结论单独不声称任意集合都严格线性。
OrdinalTransitivity双向推导原双全称传递公式与已有传递覆盖中的传递谓词；没有把二者的AST误认为相同。
OrdinalRestriction证明严格线性和内部子集极小元条件沿子集传输。
若Ord(a)且b∈a，则原传递性给出b⊆a；原a内成员关系的传递性进一步给出b传递，
再限制线性和子集极小元条件，得到原Ord(b)。此成员闭包推导不需要额外集合论输入。

OrdinalEmpty由Empty(z)逐点排除其成员，证明原传递性和全部线性条件；内部子集极小元条件由Foundation取得。
原线性条件还给出Ord(a)→a∉a：若a∈a，则在线性条件中取元素a立即矛盾。
OrdinalSuccessor按后继成员“属于旧序数”或“等于旧序数”逐项处理，证明：
- 新成员不自属，旧成员沿用原不自属条件。
- 对x∈y∈z，若z属于旧序数，使用序数成员的传递性；若z等于旧序数，使用旧序数传递性。
- 任意两个新域成员按旧/新两类的四种组合满足原比较分支。
- 新集合的全内部子集极小元条件由原Foundation取得。

## 七个完整闭句及实际存在构造
ObjectOrdinalBasic的有限理论只含Foundation、EmptySet、Pairing、Union。
每句均有source_*、*_kernel_certificate、source_ZF_*和native_*，全部显示参数均在句内量化：

| 闭句 | 对象内容 |
|---|---|
| wellFoundedSentence | ∀a membershipWellFounded(a)（原内部子集条件） |
| noSelfSentence | ∀a(Ord(a)→a∉a) |
| emptySentence | ∀z(Empty(z)→Ord(z)) |
| memberSentence | ∀a,b(Ord(a)→b∈a→Ord(b)) |
| successorSentence | ∀a,s(Ord(a)→Succ(s,a)→Ord(s)) |
| existsEmptySentence | ∃z(Empty(z)∧Ord(z)) |
| existsSuccessorSentence | ∀a(Ord(a)→∃s[Succ(s,a)∧Ord(s)]) |

EmptySet提供实际空序数见证；原Pairing/Union提供实际后继集合，再由已证后继保持性取得序数。
对象见证由原exI/exE处理，未抽取宿主选择函数。
四句有限理论的核证书未以Extensionality、Separation、Replacement、Collection或对象AC为输入。
相等/替换仍使用原逻辑等词规则；未增加集合外延性假设。
这批没有声称任意两个序数可比较，也没有声称后继集合在该有限四句理论中唯一。

## 原核与实际验收
native_*的类型均为真实FirstOrder.Derives nativeZF [] (Translation.sentence 相应闭句)。
CheckStep3还直接使用原Source.ordinal检查成员闭包，避免只验证工程内部别名。
C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，195个任务。
19源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
1248个列举审计声明：112个无依赖、1136个记录允许依赖；0条Lean警告。
新增94个审计声明，其中12个无依赖；无sorry/admit、新自定义公理或外部良基前提。
有限四句理论上的全部kernel_certificate仅依赖标准propext/Classical.choice/Quot.sound；
实际nativeZF回放继续保留底座7个固定句子FreeClosed证书的既有基线。
首次全验收中原Source.ordinal检查缺少命名闭句的显式展开，已修复检查并完整重跑成功。
verification/保存最终实际命令、日志、依赖及源码SHA；未推送远端。

## 下一项与全目标缺口
下一项对差性质x∈a∧x∉b使用已证全参数成员极小元，证明传递子集为初段或相等，
再推出任意两个原对象序数的相等/两个成员方向比较，保持全部内部序数量词。
原序数内部元素的线性与任意两序数比较是不同命题；后者仍未完成。
全局ω函数图、最小传递闭包、内部序数递归/秩/累积层、反向Collection、两种AC、
内部ProofZF/U/Con及任意内部码上的编译器正确性、对象解释/对称强迫和最终Con_ZF→Con_target仍未完成。
OpenAI原4.34.1构建及Comparator仍未运行；未宣称原PP/AC相对一致性定理已经完成。
