# 原图AC与原选择集AC的完整对象等价验收
日期：2026-10-21；基点9bafd927c25cba5f836389d9f995da59856e40cf；分支migration/yesmeta-step3。

## 实际原推导核终点
对象语言仍为单排序纯等词/成员语言。背景nativeZF为原YesMetaZFC的ZF纯语言像。
ChoiceNativeBridge.native_forward、native_reverse、native_equivalence分别给出：

```
FirstOrder.Derives nativeZF [] (Formula.imp AC (Project.fo_sentence Axioms.choice))
FirstOrder.Derives nativeZF [] (Formula.imp (Project.fo_sentence Axioms.choice) AC)
FirstOrder.Derives nativeZF [] (Formula.iff AC (Project.fo_sentence Axioms.choice))
```

AC为原Source.AC的精确翻译，包含原完整functionOn及所有内部集合量词；
另一侧是未修改的原Axioms.choice，不额外要求选择集属于族并。
原Source.AC与selectorAC还在原19规则的源ZF中有真正的双条件推导，
ObjectSelectorGraphChoice.equivalence_kernel_certificate将它传入原核。
本批由原公理构造实际集合并返回Derives，不通过宿主模型语义、可靠性或完备性换层。

## 反向构造与五句背景
有限理论T5只包含：

| 背景句子 | 实际用途 |
|---|---|
| 原Extensionality | Kuratowski分量唯一及标签行唯一 |
| 原Pairing | 实际有序对存在 |
| replacement(TaggedRowSyntax.pairMatrix) | 对每个x实际取得精确行r={〈x,y〉:y∈x} |
| replacement(TaggedFamilySyntax.matrix) | 实际收集所有x∈a的唯一行成精确族b |
| replacement(SelectedPairSyntax.matrix) | 从每个x的唯一被选标签对取得精确图f |

TaggedRowExistence证明实际行存在唯一；TaggedRowLogic由实际交点和有序对分量唯一性证明相交行相等。
TaggedFamilyCollection/Logic构造精确族并证明当a逐项非空时，b逐项非空且不同成员不交。
没有预设族存在，没有在Lean中抽取一族内部行或选择见证。

从原selectorAC前件取得b的实际选择集s。SelectedPairFiber把每个实际行中的唯一交点
传为Chosen(s,x,p):=p∈s∧∃y∈x Ordered(p,x,y)的唯一纤维。
第三个原Replacement取得严格精确像f：
∀p[p∈f ↔ ∃x∈a Chosen(s,x,p)]。
选择集s本身允许有任何杂项，f的精确像定义会排除它们。
这实现了原流程中“排除杂项”的完整验收目的，不再额外构造族并和Separation限制。

SelectedGraphLogic对任意f成员消去其实际输入和输出，证明完整entriesOn。
对任意竞争边消去其实际pair code，原Kuratowski分量唯一性把其标签对齐到相同x；
该x的唯一选择点推出pair code相等，再由分量唯一性得输出相等。
SelectedGraphChoice保留完整totalOn，并证明每个域内输入有实际输出属于它，取得原choiceOn。
包括空族在内的全部内部族由同一对象推导覆盖，不限定外部标准集合。

ObjectSelectorGraphChoice.source_family/source_reverse有T5中的完整闭句推导和原核证书，
并逐个原公理回放到源ZF及nativeZF。AC仅是reverseSentence的对象蕴含前件。
没有增加对象AC、Collection输入、Foundation或不可达等假设；五句背景只是已验证充分背景，不宣称最小性。

## 可信基与验收
上批原choice桥接的额外既有FreeClosed证书仍仅限ChoiceNativeBridge及原Axioms.choice声明；
CHOICE_TRUST_BASELINE.json与原ZF七证书的TRUST_BASELINE.json均未改。
原Common.lean源码哈希通过核对。没有新增自定义axiom声明。

| 核心证书 | 实际依赖 |
|---|---|
| T5的family_kernel_certificate | propext、Classical.choice、Quot.sound |
| T5的reverse_kernel_certificate | 同上三项 |
| 源ZF的equivalence_kernel_certificate | 同上三项 |
| 原公式reverse_kernel_certificate | 三项及原choice既有闭性证书 |
| 原native_equivalence | 三项、原ZF七项及原choice既有闭性证书 |

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成305个任务。
Check、CheckStep2、CheckStep3与Audit均以--trust=0通过。
19条源规则、9类源ZF及原文锁定SHA核对通过。
2305项审计：180项无公理依赖、2125项记录允许依赖；0条警告。
本批新增120项显式审计，其中16项无公理依赖。
273个验收文件实际SHA256复核一致。验证器禁用sorry/admit、unsafe及新增自定义公理。
CheckStep3直接验收Replacement纤维/精确图AST、源原完整choiceOn、T5闭句及原nativeZF双条件。
命令、日志、完整声明依赖与哈希保留本地verification/，不作为GitHub发布材料。
本批未推送远端。

## 全目标边界及下一项
3d的AC互导已完成；不能据此宣称ZF证明AC或原PP/AC问题的相对一致性已经完成。
最终仍要求Derives B [] (Con_ZF → Con_target)。
下一主项为步骤4的专用ZF/U内部Proof/Con纯公式AST，需精确匹配原六规则、27逻辑模式及全Separation/Collection。
步骤5还必须证明任意内部ω码上的转换器正确性；已有外部证书回放不替代该内部推导。
内部Con主句、内部解释、实际对称强迫及模型应用仍未完成；原OpenAI构建/Comparator仍未运行。
