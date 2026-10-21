# 对象递归前置：原Kuratowski对存在唯一性与完整分量刻画
日期：2026-10-21；基点dfa6183583613d87fc9101e45b762c4fdf3f22a1。
分支migration/yesmeta-step3；原源19规则、原ZF九类公理和YesMetaZFC固定依赖均未修改。
本批完成3b.2a；3b.2图/内部ω/传递闭包及最终内部Con对象主句仍未完成。

## 精确对象交付
在同一个纯成员/等词语言ℒ中，K(p,x,y)严格采用源Source.SetLanguage.orderedPair：
p={{x},{x,y}}。PairSyntax.pair_original与ordered_original均用rfl核对原源定义。
两个实际原核闭句如下：

1. ObjectPairs.existenceSentence：
   ∀x∀y ∃p [K(p,x,y) ∧ ∀q (K(q,x,y) → q=p)]。
2. ObjectPairs.characterizationSentence：
   ∀p∀q∀x∀y∀a∀b [K(p,x,y) → (K(q,a,b) → (p=q ↔ (x=a ∧ y=b)))]。

ObjectPairs.native_exists_unique/native_characterization实际返回
FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
源Replacement版ZF亦有source_ZF_exists_unique/source_ZF_characterization，
没有借用尚未完成的Replacement/Collection双向等价。
更小的输入理论ObjectPairs.assumptions只含原Pairing和Extensionality两个闭公理。
existence_kernel_certificate/characterization_kernel_certificate在其原核理论像内取得相同闭句证明。
不需要Foundation、Replacement、Collection、对象AC或宿主配对函数。

## 证明工程
| 模块 | 实际证明 |
|---|---|
| PairSyntax | 与源Kuratowski编码严格一致；全部rename与任意变量环境的Pairing/Extensionality特化 |
| UnorderedPairLogic | 成员两分支、对象等词替换、外延唯一性、固定一个分量的消去律及单元素集分量恢复 |
| OrderedPairExistence | 三次实际Pairing构造单元素集/无序对/外层无序对；全部见证用原exI/exE |
| OrderedPairElimination | 两个Kuratowski见证的同时消去；仅由原两次exE和weaken派生 |
| OrderedPairWitnesses | 见证唯一、第一分量恢复、两分量恢复、见证层双向刻画 |
| OrderedPairLogic | 完整消去四个见证，取得实际原ordered关系的双向分量刻画、唯一性与单射性 |
| ObjectPairs | 全量词闭句、存在唯一性；两公理原核证书、源ZF及实际nativeZF回放 |

重复分量x=y没有被排除。第一分量恢复通过单元素集在外层无序对中的两个分支；
固定分量消去律包含退化情况，随后恢复第二分量。未添加x≠y或外部良基假设。
所有变量编号可以非单射；对象参数没有绑定到Lean类型元素。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0，8条实际验收命令全部退出0。
Lean4.33.1，单线程；lake --no-cache --wfail build成功，101个任务。
19源规则及9类源ZF/SHA检查通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
399个列举审计声明：31个无公理依赖、368个有已记录依赖；0条Lean警告。
新增64个审计声明，其中9个无依赖；两公理kernel_certificate只依赖标准
propext/Classical.choice/Quot.sound，不继承底座7个native_decide句子闭合证书。
实际nativeZF回放仍保留既有7证书基线；无新增自定义公理、无sorry/admit。
CheckStep3包含两个实际原核闭句、源ZF证书、两公理证书、原定义rfl对应、
同一个变量槽x=x的全称存在唯一性实例及任意变量/局部假设的分量刻画接口。
verification/保存本地实际日志、命令、公理依赖与当前源码哈希；未推送远端。

## 下一工作与剩余义务
下一项3b.2b先核对Source.SetLanguage.edge/functionOn等原图定义，证明对象图的基本操作；
继而构造内部ω及其全部内部成员上的有限迭代，取得传递覆盖集。
对Kuratowski编码只取得存在唯一性，不表示函数图递归、ω迭代或传递闭包已完成。
仍需对象递归、序数比较、秩/累积层，再在源Replacement版ZF内证明原Collection。
两种AC、完整内部ProofZF/U/Con、编译器内部表示、解释与对称强迫及最终内部Con对象主句仍待完成。
OpenAI原4.34.1工程和Comparator尚未运行；本批不声称PP/AC相对一致性已经证明。
