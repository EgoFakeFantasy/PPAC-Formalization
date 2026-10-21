# 原图AC到原选择集AC的正向对象推导验收
日期：2026-10-21；基点e410890c3f4cddf956e11714ec6ac49bbecfc57a。
分支migration/yesmeta-step3；反向选择集到图AC、完整AC等价及最终内部Con主句仍未完成。

## 原公式及全内部量词
ChoiceSyntax.choiceOn严格对应原Source.SetLanguage.choiceOn，包含完整原functionOn及逐成员实际选择输出。
原图AC严格保持∀a[每个u∈a非空→∃f ChoiceOn(f,a)]，所有集合、图、输入及输出均量化全部内部集合。

选择集公式逐字展开原Axioms.choice：
∀a[(每个u∈a非空 ∧ 不同族成员两两不交)→∃c∀u∈a∃y(
  (y∈c∧y∈u) ∧ ∀z((z∈c∧z∈u)→z=y))]。
没有增加c⊆∪a的前提或结论，保留原公式允许选择集含族并外元素的范围。
ChoiceNativeBridge.selector_ast以decide +kernel核对完整原公式和源展开的精确AST，未改原Axioms.choice。

## 三个源闭句与实际原核终点
背景有限理论T_R只含replacement(GraphRangeSyntax.matrix)。
该矩阵原关系严格是Edge(f,input,output)，保留实际图参数f。

| 闭句 | 完整数学内容（缩写展示） |
|---|---|
| rangeSentence | ∀f,a[FunctionOn(f,a)→∃c∀y(y∈c↔∃u∈a Edge(f,u,y))] |
| selectorSentence | ∀f,a[ChoiceOn(f,a)→Disjoint(a)→∃c Selector(c,a)] |
| forwardSentence | 原Source.AC→上述原选择集AC的源展开 |

ObjectGraphChoiceSelector逐句提供T_R中的source_*、有限理论*_kernel_certificate、源ZF与nativeZF回放。
原图AC是forwardSentence的对象蕴含前件，没有被加入背景公理。
本正向构造只使用该一个Replacement实例作为集合论输入；不声称它是必要最小公理集。
背景不要求额外Foundation、Pairing、PowerSet、Extensionality、Infinity、Collection或对象AC公理。

ChoiceNativeBridge另给实际原核闭句：
FirstOrder.Derives nativeZF [] (Formula.imp AC (Project.fo_sentence Axioms.choice))，
其中AC仍为原Source.AC的精确翻译，不是底座内置选择集公理的别名。
同一蕴含也有有限T_R的原核证书；原选择公理桥接的语法证书依赖单列如下。

## 实际精确值域和交点唯一性
GraphRangeSyntax的原Replacement纤维严格等于原GraphSyntax.valueExists，原functionOn已逐域点保证实际唯一输出。
GraphRangeCollection用该Replacement实例实际取得精确值集合c，未用可能含多余元素的Collection界。
ChoiceLogic对已知域内输入消去实际valueAt，证明任意两条输出边给同一值；不必额外调用图域外延性。
对任意u∈a和Edge(f,u,y)，消去原ChoiceOn的真实选择输出，由域内唯一性得y∈u。

ChoiceSelectorPoints对z∈c∩u，由精确像消去其实际输入v∈a及Edge(f,v,z)。
输出成员性给z∈v；不交族的相交成员必须相等，故u=v。
对象等词替换把这条边传回同一输入u，域内唯一性推出z等于u的选择输出。
正向实际取得每个u的输出y，并由精确像得y∈c，故交点存在且唯一。
GraphChoiceToSelector消去真实f和c见证，给选择集存在；ObjectGraphChoiceSelector闭合完整AC蕴含。
包括空内部族在内的全部族量词由同一对象推导覆盖，不以外部枚举或标准集合模型替代。

## 可信基的明确变化与隔离
原YesMetaZFC固定提交039c8e132cc19671d73a3933c66b4799d2599dd6保持不变，
原Common.lean文件经Git状态核对未修改；原ZF七个固定句子证书基线docs/TRUST_BASELINE.json也未修改。

本批第一次引用原Axioms.choice公式，因此额外激活其库中已有的语法闭性证书：
YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1。
该依赖来自原sentence!宏的FreeClosed证明，不是本工程新增声明，也不是向对象ZF加入AC公理。
但它确实是新增的活跃依赖，不能声称整个桥接仍只有前七项基线。
来源、原Common.lean的实际SHA256及限域规则见CHOICE_TRUST_BASELINE.json；原库声明本身亦加入Audit。

| 证书范围 | 实际依赖边界 |
|---|---|
| 三个源有限理论*_kernel_certificate | 恰为propext/Classical.choice/Quot.sound |
| 三个nativeZF源句子回放 | 标准三项及原ZF七项既有证书基线 |
| 原公式桥接forward_kernel_certificate | 标准三项及原choice闭性证书 |
| 原native_forward | 标准三项、原ZF七项及原choice闭性证书 |

验证器只允许ChoiceNativeBridge命名空间和原Axioms.choice声明引用这项额外证书，
源证明核心继续按标准三项审计，不将该依赖加入原ZF背景基线；没有新增自定义axiom声明。
原Common.lean源码哈希和独立基线JSON均参与本批验收。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成292个任务。
19条源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计2185个声明：164个无公理依赖、2021个记录允许依赖；0条Lean警告。
8个新模块的79个显式声明以及原choice声明共80项新增审计，其中14项无公理依赖。
260个验收文件实际SHA256复核一致，无sorry/admit、unsafe或新增对象强假设。
CheckStep3直接检查原Source.AC/choiceOn、完整唯一交点AST、原Replacement输出纤维、三个闭句及精确原Axioms.choice终点。
定向构建修正原公式有限变量对齐及抬升假设像接合；最终全仓验收通过。
命令、日志、依赖及哈希在本地verification/；原选择公理依赖探针保持本地，不推送远端。

## 下一项及全目标边界
逆向先实际构造每个原成员x的带标签纤维{〈x,y〉:y∈x}和精确族，证明非空及两两不交。
调用原选择集前提后，将它限制到实际标签族并，验证完整functionOn、唯一输出和逐成员输出属于x。
原选择集可能含并外杂项，不能直接把它当作完整选择图。
完整AC等价、内部ProofZF/U/Con AST与任意内部码正确性、对象解释/对称强迫及最终内部Con主句仍未完成。
本批不证明ZF推出AC，也不证明PP/AC分离或相对一致性最终定理。
