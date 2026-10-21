# 完整Collection与ZF呈现双向回放验收
日期：2026-10-21；基点69ca92cf83c308d341862e6aaa8d160d69ad6d0e。
分支migration/yesmeta-step3；两种AC互导、内部证明码正确性及最终内部Con主句仍未完成。

## 对象合同和本批完成范围
对象语言仍为原纯等词/成员语言，终点仍为原FirstOrder.Derives；没有新推导核。
源ZF仍为原Source.SetLanguage.ZF九类公理（七固定句、全Separation、全Replacement），没有加入Collection。
nativeZF仍为原SetTheory.ZF经Project.fo_theory的纯语言像，含全Collection，不加Choice。

本批实现任意n及p : Source.Formula (n+2)的实际对象模式：
Source.Derives (Source.SetLanguage.ZF.at 0) (CollectionSyntax.collection p)。
该闭句严格是原Collection：
∀params∀a[(∀x∈a∃y Rel_p(params,x,y))→∃v∀x∈a∃y(y∈v∧Rel_p(params,x,y))]。
所有集合、输入、输出及见证量词遍历全部内部集合，原关系无功能性或唯一见证要求。
n和p是外部模式索引，每个实例本身是完整对象句子及正式Derives；本批未声称内部统一语法码表示已完成。

## 最小见证秩和真实原关系见证
WitnessRankSyntax定义Witness(ρ,x,α):=∃y[Rel_p(ρ,x,y)∧Rank(y,α)]，
其中Rank是已证明实际存在的最小包含层秩。原y仍是内部存在见证，没有被抽为宿主函数。
predicate p保留所有原参数并追加原输入x，append_rename/append_up显式核对追加参数和重命名。
least是满足Ord(α)∧Witness(ρ,x,α)的最小序数；其原Replacement关系、唯一性、纤维、像和精确像逐式对应。

WitnessRankFibers消去原关系的实际y，由全体集合秩闭句得到其实际秩α，
再以全参数最小序数模式取得唯一最小见证秩纤维。唯一的是序数，原y不要求唯一。
WitnessRankCollection以明确的原replacement(matrix p)实例实际构造精确最小见证秩集合C，
并逐实际C成员证明其是原序数。

WitnessRankBounds给C取实际严格序数界δ，实际层存在给Layer(δ,v)。
对任意原输入x∈a，消去其最小见证秩α和Witness中的真实y，取得Rel_p(ρ,x,y)与Rank(y,α)。
精确像和严格界给α∈δ，已证层成员递归把秩中的y⊆Vα提升为y∈v。
因此v满足原关系的完整Collection覆盖式，原参数和原Rel_p均未更改。
CollectionFromReplacement实际消去C/δ/v及所有局部见证，闭合全部参数和a，得到完整原Collection句子。
依赖的实际秩、层存在和最小序数定理均来自源Replacement版ZF；没有循环输入Collection或对象AC。

## 任意原生矩阵和原核端点
CollectionFromReplacement提供：

| 端点 | 实际类型与范围 |
|---|---|
| source_collection p | 源Replacement版ZF中的完整Collection对象证明 |
| kernel_certificate p | FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) [] (Translation.sentence (collection p)) |
| native_source_matrix p | 同一源矩阵Collection在实际nativeZF中的原核回放 |
| native_project_matrix s | 任意原生Project.BinarySchema s的原Collection句子，在源ZF句子像中的实际Derives |

native_project_matrix使用已证任意矩阵回译及纯逻辑规范化等价，覆盖所有原生矩阵；
它不只覆盖源encode生成的矩阵，也不以nativeZF本身已有Collection作为源证明输入。

## 完整ZF及目标理论双向推导回放
ReverseZFReplay.replay_project_axiom逐原ZF九类构造取得实际源ZF句子像证明：
七固定公理、任意原生Separation矩阵、任意原生Collection矩阵。
replay通过原theory_cut保留任意自由上下文Γ、任意有限局部假设及任意原核结论。
derives_iff与既有正向ZFReplay组成完整ZF呈现之间的双向实际推导接口。

source_native_sentence对任意原生闭句实际返回原19条源规则的证明，
source_sentence对已翻译的原源闭句精确恢复原句；源端保留一个未用外部变量环境。
既有六种原核构造/27种逻辑模式反向编译器被实际调用，不以两边都用原核的呈现等价替代源Derives。

目标理论仍严格为各自ZF加原PP、ACwo、原图AC的否定三句。
target_axiom/target_replay/target_derives_iff及source_target_sentence接口完成同样的双向实际回放。
这没有证明该目标理论一致，也没有将原图AC偷换成底座内置不交族选择集AC。
本批完成的是对象公理逐模式互导和外部证书回放，不是任意内部Proof码的编译正确性或内部Con蕴含。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成284个任务。
19源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计2105个声明：150个无公理依赖、1955个记录允许依赖；0条Lean警告。
6个新模块的62个显式声明全部加入Audit，未新增自定义公理。
source_collection、kernel_certificate及native_project_matrix三个核心声明的依赖逐项实际核对
恰为propext/Classical.choice/Quot.sound；native回放与逆回放接口仅继承原七个固定句子证书依赖基线。
251个验收文件实际SHA256复核一致，无sorry/admit、unsafe或新增外部标准性前提。
CheckStep3直接核对原存在前提无唯一性、实际见证秩AST、原Replacement纤维/精确像、
完整原Collection闭句、任意源/原生矩阵，以及ZF/目标理论任意开放推导与原19规则返回类型。
另验收正文y=y的非函数关系实例，未给输入添加唯一见证条件。
定向构建修正源理论别名展开；首次完整检查修正AST示例的量词构造器名歧义，最终全验收通过。
实际命令、日志、依赖及哈希保留于本地verification/；未推送远端。

## 下一项与最终缺口
下一项按工程表3d.a–3d.d，先严格对应原Source.choiceOn/AC和原Axioms.choice。
图选择到选择集方向实际构造选择图的精确值集合；逆向实际构造Kuratowski带标签纤维和其非空不交族，
将原选择集限制到标签族实际并，验证完整functionOn、唯一输出及每个输出确在原族成员中。
两种AC对象互导尚未实现，不能因ZF呈现互导已完成而一并宣称完成。
专用内部ProofZF/U/Con AST、任意内部码编译正确性、对象解释/对称强迫及最终
FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
全局ω图及最小传递闭包仍是独立待办；OpenAI原4.34.1构建及Comparator仍未运行。
