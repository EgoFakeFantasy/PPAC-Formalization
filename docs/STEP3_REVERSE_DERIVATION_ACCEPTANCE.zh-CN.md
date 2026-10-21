# 第三步3c：原推导核到源演算的反向证书传输
日期：2026-10-21；基点4dd32efbc7a6afe875b91d9bcecd6914b6156966。
分支migration/yesmeta-step3；原YesMetaZFC依赖及锁定源19规则均未修改。
最终内部Con对象主目标仍未完成，保持active。

## 精确交付
ReverseCompile.certificate对任意原HilbertDerivation T free p、任意default : Fin n、
任意free变量编号f，实际返回：
Source.Derives ((Presentation.source T).at n) (Reverse.formula empty f p)。
其证明按原核全部6个构造归纳：logical_axiom、theory_axiom、modus_ponens、
forall_generalization、free_strengthening、free_substitution。
逻辑公理输入由ReverseLogicalAxioms.replay按全部27个原构造逐项回放。
所有输出证书均只使用原19条Source.Derives规则；没有新可信核或新演绎规则。

| 模块 | 已验收内容 |
|---|---|
| SourcePropositional | 纯命题及双条件展开后的实际19规则证书；经典分情况由原classical规则推导 |
| SourceQuantifiers | 全称特化/分配/空泛量化、存在引入/消去、等词替换及新鲜末变量实例 |
| ReverseSubstitution | 回译与源rename/原生rename/任意替换/顶层实例化/自由抽象严格交换 |
| ReverseLogicalAxioms | 完整27模式的Source.Derives回放，任意源上下文和变量编号 |
| ReverseCompile | 全6构造、任意有限局部假设、闭句及原源理论的精确往返 |

## 变量环境与闭句边界
纯语言没有闭项。原核允许free_strengthening将一个额外自由变量删掉；
源演算的实例化只接收Fin n中的变量，因此不把n=0直接逐规则对应。
反向编译显式要求default : Fin n，强化分支将额外free槽编号到default。
此default仅是外部语法编号，不是对象元素或语言常元；不向理论添加非空公理。
ReverseCompile.sentence在n=1回译任意原核闭句证明。
源Consistent原本量化所有n，因此可得外部一致性方向，无需更改一致性定义。
CheckStep3构造原核中使用free_strengthening的∃x(x=x)证书，
并实际回译到源空理论的一个变量环境，核对该边界。
任意有限局部假设按原核Context.discharge的真实顺序消去；
ReverseCompile.derives的源上下文恰为回译理论公理与回译局部假设的并。

对任意源理论T和原源闭句p，source_sentence_iff证明：
FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence p)
↔ Source.Derives (T.at 1) (p.rename Fin.elim0)。
source_theory_roundtrip严格恢复全部闭公理，不限制模式实例。
source_consistent_iff给出相应外部一致性等价；不是内部Con蕴含。
Presentation.source nativeZF是Collection呈现的回译，不能认作Replacement源ZF。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0，其8条命令全部退出0。
Lean4.33.1、单线程；lake --no-cache --wfail build成功，89个任务。
19源规则、9类源ZF及锁定SHA核对通过；三组Check和Audit均以--trust=0通过。
283个审计声明：19个无公理依赖、264个有记录依赖；0条Lean警告。
本批新增61个审计声明，其中5个无依赖，其余只含propext/Classical.choice/Quot.sound。
原核反向certificate仅依赖这3项标准Lean公理，不继承底座7个句子闭合native_decide证书。
实际nativeZF/target主线仍保留既有7证书基线，未把全仓称作纯标准公理依赖。
脚本禁止sorry/admit/新axiom/unsafe/native_decide；本批无新自定义公理、无数据选择接口。
verification/保存实际命令、日志、声明依赖及当前源码哈希；不自动发布日志或推送远端。

## 下一最小工作及仍未完成事项
1. 在源Replacement版ZF中证明原Collection模式：需要原对象层的秩/层级/最小见证秩及全参数证明。
   底座SetTheory.WellFounded.Rank的宿主WellFounded接口不能直接充作对象推导。
   扩展语言的极小元模式若作为输入公理，也不能充作从当前纯ZF证明的结果。
2. 源图AC与原不交族选择集的双向对象推导。
3. 专用纯语言ProofZF/U与Con完整公式，量化所有内部ω码；本批外部编译器的内部表示和正确性。
4. 对象解释/对称强迫及最终Derives nativeZF [] (Con_ZF → Con_target)。
未运行OpenAI原库或Comparator；未证明原PP/AC相对一致性结论。
