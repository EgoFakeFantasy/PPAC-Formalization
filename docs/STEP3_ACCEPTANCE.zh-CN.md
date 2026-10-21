# 第三步阶段验收：3a及五条固定ZF公理
日期：2026-10-21。分支：migration/yesmeta-step3。
基点：418d9f54c37466006de940777bf3d9ffbf613e74；上游固定提交不变。
本批完成3a和3b的五条固定公理；整个步骤3尚未完成。

## 对象合同
背景仍为原ZF纯语言像B；目标仍为原FirstOrder.Derives B [] (Con_ZF → Con_target)。
本批的等价结论实际返回原核Derives，没有使用模型语义、完备性、对象AC或不可达前提。
内部Con检查器AST、任意内部码上的编译正确性和最终对象主句仍未实现。

## 本批交付
| 模块 | 完整接口/覆盖范围 | 实际完成 |
|---|---|---|
| Normalization | 任意签名及bound/free公式；全部11构造器；替换严格交换及幂等性 | 真展开为⊥→⊥，否定展开为→⊥，双条件展开为两蕴含之合取 |
| Normalization.equivalent | 任意T、Γ、开放p：Derives T Γ (p ↔ normalize(p)) | 原核连接词及fresh量词规则，覆盖任意嵌套 |
| ReverseSyntax | 全部纯成员公式、任意有限变量映射、任意绑定深度 | 原生首binder/源末binder精确对应 |
| Reverse.source_sentence_roundtrip | 任意源闭句φ：decode(translate(φ))=φ | PP/AC/ACwo及任意参数模式均覆盖 |
| Reverse.native_sentence_roundtrip | 任意原生闭句φ：translate(decode(φ))=normalize(φ) | AST等式；再由sentence_equivalent给对象Derives |
| Presentation.derives_iff | 任意T/free/Γ/p：Derives (Presentation.theory T) Γ p ↔ Derives T Γ p | 每条公理实际回放，再用原核theory_cut |
| SourceTheory | 七固定公理+全Separation/Replacement；精确源目标理论 | 九构造器与固定源摘录逐字一致，SHA与SOURCE_LOCK交叉核对 |
| ZFEquivalence | 外延、空集、配对、并集、幂集 | 每条两个方向的原核Derives，共10条实际公理推导 |

具体固定公理接口：
- source_<name> : Derives nativeZF [] (Translation.sentence Source.SetLanguage.<name>)。
- native_<name> : Derives sourceZF [] (Project.fo_sentence Axioms.<name>)。
- sourceZF = TheoryTransport.theory Source.SetLanguage.ZF，保留源全Replacement呈现。

固定公理AST等式采用普通 decide +kernel；没有新增native_decide公理。
SourceSyntax只增加DecidableEq实例，没有改变8个构造器或19条输入规则。

## 实际验收
单线程执行 C:/Python314/python.exe scripts/verify.py，退出0。
脚本实际执行的8条命令均退出0：
1. 源19规则逐字核对。
2. 源9类ZF公理逐字核对，并与SOURCE_LOCK核对原文件SHA。
3. Lean版本读取：4.33.1。
4. lake --no-cache --wfail build：70个任务，成功。
5. lake env lean --trust=0 Check.lean。
6. lake env lean --trust=0 CheckStep2.lean。
7. lake env lean --trust=0 CheckStep3.lean。
8. lake env lean --trust=0 Audit.lean。

83个列举声明：11个无公理依赖，72个有已记录依赖；所有命令输出合计0条Lean警告。
其中新增45个审计声明：28个通用句法/逻辑/呈现声明只使用标准依赖或无依赖；
17个ZF对应声明的非标准依赖均属于原底座已经记录的7个闭合证书基线。
Normalization.equivalent本身只依赖propext、Quot.sound。
涉及原ZF句子的声明仍继承底座native_decide闭合证书，不能宣称全工程仅有标准三公理。
没有新增自定义公理；没有运行或声称通过OpenAI原库/Comparator。
本地verification/保留命令退出码、完整输出和参与验收的文件SHA；日志不作为发布内容。

## 必须保留的边界
Presentation.theory T 是原T的连接词规范化呈现，不是源Replacement版ZF的别名。
Presentation.derives_iff两边都是原FirstOrder.Derives；它没有产出Source.Derives。
Source.Consistent覆盖任意有限变量环境；后续反向编译必须检查free_strengthening与非空环境的对应，
不应直接承诺源n=0与原空free上下文逐规则等同。
五条固定公理的证明不蕴含ZF全模式等价；当前没有完整理论等价定理。

## 下一最小工作与验收门
| 工作单元 | 可修改文件 | 完成门 |
|---|---|---|
| 无穷与基础 | ZFEquivalence及必要的原核逻辑辅助 | 逐式核对存在见证合取次序、两种无交元条件；两个方向实际Derives |
| 分离模式 | Project/Source模式句法适配模块 | 任意参数数目、任意矩阵；binder反序与闭合精确；双向Derives |
| Collection/Replacement | ZFEquivalence及原核集合论构造 | 全模式双向对象证明；不引用语义证明替代，不以结构字段假定结论 |
| 反向演绎 | ReverseDerivation与源句法恒等式 | 原六规则/27逻辑模式；明确额外变量；实际Source.Derives及原核回放 |
| 两种AC | ChoiceEquivalence | 原ZF内集合图/选择集互构造，完整量词，不能预设选择函数 |

后续4–13步继续按AGENT_WORKFLOW推进；最终内部Con对象目标保持不变。
