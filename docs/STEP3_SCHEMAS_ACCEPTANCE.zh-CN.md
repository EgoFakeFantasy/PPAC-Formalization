# 持续目标批次：七固定公理与全部源分离模式
日期：2026-10-21。分支：migration/yesmeta-step3。
本批基点：4c4998cbcd93c67a8bf868d919f3bfdafe11f744。
OpenAI与YesMetaZFC固定提交未变；持续目标仍为对象ZF内的内部Con蕴含，整体尚未完成。

## 实际对象推导
- 新增 source_infinity/source_foundation/native_infinity/native_foundation。
  至此七条固定公理均在两个呈现中取得原FirstOrder.Derives。
- 无穷处理两个见证条件中的合取交换；基础处理两种无交元条件的蕴含重排。
  重排由原核逻辑规则证明；没有调用模型语义、完备性、对象AC或额外非空集合公理。
- 任意n及p : Source.Formula (n+1)，实际构造：
  FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.separation p))。
- 同一任意p的反向接口实际构造：
  FirstOrder.Derives ZFEquivalence.sourceZF []
    (Project.fo_sentence (Axioms.Schema.separation (ProjectSyntax.unary p)))。
  sourceZF是源全Replacement版ZF的句子像，没有偷换为原Collection版ZF。
- 参数个数、矩阵量词复杂度均无限制；CheckStep3除通用定理外还检查三参数/混合量词实例。

## 依赖的完整句法证据
| 文件 | 已证明的范围 |
|---|---|
| FormulaEquivalence | 任意源矩阵与项环境的对象等价模式；合取交换、蕴含重排、量词下组合；每个实例返回原Derives |
| ProjectSyntax | Source末槽→Project首槽；任意重命名严格交换；反序Fin映射；原FO翻译严格交换；任意参数全称闭合 |
| ProjectNormalization | 全Project连接词展开；自由闭合内核证书；与原FO规范化严格交换；全称闭合交换 |
| SeparationSyntax | 矩阵跨A/B/x三个局部槽的精确反序；整个分离句的AST等式；上述两个实际对象推导接口 |

SourceStatements、19输入规则和原底座未修改。
外部模式索引保留；没有把模式实例升级成内部统一真值断言，也没有把外部传输称作内部码正确性。

## 实际验收
C:/Python314/python.exe scripts/verify.py：退出0。
脚本的8条命令全部退出0：19源规则核对、9源ZF构造器/SHA核对、版本、完整build、
Check.lean、CheckStep2.lean、CheckStep3.lean、Audit.lean。
Lean 4.33.1，单线程，lake --no-cache --wfail build成功，74个任务。
三组检查及Audit均以 --trust=0 执行；所有命令合计0条Lean警告。
132个列举声明：12个无公理依赖，120个有已记录依赖；本批新增49个审计声明。
通用逻辑/Project句法模块只允许标准依赖；ZF及分离桥涉及原底座句子时，
非标准依赖仍限定在TRUST_BASELINE记录的7个原native_decide闭合证书中。
没有新增自定义公理；不能把继承证书描述为全工程只有标准三公理。
完整命令、输出与文件SHA保留在本地忽略的verification/；未推送远端。

## 未完成与下一工作
1. 任意原生Project矩阵的分离实例反向覆盖尚未证明。
   当前反向接口仅覆盖ProjectSyntax.unary p；不能据此宣称完整模式等价。
   下一步先证明任意纯成员开放公式的规范反向编码和Project重命名的FO交换，
   再把矩阵对象等价提升到完整分离句。
2. 全Collection/Replacement双向对象推导尚未完成。源Replacement→Collection方向需内部秩界等构造；
   原Collection→源Replacement方向需收集见证后用完整分离构造精确像，不能忽略多余元素。
3. 两种AC、六规则/27模式到源演绎的反向编译仍待完成。
4. 专用内部ProofZF/U检查公式、任意内部码正确性、可构造解释、对称强迫和主句装配仍待完成。
   本批不是最终内部Con定理，不声称OpenAI原库或Comparator已编译通过。

持续目标保持active；本批结果只是完整目标的已核验进展。
