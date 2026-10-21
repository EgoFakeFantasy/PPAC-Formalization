# 持续目标批次：Collection到原始Replacement及完整正向理论回放
日期：2026-10-21。基点：0b404bf949685e7c5eed1d7f5e0b5caf74f2bc79。
分支migration/yesmeta-step3；上游提交与原核未修改；内部Con对象主目标仍active。

## 实际完成的数学方向
对任意n及p : Source.Formula (n+2)，native_replacement实际返回：
FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p))。
没有限制参数数目或矩阵复杂度；输出严格匹配原始SourceStatements的Replacement句子。
该方向是“原Collection版ZF证明源Replacement”，尚不是两种ZF的完整双向等价。

## 精确像的证明
1. 从原Replacement前件取得每个x∈A的唯一输出u。
2. 将该前件弱化为总关系，使用Collection取得W，使每个x∈A有某个z∈W满足R(x,z)。
3. 任意R(x,y)与R(x,z)由同一个唯一性条件得到y=u、z=u，故z=y。
4. 通过对象等词替换由z∈W推出y∈W。这一步保证所有输出入界，而非只保证已选见证入界。
5. 对W分离谓词∃x∈A R(x,y)，得到C；用第4步消去分离定义中额外的y∈W条件。
6. 得到∀y(y∈C↔∃x∈A R(x,y))，经存在消去/引入、蕴含引入和全参数闭合恢复原Replacement句子。
整个过程用锁定19源规则组成证书，再由已证编译器产生原Hilbert核证书。
见证只以对象变量槽进入推导；没有抽取Lean选择函数，没有添加对象AC或语义完备性前提。

## 证明接口与可信边界
| 模块 | 已证明的内容 |
|---|---|
| SourceAlgebra/SourceLogic | 重命名复合、闭句参数特化与闭合、fresh假设搬运、派生等词规则；19输入规则未改 |
| ReplacementPredicates | 总功能关系、唯一纤维、收集界、分离结果和精确像的对象AST及全重命名/特化 |
| ExactImage | 唯一性推出全部输出有界；分离结果确实是完整精确像 |
| ReplacementInstances | 原始Replacement句子的严格AST等式；Collection/分离闭实例的参数特化 |
| ReplacementFromCollection.kernel_certificate | 原核Derives，只以一个Collection实例与一个分离实例为理论输入 |
| ReplacementFromCollection.native_replacement | 将上述两实例实际回放到原nativeZF，得到无外加前提的完整模式实例 |
| ZFReplay | 源ZF九类公理和源ZF+PP+ACwo+¬AC全部推导，回放到对应原生实际理论 |

两实例理论明确定义为两个闭句的析取成员谓词，不含Replacement或待证结论。
replacement_original用rfl确认原始量词和唯一性前件未变；参数闭合不引入内部统一真值断言。
source_closed_at/source_target_closed_at允许任意有限源变量环境，输出原核空free上下文。
新增consistent_source_of_native只是编译器的外部一致性方向，不是内部Con蕴含。

## 实际验收
C:/Python314/python.exe scripts/verify.py退出0；其8条命令全部退出0。
Lean4.33.1；单线程；lake --no-cache --wfail build成功，84个任务。
19规则、9类源ZF/SHA核对通过；三组Check及Audit均以--trust=0通过；0条Lean警告。
222个列举声明：14个无公理依赖、208个有已记录依赖；本批新增57个审计声明。
kernel_certificate及全部源逻辑/精确像核心只依赖允许的标准propext/Classical.choice/Quot.sound，
不继承原底座7个固定句子native_decide证书。实际nativeZF/target回放仍继承既有7证书基线。
没有新增自定义公理；底座未改；本地verification/保存命令、输出、源码SHA；未推送远端。

## 剩余工作
- 在源Replacement版ZF内证明任意原Collection实例，需对象秩/最小见证秩等构造；不得用语义秩替代。
- 原六规则/27逻辑模式到源演绎的反向编译及非空变量环境对应。
- 两种AC、内部ProofZF/U的完整AST与任意内部码正确性、解释/强迫及最终内部Con对象主句。
普通相对一致性主结论尚未完成；未运行OpenAI原库或Comparator；不标记整体目标完成。
