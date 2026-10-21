# 内部有限序列前置的对象推导验收
日期：2026-10-21；基点2040ffb404a1691d1488f123a033cc736abf5263；分支migration/yesmeta-step3。

## 交付范围
本批完成工程4a：专用ProofZF/U关系所需的实际内部有限序列基础。
对象签名仍为纯等词/成员语言，终点仍使用原FirstOrder.Derives；未引入新推导核。
专用ProofZF/U完整纯公式AST、任意内部证明码正确性和最终Con主句仍未完成。
原ZFC专用ReducedProofPresentation/PureProvability没有被直接当作ZF检查器。

## 完整对象公式与八个闭句
SequenceSyntax.sequence(f,n,b)为原完整FunctionOn(f,n)与Bounded(f,b)的合取。
Bounded(f,b):=∀i∀y(Edge(f,i,y)→y∈b)。全部序列、长度、值及见证都是内部集合。
原FunctionOn同时保留entriesOn和totalOn，故不能含域外条目或非有序对杂项。

| 闭句 | 数学内容，缩写展示 |
|---|---|
| emptySentence | 任意空集z本身是空域z上、值域限制于任意b的实际序列 |
| valueSentence | Seq(f,n,b)且i∈n时，实际存在y∈b满足原完整ValueAt(f,i,y) |
| appendSentence | 给定Seq(f,n,b)、y∈b及实际k=n∪{n}，实际存在唯一追加图g |
| existenceSentence | Omega(w)且b非空，则每个内部n∈w都有实际Seq(f,n,b) |
| naturalSentence | Omega(w)时，每个内部n∈w都有实际ω值序列 |
| naturalAppendSentence | 给定内部自然长度和值，实际取得k∈w及唯一追加图，保持全部原边 |
| prefixSentence | 给定Seq(f,d,b)及n⊆d，实际取得n上的完整前缀及精确边 |
| prefixUniqueSentence | 同一原图、限制域和界的两个精确前缀图相等 |

ObjectSequences对八句分别提供source_*、有限背景*_kernel_certificate、source_ZF_*及native_*。
所有native_*均返回FirstOrder.Derives nativeZF [] (Translation.sentence 对应闭句)。
没有通过模型语义、完备性或外部标准自然数枚举替代对象推导。

## 实际存在、精确边及全部内部长度
SequenceAppend从原Pairing和Union实际取得有序对、新域和新图；Foundation与Pairing给n∉n。
新图保持完整原FunctionOn。边刻画严格是：
Edge(g,i,v) ↔ Edge(f,i,v)∨(i=n∧v=y)。
追加结果还证明原f恰是g在原n上的实际限制，允许后续计算轨迹引用旧行。
两候选追加图由精确边双向传输及原图外延性相等；唯一性没有被当作结构字段输入。

SequencePrefix用一个明确原Separation实例实际取得前缀，证明完整FunctionOn、值域限制、原精确边和实际图唯一性。
SequenceLogic.value_at消去完整totalOn的实际唯一值见证，再由Bounded证明该值属于b。

SequenceExistence固定P(n):=∃f Seq(f,n,b)。空集给基例；逐步消去实际旧图并追加一个实际b成员给后继步。
原对象ω归纳推出∀n∈w∃f Seq(f,n,b)，覆盖任意内部ω成员，包括模型外部看来非标准的长度。
证明中未选择一个n↦f的全局宿主函数，也未把结论升级为一族同时选定的序列图。
当b=w时，由Omega(w)的实际空集成员得到b非空，因而取得全部内部自然数值序列。

有限背景T6仅含以下原句子：
Extensionality、Pairing、Union、Foundation、Separation(SequenceSyntax.existenceMatrix)、Separation(RestrictionSyntax.matrix)。
这是已验证充分背景，不宣称最小性。八句的Omega(w)是对象前件；没有额外调用Infinity取得w。
本批没有Replacement、Collection或对象AC输入。SequenceContext.Evidence只包装四个原公理证书，未假定任何序列结论。
内部序列依赖已收紧到既有对象ω与图设施；递归检索其PPAC导入闭包未发现Choice证明模块。

## 任意参数行公式的完整模式
CheckedSequence.rows(p,ρ,f):=∀i∀y(Edge(f,i,y)→p(ρ,i,y))。
CheckedSequence.checked把原完整序列与该行条件合取，p是任意有限纯公式，ρ保留全部参数。
新行满足p(n,y)时，精确追加边的旧/新两分支证明全行条件保持；新分支使用原对象等词替换对齐输入和值。
前缀的每条边传回原图，从而保留原行条件。
ObjectCheckedSequences为每个p提供appendSentence/prefixSentence的完整闭句、原核证书及源ZF/nativeZF回放。
这两个模式的源背景为空；未增加测试谓词、公理或统一内部真值断言。
模式是通用组合接口，不是ZF/U专用语法、公理、六规则或27逻辑模式的检查器。

## 实际验收与可信基
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；9条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成314个任务。
Check、CheckStep2、CheckStep3、新增CheckStep4和Audit均以--trust=0通过。
2434项审计：193项无公理依赖、2241项记录允许依赖；0条警告。
新增129项显式审计，其中13项无公理依赖。283个验收文件SHA256实际复核一致。
八个T6核心证书及两个空背景模式证书均恰为propext/Classical.choice/Quot.sound。
原nativeZF端点仍继承其类型和回放中的七个既有闭性证书，已按具体声明单列；不把它们称为仅标准三项。
本批未新增choice闭性证书依赖；原ChoiceNativeBridge的独立限域规则与两份可信基JSON均未改。
本批无sorry/admit、unsafe或新增自定义公理。原19规则和源ZF九类的原文锁定核对通过。
CheckStep4直接检查完整序列/自然长度/追加AST，以及基础闭句和任意参数模式的真正原核证书。
命令、日志、完整依赖与哈希保留本地verification/，没有推送GitHub。

## 下一步与最终完成门
下一主项4b是内部自然数算术及与原结构树码一致的编码/解码、唯一性和界性质。
源码核对以IntrinsicQuotationEvaluation.treeValue/forestValue为准：空结构列表数值为1，矛盾叶node(0,[])数值为2。
这与ProofCode中普通数列的空码0、NatPacket字节传输格式及旧Hilbert化quotation不同。
纯签名还必须保持无函数符号、membership编号0、全部11公式构造及bound/free上下文。
本批只核对这些原源码约定，未证明内部算术化正确性。
后续4c–4f须实际构造纯语法变换、ZF/U公理识别、原六规则/27逻辑模式检查及专用Con闭句，
再由步骤5证明任意内部证明码上的转换器正确性。原Con_ZF→Con_target对象主句、内部解释/对称强迫及模型应用仍未完成。
原OpenAI构建及Comparator仍未运行；不据序列前置宣称PP/AC分离或相对一致性完成。
