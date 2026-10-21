# 实际完整有序字段图与唯一列表解码验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点b21d8b4b48632e79f545f3718a6b42ba63b88337。
本批关闭4b.c.4c.iv.b.ii.c；任意字段序列的逆编码及双向往返尚未完成。

## 对象合同与实际图

语言仅含等词与∈，背景原ZF；不新增对象Choice、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport/ZFReplay得到
原FirstOrder.Derives nativeZF []完整闭句。原核及固定依赖不改。

Field(w,n,i,y):=∃t(Iteration_tail(w,n,i,t)∧Step_head(w,t,y))。
每个内部自然i有实际唯一字段值y∈w，种子n可为任意内部集合。
原自然Cons(w,h,t,n)下，实际空索引z给Field(w,n,z,y)↔y=h；
r∈w及Succ(s,r)给Field(w,n,s,y)↔Field(w,t,r,y)。原迹中Cons的head也有直接字段读取双条件。

Entry(w,n,i,p):=∃y(Field(w,n,i,y)∧Ordered(p,i,y))，Ordered严格使用原Kuratowski编码。
字段值唯一性和原有序对唯一性给每个自然索引的实际唯一索引对。
对任意l∈w，原Replacement实际构造精确像：
Graph(w,n,l,g):=∀p(p∈g↔∃i(i∈l∧Entry(w,n,i,p)))。
没有从Prop抽取宿主选择函数，也没有把收集超集当作精确图。

所有图成员实际分解为域内原有序对；原对单射性解出正确输入/字段值。
反向以原Pairing实际构造有序对并用精确像加入图，给任意内部i,y的全边双条件：
edge(g,i,y)↔(i∈l∧Field(w,n,i,y))。
每个域内i有实际唯一值，图同时排除杂项，因此满足原完整functionOn(g,l)。
所有边值属于w，所得图为原完整sequence(g,l,w)。原Extensionality给精确图唯一性。

Fields(w,n,l,g)合取完整sequence、Graph和全边精确式；
Ω(w)、l∈w下实际存在Fields图，且所有仅满足Graph的候选图都与之相等。
Decoded(w,n):=∃l∃g((l∈w∧HasLength(w,n,l))∧Fields(w,n,l,g))。
Ω(w)下Valid↔Decoded，且任意两组实际长度/Fields图都有长度和图相等。
解码仍保留原实际HasLength构造迹；本批未证明任意字段序列的逆编码或码唯一性。

| 模块 | 实际职责 |
|---|---|
| StructuralListFieldSyntax/Values/Cons | 真实tail后取head、全索引实际自然值总单值、原Cons零/后继双条件 |
| StructuralListFieldPairSyntax/Pairs | 原Kuratowski索引对唯一纤维、原Replacement实际精确像 |
| StructuralListFieldGraphSyntax/Entries/Edges | 完整图合同、图元无杂项、任意输入和值的精确全边式 |
| StructuralListFieldGraphFunction/Fiber | 原完整functionOn、ω值域、实际唯一完整图纤维 |
| StructuralListFieldDecode/Trace | Valid实际解码与长度/图联合唯一；原迹head直接读取对应 |
| ObjectStructuralListFields | 15个完整闭句的源ZF/sourceZF原核核心/原nativeZF证书 |

## 完整闭句

| 句子 | 内容 |
|---|---|
| valueFiberSentence | Ω、自然索引→实际唯一自然字段值纤维 |
| valueRangeSentence | Ω、实际Field→值属于ω，无需额外索引自然性 |
| zeroSentence / successorSentence | 原Cons字段零点及后继双条件 |
| pairFiberSentence / rawExistsSentence | 实际唯一原索引对；指定自然长度的实际精确图像存在 |
| edgeLawSentence | 精确图像→全边精确式，无需Ω |
| completeSentence | Ω、自然长度、精确图像→完整Fields合同 |
| graphUniqueSentence | 任意两个精确图像相等，无需Ω |
| fiberSentence / atLengthSentence | 任意自然长度/原实际HasLength→实际唯一完整字段图 |
| decodeSentence / decodeIffSentence | Valid实际解码；Ω下Valid↔Decoded |
| decodeUniqueSentence | 同码两组实际长度和完整Fields图联合唯一 |
| traceHeadSentence | 原迹反向位置上的自然Cons，其head恰为该索引的字段值 |

每句均有source_*、*_kernel_certificate和native_*。
CheckStep4核对真实Field见证、精确原Kuratowski图像、完整合同、实际唯一图无额外函数前提、
实际解码长度/图见证和全部15个原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成474个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
4057项声明审计：201项无公理依赖，3856项允许依赖；0警告。
13个新模块141项声明全部显式审计；Internal具名声明覆盖门禁累计1742项。
443份源码SHA256独立复核一致，差异0；累计146对核心/native证书或模式精确依赖核对通过。
本批15个核心恰为标准三项；native端点恰额外继承原七个ZF闭性证书。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、固定依赖和原核保持不变。
未新增自定义公理，未推送；原OpenAI完整构建和Comparator未运行。
本地回读verification/internal-list-fields-readback.json；日志/依赖/哈希仅本地保留。

下一关对任意原完整ω值序列和内部自然长度实际构造列表码，用固定源序列/总长的后缀不变量作对象ω归纳。
再证同长度/同字段码唯一，完成双向编码/解码往返。当前字段图解码不替代该逆编码定理。
完整往返、树、专用ProofZF/U、内部编译器及最终内部Con仍未完成。
