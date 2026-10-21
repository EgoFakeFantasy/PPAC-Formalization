# 原列表码单射与完整双向往返验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点19843ac10f63732d9ad91a5e9e8f1b07ee8ae069。
本批关闭4b.c.4c.iv.c.ii。列表编码的两个方向已证明；递归语法检查器、树及最终内部Con仍未完成。

## 对象合同及实际结果

对象语言为纯等词/成员语言，背景为原ZF；推导使用Source.Derives，
经TheoryTransport及ZFReplay实际取得原FirstOrder.Derives nativeZF []闭句证书。
原背景、固定底座及Con_ZF→Con_target规格保持不变，没有新增对象AC、Con或模型假设。

Agree(w,r,a,b):=∀i∀y(i∈r→(Field(w,a,i,y)↔Field(w,b,i,y)))。
Ω(w)下，HasLength(w,a,r)、HasLength(w,b,r)和Agree(w,r,a,b)正式推出a=b。
所有长度、索引、码与输出对象均在对象层量化，包含外部看来非标准的内部ω成员。
最终闭句没有归纳性质、已知单射性或外部标准长度前提。

Encoding仍为(n∈w∧HasLength(w,n,L))∧Fields(w,n,L,F)。
任意原完整sequence(F,L,w)、L∈w在Ω(w)下实际有唯一编码纤维：
∃n(Encoding(w,F,L,n)∧∀a(Encoding(w,F,L,a)→a=n))。
候选码a没有外部枚举限制。

解码后再编码：HasLength(w,n,L)、Fields(w,n,L,F)、Encoding(w,F,L,a)推出a=n。
更强的实际见证闭句为：
Ω(w)∧Valid(w,n)→∃L∃F∃a(((HasLength(w,n,L)∧Fields(w,n,L,F))∧Encoding(w,F,L,a))∧a=n)。
这里L、F、a实际由已有解码及任意序列编码存在定理取得，未预设重编码结果存在或正确。

编码后再解码的另一方向使用上一批已验收的ObjectStructuralListEncode.native_readback：
Encoding(w,F,L,n)、HasLength(w,n,k)、Fields(w,n,k,g)推出k=L且g=F。
两者共同关闭列表层的完整双向往返；尚未把列表字段认定为有效语法树。

## 证明结构

在长度r上作原Separation支持的对象ω归纳，性质比较任意两个该长度的码。
空长度反演为两个原Nil，再由Nil输出唯一性得到码相等。
后继长度反演两个实际Cons；原自然数传递性、Foundation及后继输入单射性把两条尾长度对齐到给定前驱r。
实际空集索引属于后继长度，原零点字段式及Agree给出头相等。
每个i∈r实际取得后继j；其属于后继长度，两个原Cons字段后继双条件给出尾的全部字段Agree。
归纳假设应用于两个真实尾码，等词替换对齐头尾后，由原Cons输出唯一性推出原码相等。

精确Fields的全边双条件把同一个原Kuratowski字段图转换为Agree。
码单射给Encoding输出唯一性，再结合上一批实际编码存在取得唯一纤维。
实际解码长度、原完整字段图及重编码见证在对象存在消去作用域内完成原码恢复。
没有宿主List归纳、模型语义桥、外部良基或Type层选择数据抽取。

| 模块 | 实际职责 |
|---|---|
| StructuralListCodeSyntax | 全内部字段比较、长度归纳性质及带给定尾长度的实际Cons视图 |
| StructuralListCodeLength | 原后继输入单射、指定尾长度反演、Nil与后继长度互斥、实际Cons视图存在 |
| StructuralListCodeFields | 原等词头尾替换、头相等及全部尾字段双条件 |
| StructuralListCodeStep | 两个实际Cons分解见证及前驱归纳假设给后继长度码相等 |
| StructuralListCodeInduction | 实际空长度基例、原对象ω归纳及全内部长度码单射 |
| StructuralListCodeGraph | 精确同字段图推出Agree和原码相等、Encoding输出唯一性 |
| StructuralListRoundTripSyntax | 全候选编码唯一纤维及三个实际存在见证的原码恢复公式 |
| StructuralListRoundTrip | 实际唯一编码纤维、条件式原码恢复、有效码实际三重见证往返 |
| ObjectStructuralListRoundTrip | 十个完整闭句的源ZF、sourceZF原核核心及原nativeZF证明 |

## 十个完整原核闭句

| 端点 | 完整句子职责 |
|---|---|
| predecessor | 同一后继的两个输入相等，给定内部自然前驱 |
| consView | 指定实际后继长度反演为自然head、给定前驱长度tail及原Cons码 |
| heads / tails | 同后继长度字段比较推出头相等及前驱域全部尾字段相同 |
| codeUnique | 同实际长度、全部域内字段相同推出原码相等 |
| sameGraph | 同实际长度及同一个精确完整字段图推出原码相等 |
| encodedUnique | 同原完整序列的两个Encoding码相等 |
| encodingFiber | 任意内部完整ω值序列实际具有唯一原列表编码 |
| decodeThenEncode | 任意实际解码及重编码候选正式恢复原码 |
| roundTrip | 每个有效原码实际取得长度、完整图和等于原码的重编码值 |

每个端点有source_*、*_kernel_certificate及native_*。
CheckStep4核对Agree的全索引/全输出量词、最终单射句无归纳前提、唯一纤维比较全部码、
三重实际往返见证和全部十个原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成495个任务。
Check、CheckStep2、CheckStep3、CheckStep4及Audit五个入口均以--trust=0通过。
4243项声明审计：201项无公理依赖，4042项允许依赖；0警告。
本批9个模块84项声明全部显式审计；Internal具名声明覆盖门禁累计1928项。
464份源码SHA256独立复核，差异0；累计169对核心/native证书或模式精确依赖核对通过。
新增十个核心恰为标准propext/Classical.choice/Quot.sound，native端点恰额外继承原七个ZF闭性证书。
这些是Lean证明证书的依赖；未把对象AC加入背景。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、固定依赖及原核保持不变。
未新增自定义公理；未推送；原OpenAI完整构建及Comparator未运行。

本地独立回读：verification/internal-list-roundtrip-readback.json。
完整日志、依赖和哈希保留在本地verification/；未作为发布材料。
三个明确列表门禁已转为True：同长度同字段码单射、解码再编码恢复原码、完整双向往返。
实际唯一编码纤维另有独立True标志。
递归structural-list检查器的总检查/拒绝及树有效性未由当前关系式往返代替，相关总门禁仍为False。

## 下一最小工程

推进4b.c.4c.v：使用严格子码界构造全内部自然码上的实际递归列表检查轨迹，
证明接受恰对应原Valid、拒绝与有效码互斥；实际递归值存在唯一，不能把Valid当作判定预言机。
随后将已验收的完整字段图和原raw_node连接到树字段递归有效性，再处理全部11个原生公式构造。
专用ProofZF/U、任意内部证明码正确性、内部编译器及最终Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
