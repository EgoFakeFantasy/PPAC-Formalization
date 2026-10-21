# 任意内部字段序列的实际列表逆编码验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点c22a7747adb782c8c2f54094f0975bba9ed93547。
本批关闭4b.c.4c.iv.c.i；不同候选码的唯一性及完整双向往返尚未完成。

## 对象合同

语言仅含等词与∈，背景原ZF，不新增对象Choice、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport/ZFReplay取得
原FirstOrder.Derives nativeZF []完整闭句，原核及固定依赖不改。

Encoding(w,F,L,n):=(n∈w∧HasLength(w,n,L))∧Fields(w,n,L,F)。
Ω(w)、L∈w及原完整sequence(F,L,w)实际推出∃n Encoding(w,F,L,n)。
原source sequence含完整functionOn并限制所有边值属于w，排除杂项及遗漏输入。
输入仅为任意此类内部图及内部自然长度，不假定它已有列表编码，不使用宿主List或外部有限实例。
所得码的HasLength仍保留原Nil/Cons完整构造迹；Fields为已证完整有序图合同。

## 精确长度及固定源后缀归纳

原Nil在任意实际空长度z上有HasLength；原Cons将尾的给定实际长度r构造为指定后继s。
这由真实有效性/长度存在、原精确前驱长度及长度唯一性对齐取得，未只交付Valid。
空实际长度也在对象核中反演为原Nil。

Aligned(w,F,k,r,n)量化所有内部i,q,y：i∈r及Sum(w,k,i,q)时，
Field(w,n,i,y)↔edge(F,q,y)。Coded保留n∈w、HasLength(w,n,r)及完整Aligned。
固定F和总长L，对全部内部r作原Separation支持的ω归纳，性质量化所有k∈w且r+k=L，实际取得Coded见证。
零点实际构造原Nil；后继步实际取得j=Succ(k)、旧后缀码、F在k处的自然head和新原Cons码。
指定后继长度由上述构造取得，字段零点读取新head，后继读取旧尾码并由内部偏移加法精确对齐。
全部偏移、head、旧码和新码均由对象存在消去处理，未抽取宿主选择函数。

零偏移和全长度实例取得完整源序列的字段逐点双条件。
原functionOn的无杂项成员分解及Kuratowski对唯一性将其提升为精确Graph(w,n,L,F)，
所以编码后完整Fields图就是原给定F，而非仅同值的超集。
编码对象实际满足Valid；任意HasLength(w,n,k)、Fields(w,n,k,g)的解码均证明k=L且g=F。
后者是编码后解码的图读回，不是不同编码码之间的唯一性。

| 模块 | 实际职责 |
|---|---|
| StructuralListLengthConstruct | 指定长度替换、Nil实际零长度、Cons实际后继长度、空长度反演Nil |
| StructuralListSuffixSyntax/Arithmetic | 全内部后缀量词、偏移后继加法和前驱成员界 |
| StructuralListSuffixBase/Match/Step/Induction | 实际空码、原Cons逐字段对齐、全部见证后继构造及对象ω归纳 |
| StructuralListEncodeSyntax/Graph/Existence | 完整逆编码合同、原源图恢复、任意原完整内部序列的实际编码 |
| StructuralListEncodeReadback | 码有效性和任意实际解码的原长度/图读回 |
| ObjectStructuralListEncode | 13个完整闭句的源ZF/sourceZF原核核心/原nativeZF证书 |

## 完整闭句

| 句子 | 内容 |
|---|---|
| nilLengthSentence / consLengthSentence | 原Nil给定零长度；原Cons给定尾长度的指定后继长度 |
| emptyLengthSentence | 实际空长度反演Nil，无需Ω |
| offsetSentence | 原后继偏移与自然字段索引的加法转换 |
| suffixZeroSentence / suffixConsSentence | 实际空后缀码；原Cons前置保持源偏移全部字段 |
| suffixSentence / fullSuffixSentence | 任意内部r+k=L的实际后缀码；实际零偏移全长码 |
| graphRecoverySentence | 原完整functionOn和域内字段双条件恢复精确Kuratowski图像 |
| zeroFieldsSentence | 零偏移全长匹配恢复给定源F的完整Fields |
| existsSentence | 任意原完整内部ω值序列和内部自然长度实际取得Encoding见证 |
| validSentence | Encoding实际推出原Valid |
| readbackSentence | 任意实际解码恢复编码时的原长度和原图 |

每句有source_*、*_kernel_certificate和native_*。
CheckStep4核对实际逆编码的自然码/原构造迹/给定图、后缀全偏移量词、编码前提未假定已有编码，
以及任意解码读回与全部13个原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成486个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
4159项声明审计：201项无公理依赖，3958项允许依赖；0警告。
12个新模块102项声明全部显式审计；Internal具名声明覆盖门禁累计1844项。
455份源码SHA256独立复核一致，差异0；累计159对核心/native证书或模式精确依赖核对通过。
本批13个核心恰为标准三项，native端点恰额外继承原七个ZF闭性证书。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、原依赖和原核保持不变。
未新增自定义公理，未推送；原OpenAI完整构建和Comparator未运行。
本地回读verification/internal-list-encode-readback.json；日志/依赖/哈希仅本地保留。

下一关以对象内部长度归纳证明同长度/同字段码相等，取得实际唯一编码纤维，
再证明解码后重新编码恢复原码，完成两个方向的往返。
当前码唯一性、反向原码恢复、完整双向往返、树、专用ProofZF/U及最终内部Con仍未完成。
