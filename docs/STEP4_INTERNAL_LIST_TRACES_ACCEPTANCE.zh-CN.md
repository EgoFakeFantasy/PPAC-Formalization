# 内部有限列表轨迹与双向递归式验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点4627673476c32b2fb77ab1b520a57f9bc9099f05。
本批关闭4b.c.4c.i–iii。精确一步分解已完成；唯一长度、实际完整字段图和完整解码仍未完成。

## 对象合同与纯轨迹

语言仍仅含等词和∈，背景仍是原ZF，不加对象AC、不可达、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport和ZFReplay取得
原FirstOrder.Derives nativeZF []完整闭句证书。原核与固定依赖未改。

Step(w,a,b):=∃h(h∈w∧Cons(w,h,a,b))。
Row(w,f,i)实际存在j,a,b，满足Succ(j,i)、edge(f,i,a)、edge(f,j,b)及Step(w,a,b)。
Links(w,l,f):=∀i(i∈l→Row(w,f,i))。

Trace(w,z,e,l,d,f,n)包含：Empty(z)、Nil(w,e)、l∈w、Succ(d,l)、
原SequenceSyntax.sequence(f,d,w)、edge(f,z,e)、Links(w,l,f)及edge(f,l,n)。
sequence保留原完整functionOn和对全部边的ω值域约束。
Valid(w,n):=∃z∃e∃l∃d∃f Trace(w,z,e,l,d,f,n)。
长度和完整图均为内部集合对象，包含模型外部看来非标准的内部自然长度。
不以宿主List、外部有限标准实例、外部WellFounded或统一真值谓词代替。

## 实际构造、迁移和反向前缀

从实际空序列追加实际内部单位值，取得完整单点Nil轨迹；长度为内部零，域为其实际后继。
Cons追加先由原序列追加取得实际新图。所有旧行的后继/前后值/Cons见证通过旧边包含逐个迁移，
新末行单独由旧末值、新Cons值和实际后继索引构造，再用后继成员分解拼成全部新Links。
未直接套用图参数已变化的旧rows模式。

反向处理中，零长度轨迹的种子与末索引由原Empty唯一性对齐，再由完整函数图单值性得到Nil末值。
后继长度l=Succ(p)时，末行实际取得前后值及Cons见证；后继唯一性对齐其新索引与l，图单值性对齐末值。
实际限制图f↾l提供长度p、域l的前缀。i∈p时，其后继j≤p，故两个行索引都属于l；
两条旧边实际限制到新图，保留该行Cons见证和全部前缀Links。
种子零索引属于l也在对象核中证明，完整序列和实际末值均保留，从而取得实际有效尾。

## 精确对象结果

Omega(w)下已证明：
Valid(w,n)↔Nil(w,n)∨∃t(Valid(w,t)∧∃h(h∈w∧Cons(w,h,t,n)))。
这是两个方向的实际Derives，包含全内部有限轨迹的实际存在见证。
已知h,t∈w和Cons(w,h,t,n)时，Valid(w,n)↔Valid(w,t)。
反向有效尾由上述分解、Nil/Cons互斥及Cons输入单射性取得，不预设其有效。
有效码属于w且非零；每个实际Empty(z)都被证明不满足Valid(w,z)。

| 模块 | 实际职责 |
|---|---|
| StructuralListTraceSyntax/Properties | Step/Row/Links/Trace/Valid纯AST、五重内部见证引入/消去、轨迹投影和范围 |
| StructuralListTraceRows | 旧行迁移、Links包含迁移、后继长度新末行拼接 |
| StructuralListTraceBase/Append | 实际Nil种子、实际序列追加、新轨迹和Valid的Cons闭包 |
| StructuralListValidity | 全内部有效尾上的实际Cons闭包及有效码属于w |
| StructuralListTraceOrder/Prefix | ω成员闭包、对象替换、实际前缀图和全部前缀行保持 |
| StructuralListDecodeSyntax | Nil或存在有效尾/自然head的纯分解公式 |
| StructuralListTraceInvert | 内部长度零/后继分解、实际前缀和有效码反向分解 |
| StructuralListDecode | 双向递归式、已知Cons的尾有效性反射、正值及零码排除 |
| ObjectStructuralListTrace | 十个完整闭句及源ZF/sourceZF原核核心/原nativeZF证书 |

## 十个闭句

下表除rangeSentence外均保留Omega(w)，自由对象变量全部.close全称闭合。

| 句子 | 其他前提与完整结论 |
|---|---|
| baseSentence | Empty(z)、Succ(e,z)→实际存在Trace(w,z,e,z,e,f,e)的完整图f |
| appendSentence | 自然head h、实际旧Trace和Cons(w,h,n,y)、Succ(k,d)→实际存在长度d、域k、末值y的新完整Trace |
| nilValidSentence | Nil(w,n)→Valid(w,n) |
| consValidSentence | h∈w、Valid(w,t)、Cons(w,h,t,n)→Valid(w,n) |
| rangeSentence | Valid(w,n)→n∈w，此句无需Omega前提 |
| recursiveSentence | Valid(w,n)与上述完整Nil/有效尾Cons分解的实际双条件 |
| consIffSentence | h,t∈w及Cons(w,h,t,n)→(Valid(w,n)↔Valid(w,t)) |
| positiveSentence | Valid(w,n)→¬Empty(n) |
| zeroRejectedSentence | Empty(z)→¬Valid(w,z) |
| prefixSentence | p∈w、Succ(l,p)、旧Trace及edge(f,p,a)→Valid(w,a)，实际构造前缀图 |

每句均有source_*、*_kernel_certificate及native_*。
CheckStep4直接核对实际长度/域/完整图/种子/行条件、Valid五重内部对象量词、分解中的有效尾和自然head，
以及Cons有效性双条件、实际零码排除和十个原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成430个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3590项显式声明审计：200项无公理依赖、3390项允许依赖；0警告。
本批12个模块、118项新增声明均进入审计；399个文件SHA256实际复核一致，差异0。
累计94个算术/顺序/编码核心证书与对应原nativeZF端点由verify.py精确核对依赖。
本批十个核心恰为propext、Classical.choice、Quot.sound；原native端点恰为这三项加七个原有闭性证书。
原choice额外证书限域、两份可信基JSON、固定底座和原核未变；未新增自定义公理或对象Choice输入。
原19规则及九类源ZF锁定检查通过。原OpenAI完整构建和Comparator未运行；未远端推送。
命令、依赖、哈希和独立复核仅保留本地verification/；复核文件为internal-list-traces-readback.json。

## 下一项与未完成边界

当前一步分解已经实际取得有效尾和自然head，但还没有证明任意两条同码轨迹长度相等，
也没有实际构造唯一完整字段图。因此object_internal_structural_list_validity_and_decode_proved仍为False。

| 顺序 | 下项实现 | 对象验收门 |
|---|---|---|
| 1 | 精确前驱前缀接口 | 从现有valid_prefix构造提取existsTrace(w,z,e,p,l,a)，保留固定长度/域和实际图；同时保留末Cons见证 |
| 2 | 唯一内部长度 | 在一条轨迹的内部长度上作对象ω归纳，比较任意另一条同码轨迹；Nil/Cons互斥及单射对齐尾码与前驱长度 |
| 3 | 实际字段图 | 原Replacement精确收集唯一相邻head，实际取得有界完整函数图；用内部自然差分恢复原字段顺序 |
| 4 | 原顺序往返 | 全内部有效码实际解码及重编码双向正确，唯一长度和字段图均有原核闭句 |
| 5 | 列表检查/树 | 覆盖全部内部码的有效解码或拒绝，再按严格子码界接入树字段及完整语法 |

树、全11语法构造及bound/free长度、27逻辑模式、六规则和全Separation/Collection检查仍待完成。
全ω二元运算图未单独交付；内部ProofZF/U、任意内部码正确性、内部编译器、构造解释、实际对称强迫
及最终FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成，相关完成标志保持False。
