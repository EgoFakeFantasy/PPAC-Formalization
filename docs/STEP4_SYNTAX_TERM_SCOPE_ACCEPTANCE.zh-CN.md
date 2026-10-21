# 变量反向解码与纯项内部作用域验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点45f278450e4321156751961a6547bfc376af2c5a。
本批完成4c.a.ii：字段反向恢复、变量唯一内部索引解码、纯项scope和拒绝性质。
全部11公式类型、上下文状态递归、内部替换、ProofZF/U及最终Con仍未完成。

## 固定对象合同

语言仅含等词/成员，背景仍为原ZF。数学证明均为Source.Derives，
通过TheoryTransport/ZFReplay取得原FirstOrder.Derives nativeZF []完整闭句证书。
未新增对象AC、Con、外部标准ω或推导核；固定原19规则、九类ZF和原编码均保持。

外部有限字段数k和字段位置只索引有限公式模式；每个实例实际返回原核证明。
变量索引i、上下文长度b/f、候选码n和payload p始终是对象变量，量化全部内部集合/ω。
Fin m用于公式变量槽位，不把内部自然索引限制为外部有限集合。

## 同码字段及变量反向恢复

先对每个有限字段向量证明：相同Forest码反推出每个相应字段相等。
原Cons输入单射性同时恢复头和尾，真实尾码通过对象等词替换对齐，再递归处理剩余有限字段。
同码原raw节点由原配数单射性恢复payload；相同有限字段数的Node及Constructor恢复所有字段。
这些反向结论不使用“同一输入编码唯一”代替字段解码。

不同有限字段数的森林互斥：实际构造两个内部数码长度，原HasLength唯一性要求长度相等，
不同数码的实际非等词证明导出矛盾。原raw输入单射性把该排除传到任意自然标签的节点。
因此裸scalar叶和缺失/多余字段不能通过单字段变量封装。

Var_mode(w,i,n)仍是原bvar/fvar标签0/1的单scalar字段。
先恢复该单字段scalar码，再用scalar的索引单射性，证明任意两个同码变量的内部索引相等。
IndexUnique_mode(w,n,i):=∀j(Var_mode(w,j,n)→j=i)，候选j不预先限制在某个scope内。
IndexFiber实际存在i，保留i∈w、真实Var和完整IndexUnique。
原核证明Recognized_mode(w,n):=∃i Var_mode(w,i,n)恰好等于IndexFiber。
索引自然性从实际scalar标签guard推出；未从宿主解码器取索引，也未假定标准ω。

## 纯项scope的精确对象关系

纯签名没有函数符号，因此项只可能是bound/free变量。
Ctx(w,b,f):=b∈w∧f∈w。
Branch_mode(w,l,n):=∃i(i∈l∧Var_mode(w,i,n))。
Term(w,b,f,n):=Ctx(w,b,f)∧(Branch_bound(w,b,n)∨Branch_free(w,f,n))。
两个内部上下文长度都保留，即使当前项只使用其中一个。

Ω(w)和已知Var_mode(w,i,n)下，原ZF核证明：
Term(w,b,f,n)↔(Ctx(w,b,f)∧i∈相应的b或f)。
正向真实解出候选索引，使用反向变量索引单射性恢复给定i，并排除相反变量类别。
反向把给定内部scope成员与原变量码组成真实项见证。

给定Ctx及合法内部索引，先由内部自然数传递性推出i∈ω，再用原变量构造器实际构造自然项码。
ExistsAt保留n∈w、原Var_mode(w,i,n)和Term三项；存在性前件不假设已经有某个码。
此结论覆盖内部非标准长度和索引。

DecodedBranch实际存在相应scope中的索引，保留原Var及对全部候选的IndexUnique。
DecodedTerm保留两个上下文guard和bound/free解码分支。
原核证明Term↔DecodedTerm；两个解码分支互斥，分支内实际索引唯一，且所有Term码属于内部ω。
这些是纯项关系和正确性证书，不把模型语义或宿主Option结果当作对象推导。

## 错误scope及形状排除

已知变量码而索引不属于对应scope时，Term被拒绝；两个空上下文中不存在任何纯项。
不同字段数互斥正式排除非单字段节点及裸scalar；异标签互斥排除标签不为0/1的构造器。

另有更完整的raw拒绝句：Ω(w)、Num_label(t)、p∈w、Raw(w,t,p,n)，label≠0且label≠1时，
正式推出¬Term(w,b,f,n)。特别地，label=2拒绝所有函数应用标签。
该句量化任意内部自然payload p，不要求某个外部固定字段数，也不假设payload是有效森林。
因此函数标签排除覆盖内部非标准长度；固定有限字段构造器的排除模式只是额外实例。
另有全对象未知标签拒绝句：任意内部t∈ω若满足¬Num_0(t)∧¬Num_1(t)，则任意自然payload的Raw(w,t,p,n)都不是纯项。
该句没有外部Nat标签参数，覆盖非标准内部标签；证明由raw标签恢复实际Var的0/1数码再与对象否定冲突。

| 新模块 | 职责 |
|---|---|
| SyntaxForestInjective | 同码原森林逐字段反向恢复和码等词替换 |
| SyntaxNodeInjective | 同码节点/构造器字段恢复、标签guard和任意raw标签比较 |
| SyntaxForestArity/NodeArity | 实际数码长度排除不同字段数；变量单字段要求 |
| SyntaxVariableDecodeSyntax/Decode | 实际唯一内部索引纤维、反向单射、识别双条件、异类/raw标签排斥 |
| SyntaxTermSyntax | 纯项scope、真实索引分支、完整解码和实际码存在公式 |
| SyntaxTermBranches | 分支scope双条件、索引解码、自然值域、互斥及空域排除 |
| SyntaxTerms | 完整scope双条件、合法索引实际项码、解码双条件、空/错域排除 |
| SyntaxTermReject | 错标签/字段数/scalar排除；任意内部payload的函数标签拒绝 |
| ObjectSyntaxTerms | 27个完整源ZF及原nativeZF闭句模式 |

27个端点为forestInput、nodeInput、constructorInput、forestArity、nodeArity、indexNatural、
indexInjective、variableDecode、indexFiber、branchScope、branchDecode、scope、termExists、termRange、
termDecode、branchExclusive、decodedExclusive、rejectScope、rejectEmpty、rejectTag、rejectFunction、
rejectArity、rejectScalar、branchEmpty、rawRejectTag、rawRejectFunction、rawRejectUnknownTag。
每个有source_*、*_kernel_certificate、native_*；字段数/标签非等条件是外部有限公式模式的条件。
对象候选、索引和payload不因此缩小。
CheckStep4核对两个上下文guard、真实Var索引见证、全候选唯一性、任意payload函数拒绝句及全部27个端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成556个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit五个入口均以--trust=0通过。
5104项声明审计：215项无公理依赖，4889项允许依赖；0警告。
本批11个新模块188项显式声明全部审计；Internal具名覆盖累计2789项。
525份源码SHA256独立复核，差异0；累计272对核心/native证书或模式精确依赖通过。
新增27组核心恰依赖propext/Classical.choice/Quot.sound；native恰额外继承原七项ZF闭性证书。
原choice额外证书继续限域；对象ZF没有新增选择公理或自定义公理。
两份可信基JSON、原19规则/九类ZF锁、固定依赖和原核不改；锁文件Git复核仅规范化检出CRLF。
原YesMetaZFC为039c8e132cc19671d73a3933c66b4799d2599dd6且工作区干净。
独立回读verification/syntax-terms-readback.json；日志/哈希/完整足迹仅本地verification/。
未推送；原OpenAI完整构建与Comparator未运行。

## 下一主项

4c.a.iii.a先处理membership唯一编号0的scalar字段、falsum/truth和原子式/等词的局部项类型。
再完成五个联结词及两个量词的局部类型分支，量词子式bound必须取真实内部后继。
4c.b实际构造全部内部上下文的类型状态及递归图，随后4c.c完成非单射捕获规避替换。
纯项scope门禁现True；全部公式类型、上下文类型递归、内部替换、ProofZF/U及最终Con仍False。
最终目标仍为原核Derives nativeZF [] (Con_ZF→Con_target)，没有缩小背景、结论或全内部ω范围。
