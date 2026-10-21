# 原Gödel配数对象推导验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点7a41813af64dd2a02a15e729fff03ceb389033c3。
本批关闭流程4b.c.1和4b.c.2。4b.c.3全内部码逆解码和最终内部Con主句仍未完成。

## 对象语言、背景和固定关系

对象签名仅含等词和∈。源推导为Source.Derives (Source.SetLanguage.ZF.at n)，
经既有TheoryTransport和ZFReplay返回原YesMetaZFC的FirstOrder.Derives nativeZF []闭句。
背景仍为原ZF，无对象AC、不可达或Con前提；没有修改底座推导核。

令Omega(w)为已证实际最小归纳集，Add/Mul为已证全内部自然值关系。
以下所有平方、和、后继和不等式均为纯对象关系，不是Lean数值运算。
below(x,y)展开为x=y∨x∈y。固定原配数：

- Lower(w,a,b,p) := ∃q (Mul(w,b,b,q)∧Add(w,q,a,p))。
- Upper(w,a,b,p) := ∃q∃t (Mul(w,a,a,q)∧Add(w,q,a,t)∧Add(w,t,b,p))。
- Pair(w,a,b,p) := (a∈b∧Lower(w,a,b,p))∨(¬a∈b∧Upper(w,a,b,p))。

严格分支a∈b以及高支的逐次和次序均按固定底座原约定保留。
CheckStep4以rfl核对这三个公式及完整单射闭句，未调用原InternalPairingRules中的ZFC模型语义证明。
全部内部自然输入均被覆盖，包括模型外部看来非标准的自然对象；没有外部标准码限制。

## 七个闭句及其原核证书

下表均含Omega(w)，其他自然前提按表逐项保留；所有自由对象变量由.close全称闭合。
每行提供source_*、*_kernel_certificate及native_*，均在ObjectGodelPair模块。

| 句子 | 完整结论与前提边界 |
|---|---|
| fiberSentence | a,b∈w下存在p∈w使Pair(w,a,b,p)，且每个满足Pair的任意对象q均等于p |
| closureSentence | Pair(w,a,b,p)推出p∈w；该句不额外假定输入自然性 |
| valueUniqueSentence | a,b∈w且Pair(w,a,b,p)、Pair(w,a,b,q)推出p=q；候选p、q无额外标准码或ω前提 |
| componentsSentence | a,b∈w且Pair(w,a,b,p)推出below(a,p)∧below(b,p) |
| injectiveSentence | a,b,c,d∈w且Pair(w,a,b,p)、Pair(w,c,d,p)推出a=c∧b=d |
| lowerBandSentence | a,b∈w、a∈b及Lower(w,a,b,p)推出Band(w,b,p) |
| upperBandSentence | a,b∈w、¬a∈b及Upper(w,a,b,p)推出Band(w,a,p) |

Band(w,x,p)是两个纯对象全称句的合取：
∀q(Mul(w,x,x,q)→below(q,p))，以及
∀s∀v(Succ(s,x)→Mul(w,s,s,v)→p∈v)。
它给出[x²,(x+1)²)的严格平方区间，未使用宿主max或sqrt。

## 证明结构与工程模块

| 模块 | 实际证明职责 |
|---|---|
| GodelPairSyntax | 原分支纯AST、所有重命名交换、实际见证引入与消去 |
| GodelPairBranchExistence、GodelPairPolynomial | 实际取得自然平方及逐次和；ω闭包及每支输出唯一 |
| GodelPairCore | 两支总存在、完整输出唯一、实际唯一自然输出fiber及守卫精确等价 |
| GodelPairArithmetic、GodelPairBounds | 和界、抵消、平方后继式、后继弱界、双分量不超过编码 |
| GodelPairIntervals | 原低支/高支严格小于相应后继平方；中间和实际存在 |
| GodelPairBandSyntax、GodelPairBands | 纯全称平方区间公式及每支实际区间证书 |
| GodelPairBandUnique | 内部实际后继和两个平方见证证明相同输出的区间指标唯一 |
| GodelPairCancellation | 同指标下余数抵消；混合分支因严格和界矛盾而不交 |
| GodelPairInjective、ObjectGodelPair | 四种分支组合的完整输入单射性；七个闭句及原核回放 |

相同输出首先固定平方区间指标；同支使用平方/和唯一性对齐中间值，再抵消余数。
混合支对齐平方后得到p∈t，而另一支得到below(t,p)，由内部自然顺序排除。
所有ZFContext.Evidence字段仍仅是原ZF公理包含关系，算术事实由此前证书实际推导，不作为新输入公理。

## 实际验收记录

执行C:/Python314/python.exe -X utf8 scripts/verify.py，退出0。
九条正式命令及退出码记录于本地verification/commands.json，全部为0：
原19规则锁定检查、源九类ZF锁定检查、Lean版本、完整构建，以及五个--trust=0检查/审计入口。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成396个任务。
3232项声明审计：198项无公理依赖、3034项记录允许依赖；0条警告。
本批13个模块的98项显式声明均已审计；365个验收文件SHA256实际复核一致，差异0。

verify.py精确核对累计60个算术/顺序/配数核心证书及对应native端点。
本批七个*_kernel_certificate的依赖恰为propext、Classical.choice、Quot.sound；
七个native_*依赖恰为这三项加固定底座原有七项FreeClosed证书。
原choice额外证书仍限制在原桥接范围；两份可信基JSON、原核及固定依赖没有改变。
未新增自定义公理、sorry/admit、unsafe或native_decide，没有对象Choice输入。
本地verification/summary.json记录精确依赖、哈希及完成标志；日志和探针不作为GitHub发布材料。
原OpenAI完整构建和Comparator未运行；未远端推送。

## 下一关：全部内部自然码的实际解码

现有单射性只给出已存在解码的唯一性；尚不能推出每个p∈w均有解码。
4b.c.3必须构造纯公式Unpair(w,p):=∃a∈w∃b∈w Pair(w,a,b,p)，
证明Omega(w)→∀p∈w Unpair(w,p)，然后装配实际唯一解码闭句及原nativeZF证书。

| 顺序 | 实现工作 | 必须验收的对象结果 |
|---|---|---|
| 1 | 内部零点配数 | 实际空集z下Pair(w,z,z,z)，实际取得两个自然分量 |
| 2 | 低支后继 | a∈b时实际取得Succ(t,a)；t∈b时Pair(t,b)给编码后继，t=b时转高支Pair(b,z) |
| 3 | 高支后继 | b≤a；b∈a时提升第二分量，b=a时借平方后继式转低支Pair(z,Succ(a)) |
| 4 | 对象ω归纳 | 对每个内部编码p推出实际分量存在，不以宿主递归或标准码枚举代替 |
| 5 | 解码唯一及原核闭句 | 用本批输入单射性得到两分量唯一；正反对应及范围/界全部保留对象量词 |
| 6 | 结构列表/树 | 按原节点后继封装构造内部编码/解码和子码界，保留空结构列1、叶0数值2 |

专用全11构造语法、六条原核规则/27逻辑模式检查器、完整ZF/U公理识别、内部编译器及最终
FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
