# 全内部递归列表检查及接受/拒绝正确性验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点e7f7505150cf022e1ff17c0f7d2415fc153c3e55。
本批关闭4b.c.4c.v.a：列表检查轨迹的实际终止、首个终端存在唯一、完整接受/拒绝正确性及接受后解码。
树有效性、专用ProofZF/U、内部编译器及最终内部Con仍未完成。

## 对象合同

语言为原纯等词/成员语言，背景原ZF；使用Source.Derives，
经TheoryTransport和ZFReplay得到原FirstOrder.Derives nativeZF []完整闭句证书。
不新增对象AC、Con或外部标准ω假设；固定依赖、原核及原内部Con规格保持不变。

原真实tail递归Iteration_tail保留实际后继域、完整原递归图及实际边见证。
检查器使用该递归在全部内部自然索引上的第一次停止：

Terminal(w,b):=Empty(b)∨Nil(w,b)。
Occurs(w,n,r):=∃b(Iteration_tail(w,n,r,b)∧Terminal(w,b))。
Eventually(w,n):=∃r(r∈w∧Occurs(w,n,r))。
Before(w,n,r):=∀i(i∈r→¬Occurs(w,n,i))。
CheckedAt(w,n,r,b):=(((r∈w∧Iteration_tail(w,n,r,b))∧Terminal(w,b))∧Before(w,n,r))。
CheckValue(w,n,b):=∃r CheckedAt(w,n,r,b)。
Accepts(w,n):=∃b(CheckValue(w,n,b)∧Nil(w,b))。
Rejects(w,n):=∃b(CheckValue(w,n,b)∧Empty(b))。

这些定义不引用原Valid、不调用宿主判定器；其依赖为已证明总单值的原tail投影及实际内部递归。
Before排除所有更早内部索引上的终端事件，防止有效码越过Nil后再到空集而被误判。
所有运行长度、码、输出及中间图都是对象量词，不限制为外部标准数或外部有限实例。

## 实际证明

Ω(w)、n∈w推出Eventually(w,n)。
在n上沿原严格尾码界作对象成员归纳：有Cons时实际取得自然head/tail，
tail严格属于n；其实际终端执行经已证明的一步种子移位前置，得到n的终端执行。
没有Cons时实际取得空集零和原tail单步，再前置实际空终端执行。
该存在证明不预设列表有效性；Nil和无效码均在覆盖范围内。

原Foundation和一个明确Separation实例在w中取得最小终端事件索引。
内部自然数传递性给出Before条件，再实际取得该索引的终端值。
任意两组CheckedAt的自然索引可比较；严格较早的一组违反另一组Before，因此索引相等。
原实际递归输出唯一性给出终端值相等。每个内部自然码都有实际CheckValue唯一纤维：
∃b(CheckValue(w,n,b)∧∀c(CheckValue(w,n,c)→c=b))。

非终端的一步原tail关系保持并反射Valid：Cons分支使用已证原Cons有效性双条件；
无Cons分支由原Nil/Cons分解排除输入有效性，空输出也已证明无效。
在执行索引上作对象ω归纳，结合实际前驱求值、Before前驱限制和真实递推步，
得到首次终端之前及该终端处的Valid双条件。
终端为空集时无效，为原Nil时有效，故正式取得：

- CheckValue(w,n,b)→(Valid(w,n)↔Nil(w,b))。
- CheckValue(w,n,b)→(Empty(b)↔¬Valid(w,n))。
- n∈w→(Valid(w,n)↔Accepts(w,n))。
- n∈w→(¬Valid(w,n)↔Rejects(w,n))。
- n∈w→Accepts(w,n)∨Rejects(w,n)，且两者互斥。

上述各句在Ω(w)下均有实际原核Derives。两个关于CheckValue输出的局部双条件明确保留已有检查值前提；
最终接受/拒绝及完整分类闭句只要求Ω(w)和n∈w，不预设终止性、归纳性质或已有检查值。
原Nil被接受、实际空码被拒绝。接受还实际产生已验收的唯一内部长度和完整有序字段图解码见证。
这些是列表层检查；尚不检查字段是否是有效语法树，也不充当专用ProofZF/U。

## 模块与闭句

| 模块 | 已完成职责 |
|---|---|
| StructuralListCheckSyntax | 纯对象首次终端、检查值、唯一纤维及接受/拒绝定义 |
| StructuralListCheckTerminationPoint/Termination | 实际终端执行的单步前置及沿严格尾码界的对象归纳 |
| StructuralListCheckMinimal | 原Foundation/Separation取得首个终端及实际检查值 |
| StructuralListCheckUnique | 任意首个终端的索引/值唯一及实际唯一检查纤维 |
| StructuralListCheckPreservationStep | 非终端一步保持/反射原Valid；无Cons分支正确性 |
| StructuralListCheckInvariantSyntax/Step/Invariant | 所有内部执行索引上的停止前有效性不变量 |
| StructuralListCheckCorrectness | 接受/拒绝双条件、互斥完整分类、Nil/零边界及实际解码 |
| ObjectStructuralListCheck | 十六个完整源ZF/sourceZF原核核心/原nativeZF闭句 |

十六个端点为termination、exists、fiber、indexUnique、valueUnique、preservesStep、invariant、
acceptValue、rejectValue、acceptsIff、rejectsIff、exclusive、decodeAccepted、nilAccepts、zeroRejects、classification。
每个端点均有source_*、*_kernel_certificate及native_*。
CheckStep4逐项核对停止条件、实际递归、首次停止全索引排除、实际检查纤维、接受/拒绝定义、
覆盖全部内部自然码的最终双条件及全部十六个原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成506个任务。
Check、CheckStep2、CheckStep3、CheckStep4及Audit五个入口均以--trust=0通过。
4397项声明审计：201项无公理依赖，4196项允许依赖；0警告。
本批11个模块154项声明全部显式审计；Internal具名声明覆盖门禁累计2082项。
475份源码SHA256独立复核，差异0；累计185对核心/native证书或模式精确依赖核对通过。
新增十六个核心恰为标准propext/Classical.choice/Quot.sound，native端点恰额外继承原七个ZF闭性证书。
这些是Lean证明证书的依赖，未将对象AC加入背景。
两份可信基JSON、原choice额外证书限域、原19规则/九类源ZF、原核及固定依赖不改。
未新增自定义公理；未推送；原OpenAI完整构建与Comparator未运行。

独立回读保留于本地verification/internal-list-check-readback.json；完整日志/依赖/哈希仅本地保留。
列表实际递归检查、接受/拒绝正确性及完整列表有效性/解码门禁现为True。
树、专用ProofZF/U、任意内部证明码正确性、最终内部Con及相对一致性主定理门禁仍为False。

## 下一最小工程

4b.c.4c.v.b先证明有效原列表的每个域内字段值严格属于原列表码，覆盖全部内部长度和字段索引。
组合原raw_node载荷的严格成员界，得到树子字段严格小于父码，支撑全内部码上的树递归检查。
随后证明树有效/无效分支和实际解码，再按原标签、纯成员签名、bound/free上下文及全部11个原生公式构造接入。
最终目标仍为原Derives nativeZF [] (Con_ZF→Con_target)，不能从当前检查器或编译成功宣称该主句完成。
