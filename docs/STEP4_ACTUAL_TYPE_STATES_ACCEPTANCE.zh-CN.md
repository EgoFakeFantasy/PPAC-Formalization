# 实际类型状态、原递归图与内部读取对应验收

日期：2026-10-22；分支migration/yesmeta-step3。
本批基点2d6e81b72fd54688d002e04bf8fa13459dd51720。
完成4c.b.1b实际Separation状态、4c.b.2算子总单值性，
以及4c.b.3中实际递归图/状态值和全部前段读取对应。
新增35个完整闭句模式实际取得原FirstOrder.Derives nativeZF []证书。
完整11构造的历史无关递归类型式、原编码识别正确性、内部替换、ProofZF/U及最终Con仍未完成。

## 对象合同与组合局部判据

语言仍为原纯等词/成员，背景为原ZF；数学证明先用Source.Derives，再回放到原nativeZF核。
原19规则、九类源ZF、两份可信基和固定依赖不改。
没有新增对象AC、Con、不可达或新谓词公理；类型判断只是有限纯公式的定义缩写。
全部内部候选码、上下文长度、状态集合、历史图和递归图都保留为对象变量。
外部Fin 4/Bool只索引有限原构造模式，不限制内部自然数或候选码取值。

Local(w,b,f,h,n)是四种Atomic与neg、四种binary、forall、exists的精确有限析取。
没有默认接受分支，量词仍通过实际Succ(k,b)查询(k,f)。
原核证明Local保留Ctx(w,b,f)，并在Ω(w)下推出n∈w。
局部模式引入、任意非单射变量重命名、bound/free等词替换均有实际推导。

## 实际Separation状态与唯一性

Row(w,n,h,p):=∃b∃f(Ordered(p,b,f)∧Local(w,b,f,h,n))。
State(w,C,n,h,V):=∀p(p∈V↔(p∈C∧Row(w,n,h,p)))。
一个原三参数完整Separation实例实际构造V；不要求索引n自然或历史h已是函数。
原Extensionality证明同输入状态唯一，并构造包含真实全称唯一性公式的对象存在纤维。

状态满足V⊆C，故给定实际PowerOf(U,C)，有V∈U。
所有状态成员都属于C且有真实上下文对见证；非上下文对杂项被排除。
给定真实Ordered(p,b,f)，原有序对分量单射性证明Row(w,n,h,p)↔Local(w,b,f,h,n)。

给定实际A=P(w)、C=P(A)及State，原核对任意内部b,f证明：
Edge(V,b,f)↔Local(w,b,f,h,n)。
反向实际构造落在C中的Kuratowski上下文对，再由Separation方程得到其属于V。
不以“任意编码约定”或宿主对值替代真实对象见证。
非法Ctx被拒绝；Ω(w)且n∉w时实际状态为空。

## 具体集合值算子与原超限递归

递归矩阵最后三槽明确为索引n、真实历史h、输出V；前两参数为w,C。
Step(w,C,n,h,V)就是上述实际State公式。
原Separation证明每个内部输入/历史实际有输出，原Extensionality证明输出单值。
这两个前提在对象层实际消去后，实例化已证明的原超限递归模式。

结果是在全部内部原序数域上存在唯一完整递归图，保留原functionOn和每步真实限制历史方程。
没有使用宿主WellFounded、外部标准ω、宿主递归函数或从Prop中抽取集合数据。
还实际取得三层幂集A/C/U及该C上的全部唯一递归图，载体没有停留为额外未证存在前提。
非自然原序数上的状态值为空，作为实际默认行为证明，而不是在宿主分支中指定一个值。

## 实际状态值及前段对应

Evaluation(w,C,n,V)实际存在后继域s和完整递归图g，
保留Succ(s,n)、Graph(w,C,g,s)及原Edge(g,n,V)。
每个内部原序数n有实际输出；特别地，每个内部n∈ω有实际输出。
任意两个实际后继域/完整图的输出都相等，并有真实内部全称唯一性纤维。

任意更长内部原序数域上的递归图，其域内边恰好等价于对应索引的Evaluation。
兼容性使用原对象序数/图证明，覆盖全部内部索引，不只核对外部标准证明码。
每个实际状态值还具有完整前段递归图h，并满足State(w,C,n,h,V)；
该历史是实际限制集合，没有把历史替换为外部函数。
状态值满足V⊆C及V∈U的统一界。

## 内部类型判断与真实读取

Typed(w,C,n,b,f):=(n∈w)∧Ctx(w,b,f)∧∃V(Evaluation(w,C,n,V)∧Edge(V,b,f))。
这是真实有限纯对象公式，保留根自然码与两侧上下文守卫。
非法码/上下文的拒绝直接在对象核中证明。

给定原序数n、n∈w和任意实际Evaluation值V，原核证明：
Typed(w,C,n,b,f)↔Edge(V,b,f)。
类型不依赖所选实际后继域或递归图。

给定完整前段Graph(w,C,h,d)、原序数d、x∈d及x∈w，原核进一步证明：
Read(h,x,b,f)↔Typed(w,C,x,b,f)。
因此可以在后续全11递归式中消去历史读取，用真实内部类型判断描述子式；
量词体仍须在实际后继bound下使用该对应，不能冻结原始bound。

## 模块和实际验收

17个新模块共243项显式声明，全部列入Audit。
FormulaLocal两模块组合11分支；TypeState四模块构造/唯一化状态并证明成员关系；
TypeRecursion/Recursors三模块取得实际原递归图；
TypeEvaluation/GraphValues/History五模块证明实际值与全部前段对应；
TypeJudgment两模块给出内部类型公式和读取等价；ObjectSyntaxTypeStates提供35个完整闭句模式。

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：两个固定源锁检查、Lean版本、全仓wfail构建，
以及Check/CheckStep2/CheckStep3/CheckStep4/Audit五份lake env lean --trust=0入口。
实际结果：595个构建任务；5778项声明审计；235项无公理依赖、5543项允许依赖；0警告。
Internal累计3463项显式声明全覆盖；累计365对核心/native证书或模式精确足迹通过，新增35对。
新增核心证书恰为propext、Classical.choice、Quot.sound；native端点另继承原七项ZF证书。
Classical.choice在这里是Lean证明基础依赖，没有引入对象AC；原choice额外证书仍单独限域。
564份源码SHA256独立重算差异0，所有可信基和原规则/理论锁不变。
YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
独立回读verification/syntax-type-states-readback.json；日志/探针/哈希不入库。
本批未推送；原OpenAI完整构建和Comparator未运行。

## 下一关和未完成边界

下一步定义不含历史参数的11构造递归判据，用已证Read↔Typed替换严格子码处的历史读取，
并证明完整Typed双条件，尤其forall/exists的真实后继bound分支。
还须证明原编码识别/构造的正确性，不能把本批“状态集合实际存在”当作全部类型正确性已经完成。
因此原完整11公式类型/完整上下文类型正确性门禁暂仍False；实际状态存在和前段对应另有精确True门禁。
之后仍需内部非单射捕获规避替换、ZF/U原规则/模式检查、任意内部证明码正确性、内部编译器，
以及最终原FirstOrder.Derives nativeZF [] (Formula.imp Con_ZF Con_target)。
