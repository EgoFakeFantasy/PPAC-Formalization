# 原生全11公式替换quotation验收

2026-10-23；S3.4c.2b.2b.1。基点699914ee8f98f25bfbbc15dd3f97f0caf929483a。
本批完成原生变量替换的实际项像环境、原生项替换，以及全11公式替换的对象quotation双条件和实际带类型联合唯一纤维。
S3.4c.2b.2b中的首槽专门对应仍待完成；最终内部Con蕴含仍未证明。

## 对象合同与准确范围

对象语言仍为原YesMetaZFC单排序纯等词/成员语言ℒ；背景为原nativeZF（完整Collection）。
推导固定原FirstOrder.Derives，封装返回原Hilbert证书，没有增加新核、公理、模型前提或完备性捷径。
最终目标仍为 Derives nativeZF [] (Formula.imp Con_ZF Con_target)，target=ZF+PP+ACwo+¬AC。
内部Con仍要求¬∃p(p∈ω∧Proof_T(p,code⊥))，量化全部内部ω证明码，保留六规则、27模式和完整Separation/Collection。
本批不改变这一目标，也不把下述外部公式模式等同于任意内部AST的统一正确性。

模式参数为原生纯类型公式φ:Formula(sb,sf)，以及原生变量替换
σ:VariableSubstitution(sb,tb,tf)、τ:VariableSubstitution(sf,tb,tf)。
σ、τ允许非单射，其像项可含两类目标变量。公式/替换是外部有限语法模式索引。
实际ω、四个上下文长度、两张项像码表、输入码及全部候选输出码仍是对象变量。

设Q_φ(w,n)为原IntrinsicQuotation结构数值quotation，Env_στ为原实际项像环境。
在Omega(w)、Num(|sb|,a)、Num(|sf|,b)、Num(|tb|,c)、Num(|tf|,d)、
Env_στ(w,a,b,c,d,R,S)及Q_φ(w,n)下，原核对每个内部候选q证明：

MixedFormulaSubst(w,R,S,a,b,c,d,n,q)
↔ Q_(φ.substituteMapped σ τ)(w,q)。

这是真实对象双条件，非Lean宿主层的树等式，也不要求候选q已带未来目标quotation或类型假设。
此外实际取得同一内部q，联合满足原MixedFormulaSubst、准确目标quotation及原FormulaCode(w,q,c,d)，
并证明∀v(MixedFormulaSubst(w,R,S,a,b,c,d,n,v)→v=q)。
唯一性比较全部内部原替换候选，不只比较预先带quotation的候选。

## 具体实现及消去的义务

| 单元 | 实现与已证明结果 | 验收边界 |
|---|---|---|
| 原生变量替换列表 | 递归列出显式变量替换的像项，长度等于原source上下文长度；entry.index字段精确等于σ(entry) | 显式语法数据，不抽取内部集合值 |
| 原生量词提升 | images(liftBound σ)=newBound(images σ)；images(weakenBound τ)=shifted(images τ) | 严格列表等式只作对象证明接口 |
| 实际环境 | 四个准确内部长度numeral下实际取得唯一项像环境；原CodedMixedBinder实际输出是原生提升后环境 | 图、头码已在前批对象定理内消去 |
| 原生项替换 | 原CodedMixedTermSubst对全部内部q精确对应原生Term.substituteMapped的quotation | 保留原变量index与原项码的区别 |
| falsum/truth | 原零元构造字段，quotation唯一性给出原端点所需码相等 | 两个原构造均保留 |
| equality/membership | 实际取得四个源/目标子项码；membership另取原编号0的scalar码；准确原字段接到两项替换判断 | 未把符号码当作索引或裸0 |
| negation及四种二元逻辑 | 实际取得源/目标子公式quotation，原全构造字段与递归假设组成原替换判断 | neg/conj/disj/imp/iff全部覆盖 |
| forallE/existsE | 内部实际构造源/目标后继长度；取得原提升码对K/H；在准确原生liftBound/weakenBound环境下调用归纳假设 | A/C、K/H及子码全部在对象存在量词中消去 |
| 全候选双条件 | 反向由实际构造证明；正向实际取得期望目标quotation码，原MixedFormula全候选唯一性及对象等词传输得到候选quotation | 不留下未来构造器分类/存在性前提 |
| 实际带类型联合纤维 | 同一q满足原操作、准确quotation、FormulaCode与针对全部原候选的唯一性 | 不以三个彼此独立存在的证书替代同值见证 |

全公式构造按原生11构造递归，显式保留当前source上下文索引并泛化目标上下文。
嵌套量词的两类目标像均按原定义提升；没有外部ω标准性、外部良基、统一秩界或深度上界假设。
没有恢复退役反射实现；数值格式仍为原结构树/森林，不混用NatPacket字节码或旧quote_hilbert接口。

## 文件与原核入口

新增11模块、99个显式声明，均在PPAC/Migration/Internal/。

| 模块 | 职责 |
|---|---|
| NativeSubstitutionImages | 原生变量替换的显式有限项像列表及index/提升交换 |
| NativeSubstitutionSyntax、NativeSubstitutionEnvironment | 原生替换实际环境AST、存在唯一纤维和对象binder对应 |
| NativeTermQuotationSubstitution | 原生项替换与原CodedMixedTerm判断精确双条件 |
| FormulaQuotationAtomicSteps、FormulaQuotationLogicalSteps | 原全11构造的精确字段组合步骤 |
| NativeFormulaQuotationConstruct | 完整11分支对象构造；实际消去子码、后继长度和提升表见证 |
| NativeFormulaQuotationCorrespondence | 全内部候选q上的精确quotation双条件 |
| NativeFormulaQuotationValueSyntax、NativeFormulaQuotationValue | 同值操作/quotation/FormulaCode纯AST及实际联合唯一纤维 |
| ObjectNativeFormulaQuotation | 16组Source闭句、原sourceZF及原nativeZF证书 |

主要入口：native_termIff、native_formulaConstruct、native_formulaIff、native_formulaFiber。
证书路线为source闭句→TheoryTransport.sentence→ZFReplay.replay，返回原FirstOrder.Derives nativeZF []。
局部原子/逻辑步骤中的实际字段前提在完整construct定理中由对象存在量词实际取得，未当作未完成假设交付。

## 实际验收

执行 C:\Python314\python.exe -X utf8 scripts/verify.py，退出0。
独立执行.local/verify-native-formula-readback.py，退出0；本地证据为verification/native-formula-readback.json。

| 验收项 | 实际结果 |
|---|---|
| 串行严格全仓构建 | lake --wfail build，1127任务通过，LEAN_NUM_THREADS=1 |
| 声明依赖审计 | 12546项；337无公理依赖、12209符合记录依赖；0警告 |
| 命令与原核检查 | 九命令全部退出0，其中五个--trust=0入口全部退出0 |
| 新闭句精确依赖 | 16对core=std3、native=std3+原7证书，逐项相等 |
| 累计闭句精确依赖 | 1348对逐项核验 |
| Internal显式声明覆盖 | 10202项全部审计 |
| 独立源码/脚本SHA256回读 | 1025份全部匹配 |
| 七锁文件 | 相对本批基点全部不变 |
| YesMetaZFC固定底座 | 039c8e132cc19671d73a3933c66b4799d2599dd6；依赖工作区干净 |
| 缺口及额外公理检查 | 活动源码无sorry/admit/axiom/unsafe/native_decide；未关闭linter |

std3={propext,Classical.choice,Quot.sound}；原7证书精确基线见TRUST_BASELINE.json。
独立Choice桥保持原范围；宿主Prop经典证书不表示对象ZF加入AC。
新源码统一LF，旧基点文件保留既有换行；工作区精确字节哈希与提交blob换行差异分开记录。
未推送/创建PR；未运行原OpenAI全构建或Comparator；verification及.local证据保持本地。

## 后续工程流程

| 顺序 | 实现职责 | 必须交付与验收 | 状态 |
|---|---|---|---|
| S3.4c.2b.2b.1 | 原生变量替换与全11公式 | 实际环境、原生项/公式精确quotation及实际带类型联合纤维 | 本批已验收 |
| S3.4c.2b.2b.2 | 实际InstantiateTop/AbstractFreeTop环境 | 原首槽码表与具体原生替换列表对应，专门原操作quotation，消去实际环境见证 | 下一步 |
| S3.4c.2b.2c | 原数值程序/规格与合法AST | 任意内部有效AST统一操作正确性及准确无效候选处理，不以标准quotation实例代替 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 规则5/4对任意内部码的精确检查兼容 | 待完成 |
| 5a/5b | 六规则、27模式、全ZF/U公理 | 专用ProofZF/U有限纯AST，全部内部ω检查/编译正确性 | 待完成 |
| 6a | 原数学解释路线与对象递归 | 完整内部解释及目标ZF、PP、ACwo、¬AC的原核推导 | 待完成 |
| 6b | 内部解释、检查器和锁定Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

verify.py仅新增三个精确的外部原生语法模式细门。
首槽总门、任意内部AST原操作、完整检查器及最终Con总门继续为False。
