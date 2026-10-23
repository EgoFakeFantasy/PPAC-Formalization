# 原首槽实例化与抽象quotation验收

2026-10-23；S3.4c.2b.2b.2。基点e085f94410a2d816e56ccd5387d8643c0e653e5f。
本批完成原InstantiateTop/AbstractFreeTop实际码表与具体原生替换的整表对应、专门公式双条件、原树操作quotation及实际带类型联合唯一纤维。
S3.4c.2b.2b的外部有限有效语法quotation模式部分已验收；任意内部AST统一正确性及最终Con尚未完成。

## 固定合同与精确对象结论

签名仍为原YesMetaZFC单排序纯等词/成员语言ℒ，背景原nativeZF使用完整Collection。
推导固定原FirstOrder.Derives；闭句封装返回原Hilbert证书，未新建推导核或采用模型/完备性捷径。
最终目标仍为 Derives nativeZF [] (Formula.imp Con_ZF Con_target)，target=ZF+PP+ACwo+¬AC。
Con_T仍要求¬∃p(p∈ω∧Proof_T(p,code⊥))，遍历全部内部ω证明码，保留六规则、27模式和完整Separation/Collection。
本批不改变该目标，不将外部模式索引误写成全内部AST统一断言。

外部模式为有限原生纯类型公式、替换项及其上下文；a、b、A、B、t、n、q及所有码表值均为内部对象变量。
设Q为原IntrinsicQuotation结构数值quotation。原核证明：

| 操作 | 对象守卫 | 全内部候选q上的对象双条件 |
|---|---|---|
| 首bound槽实例化 | Omega(w)、Num(|bound|,a)、Num(|free|,b)、Succ(A,a)、Q_replacement(w,t)、Q_input(w,n)，input:Formula(set::bound,free) | Instantiated(w,a,b,A,t,n,q) ↔ Q_(input.instantiateTop replacement)(w,q) |
| 首free槽抽象 | Omega(w)、Num(|bound|,a)、Num(|free|,b)、Succ(A,a)、Succ(B,b)、Q_input(w,n)，input:Formula(bound,set::free) | Abstracted(w,a,b,A,B,n,q) ↔ Q_(input.abstractFreeTop)(w,q) |

最终两条双条件不要求调用方提供R/S码表、内部图、字段正确性或目标quotation。
原实际首槽码表在对象存在量词中取得并消去；替换项原Term类型从其实际quotation及上下文numeral证明，不作为未来未证义务留下。

另有两条双条件将右侧直接写成固定原树操作的quotation：

- instantiateTree(termTree replacement,formulaTree input)，其中instantiateTree按原SyntaxSubstitution.formula固定零槽、旧bound前驱和free恒等；
- 原SyntaxSubstitution.abstractTop(formulaTree input)。

这两条通过已证明的严格原树编码桥接入本批对象推导，不是只定义别名或仅交付宿主树相等。
原始无效树的默认行为与合法输入下的检查关系保持区分；本批不声称对任意无类型树全域相等。

每个操作还实际取得同一内部q，联合满足原首槽判断、准确原生结果quotation及原目标FormulaCode，
并有∀v(原首槽判断(v)→v=q)。唯一性比较全部原内部候选，而不只比较预先带quotation的候选。

## 已实际消去的义务

| 单元 | 实现与对象证明 |
|---|---|
| 外部变量位置 | entryAt和sourceIndex是有限纯语法上的确定构造；index_entryAt和get_at精确恢复原生替换列表的变量位置，不从模型抽取值 |
| 具体原生替换 | instantiateBound/freeId及abstractBound/abstractFreeTop与底座定义严格对齐；free抽象函数相等用逐变量证明，未加入新算法或公理 |
| 实例化零槽 | 原Field双条件给出q=t，原实际替换项quotation唯一值刻画接到Q_replacement(q) |
| 实例化旧bound槽 | 内部解包索引后继numeral，实际前驱Num/index及Succ关系接到原bvar quotation；前驱见证消去 |
| 实例化free槽 | 原free字段保持原索引，给出对应fvar quotation |
| 抽象bound槽 | 实际取得内部后继索引及其numeral，接到后移bvar quotation；后继见证消去 |
| 抽象free零/后继槽 | 零槽转为bvar0，旧free后继槽恢复原free索引及fvar quotation；全部源域守卫保留 |
| 整表恢复 | 四类完整readings含全部内部位置/输出量词；原TermLists给出HasLength，由完整字段一致性及原列表码单射性恢复实际项像quotation |
| 原生环境 | 两类原首槽码表精确成为对应具体原生替换的NativeSubstitutionSyntax.environment |
| 公式接入 | 原首槽at_codes双条件与前批全11公式quotation组合，再实际取得/消去码表；嵌套量词沿前批实际binder对应处理 |
| 同值纤维 | 一个实际输出同时满足原操作、quotation、FormulaCode与对全部原首槽候选的唯一性 |

不假设内部ω外部标准、不假设模型外部良基，不固定统一秩或深度上界；没有宿主集合见证选择。
数值编码仍为原结构树/森林，不混用NatPacket字节码或旧quote_hilbert。未恢复退役反射实现。

## 文件与原核入口

新增10模块124显式声明，均位于PPAC/Migration/Internal/。

| 模块 | 职责 |
|---|---|
| NativeTopQuotationIndices | 确定变量位置、具体原生替换与底座对齐、专门原生公式变换等式 |
| TopQuotationVariableFields、TopQuotationReadings | 四类逐变量字段及完整内部字段读取 |
| NativeTopQuotationEnvironment | 原实际首槽码表到完整原生替换环境 |
| NativeTopQuotationAtCodes、NativeTopQuotationCorrespondence | 有实际码表入口及内部消去码表后的专门双条件 |
| NativeTopQuotationOriginal | 原SyntaxSubstitution树操作的专门quotation双条件 |
| NativeTopQuotationValueSyntax、NativeTopQuotationValue | 同值操作/quotation/类型纯AST及实际联合唯一纤维 |
| ObjectNativeTopQuotation | 20组Source闭句、原sourceZF及原nativeZF证书 |

主要入口为native_instantiateIff、native_abstractIff、native_instantiateOriginalIff、native_abstractOriginalIff、
native_instantiateFiber、native_abstractFiber。
封装路线仍是source闭句→TheoryTransport.sentence→ZFReplay.replay，返回原FirstOrder.Derives nativeZF []。

## 实际验收

执行 C:\Python314\python.exe -X utf8 scripts/verify.py，退出0。
独立执行.local/verify-native-top-readback.py，退出0；本地证据为verification/native-top-readback.json。
闭句初次封装曾因隐式上下文无法推断而失败；已显式传递bound/free并完整复跑，下表只记录修复后的最终验收。

| 验收项 | 实际结果 |
|---|---|
| 串行严格全仓构建 | lake --no-cache --wfail build，1137任务通过，LEAN_NUM_THREADS=1 |
| 声明依赖审计 | 12670项；345无公理依赖、12325符合记录依赖；0警告 |
| 命令与原核检查 | 九命令全部退出0，其中五个--trust=0入口全部退出0 |
| 新闭句精确依赖 | 20对core=std3、native=std3+原7证书，逐项相等 |
| 累计闭句精确依赖 | 1368对逐项核验 |
| Internal显式声明覆盖 | 10326项全部审计 |
| 独立源码/脚本SHA256回读 | 1035份全部匹配 |
| 七锁文件 | 相对本批基点全部不变 |
| YesMetaZFC固定底座 | 039c8e132cc19671d73a3933c66b4799d2599dd6；依赖工作区干净 |
| 缺口及额外公理审查 | 活动源码无sorry/admit/axiom/unsafe/native_decide；未关闭linter |

std3={propext,Classical.choice,Quot.sound}；原7证书精确基线见TRUST_BASELINE.json。
独立Choice桥保持原范围，宿主Prop等式证书不表示对象ZF加入AC。
新源码统一LF；旧基点文件换行保持不变，工作区字节哈希与提交blob换行差异分别记录。
未推送/创建PR；未运行原OpenAI全构建或Comparator；verification及.local证据保持本地。

## 后续工程流程

| 顺序 | 输入/动作 | 必须交付与验收 | 状态 |
|---|---|---|---|
| S3.4c.2b.2b.2 | 原首槽实际环境、具体原生替换与全公式quotation | 两类首槽专门双条件、原树操作quotation、实际带类型联合纤维 | 本批已验收 |
| S3.4c.2b.2c | 固定原数值程序、内部有效AST判断、现有全内部递归端点 | 独立有限程序/求值关系的实际表示及与原判断在任意内部有效AST上的统一正确性；准确处理无效候选，不以标准quotation实例替代 | 下一步 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 规则5/4在任意内部码上的精确检查兼容 | 待完成 |
| 5a/5b | 六规则、27模式、完整ZF/U公理 | 专用ProofZF/U有限纯AST及全部内部ω检查/编译正确性 | 待完成 |
| 6a | 原数学路线与对象递归 | 完整内部解释及目标ZF、PP、ACwo、¬AC的原核推导 | 待完成 |
| 6b | 内部解释、检查器和锁定Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

verify.py仅新增三个外部有效语法模式细门。广义全内部原操作/首槽总门、完整检查器和最终Con仍为False。
