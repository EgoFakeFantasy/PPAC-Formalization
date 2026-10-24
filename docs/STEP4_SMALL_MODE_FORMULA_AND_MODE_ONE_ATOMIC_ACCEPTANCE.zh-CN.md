# 原小模式完整公式运行方程与 mode1 四原子程序验收

基点：7a047e736ecb1013cb604acd6a0a02901dbb5429。单元3f.2c.3b.2d.6h；10模块89项显式声明、17组原核闭句。

## 对象背景、内部 Con 和边界

对象语言仍为原纯等词／成员语言，背景为完整原ZF经Project.fo_theory的像，推导关系为原FirstOrder.Derives。固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6、七份锁定文件及原完整Separation／Collection保持不变。没有增加AC、不可达或Con前提。

内部Con继续按锁定规格 `¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))`：ω由唯一最小归纳集的纯成员公式消去，Proof_T检查全部内部证明码、原六规则／27逻辑模式和完整ZF／目标理论模式。没有外部标准ω限制。专用ProofZF/U的完整实现与正确性仍未完成，见[对象目标](OBJECT_TARGET.zh-CN.md)。

最终目标仍未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批有两个严格区分的结果：每个固定模式编号小于4的原Run3十一分支展开方程，以及任意内部深度mode1兼容frame下全部四原子输入的程序正确性。展开方程保留原递归子Run查询，不等于完整递归公式操作正确性；全公式归纳、forall节点、Proof／内部解释及最终Con尚未完成。

## 原十一分支 Run3 方程真实覆盖 mode1

旧OriginalFormulaRunEquation的Bool参数只覆盖mode0／3，不能把false解释为mode1。新证明从原常量守卫入手：

1. SmallModeFormulaMatrix把原常量mode<4守卫交给已证SmallModeArgumentsGuard；原常量规则与nil参数列规则在该守卫上精确相同。复用原constant_matrix_iff_head及原constant_at_row表达式推导，保留真实原head图。
2. SmallModeFormulaConstantApplication消去并重建原三槽arity赋值、环境自然性及赋值数值界；没有改写原常量矩阵接受条件。
3. SmallModeFormulaTrace只替换两个常量应用证明，其他九分支复用原关系应用、等词、否定、四二元连接词及两量词的原局部接口。原OriginalFormulaTraceEquation.outcomes AST未复制或修改。
4. SmallModeFormulaRun构造并消去实际根行码；反向由原outcomes自然性定理推出输入／输出自然性，再构造真正原行及轨迹。全根集合见证也在对象EX中取得和消去。

对每个固定外部modeIndex<4，实际对象合同为：

```text
Ω(w), Num(modeIndex,mode), depth∈w, P∈w
  ⊢ Run3(w,mode,depth,P,input,output)
       ↔ OriginalElevenOutcomes(w,mode,depth,P,input,output).
```

input/output为任意内部对象，不预给合法公式或自然性。modeIndex是有限模式族的外部编号，runtime深度、参数和语法码仍全部内部量化。native包装采用Fin4，并在trust=0检查中显式实例化modeIndex=1。

原outcomes中的Run1／Run2／Run3子查询、量词深度递增、规则标签、arity和对象赋值均保持原样。仅取得展开式不能宣称已证明整棵内部公式的正确性。

## 真实 frame 下的一致性前提均实际证明

SmallModeAtomicDispatch用新小模式Run3方程合并原outcomes排斥证明，取得两个常量、等词和成员的整条运行分派。

AbstractFrameAtomicAgreement.terms从前批任意深度frame项程序定理及真实checked／run双条件，在内部ALL2中推出AtomicTermAgreementSyntax.agreement。

pair_at_length从真实二项forest和typedInputs构造源列表，再将前批Run2逐字段映射接ArgumentPairProgramFields.mapped_iff。pair_iff实际构造Num2长度见证并在对象EX中消去；pair_agreement在内部ALL2中覆盖所有该二项forest输入及任意候选输出。因此项／二参数一致性是原核中的推论，不是新假设。

## 全部四原子输入的实际程序正确性

AbstractFrameAtomicExisting在真实frame下接入既有Constant／Member／Equality操作：

- 常量使用真实mode1整条运行分派与原ConstantExistingAtomBridge。
- 成员使用实际二参数agreement、原MemberProgramCase.application_iff及MemberExistingAtomBridge。
- 等词使用实际全项agreement及原EqualityExistingAtomBridge。

AbstractFrameTypedAtomic再用原SyntaxAtomLogic消去成员的三个源字段及等词的两个源字段。最终没有预给标量／项字段、长度或比较agreement前提。

AbstractFrameAtomic用AtomicProgramMerge合并四原子分支，并接既有FormulaTransformProgramSyntax中的原子程序。最终合同：

```text
Ω(w), Frame(w,mode,depth,P,a,b,c,e,R,S), Atomic(w,a,b,n)
  ⊢ Run3(w,mode,depth,P,n,q)
       ↔ AtomicProgram(w,R,S,a,b,c,e,h,n,q).
```

depth、源／目标上下文界、两码表、n/q以及程序历史参数h均是内部对象变量；候选输出不预给自然性／类型。该原子程序不需要公式递归IH或历史agreement。frame的实际Top根实例及原binder闭包已在此前证明，不把新的原子正确性当作frame定义的一部分。

## 原核证书与实际验收

ObjectAbstractAtomicFormula的17组闭句涵盖小模式常量守卫／矩阵／应用、原整条trace／Run3、四原子分派、实际项／二参数agreement、三个具体原子操作及合并程序；经原源传输和ZFReplay返回原nativeZF核。

1749构建任务、18749项声明审计（399无公理／18350允许依赖）、零警告；九条命令及五个trust=0入口全部退出0；1584份工作文件独立哈希一致、2172对精确核／native证书足迹、16405项Internal显式声明覆盖。

证据：`verification/small-formula-atomic-readback.json`、`verification/commands.json`及`scripts/verify.py`。独立复核检查每组核证书恰有三项标准依赖、native证书恰有同三项加既有七项固定依赖；展开真实mode1实例和完整四原子native合同；核查原长度EX、源字段EX、真实frame agreement推导及最终前提集合。

独立检查还禁止新路线调用旧Bool模式的公式／原子／成员run_iff接口，禁止宿主求值／选择预言机，并要求新证明文件复用既有接受／程序定义。原Run3／十一outcomes、原常量及公式规则、原原子程序、agreement AST、上一批frame／binder／项／参数列源码均保持Git字节不变。

新增“小模式完整公式运行方程”状态门指展开方程；新增“mode1全部四原子程序”门指上述原子合同。完整mode1递归公式／forall／专用Proof／Con的状态门仍为false。

## 继续实施表

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 原小模式Run3方程 | 常量守卫及arity、整条trace／真实根行EX | 每个固定mode<4的Run3↔原十一outcomes | 本批完成 |
| mode1四原子基例 | 实际项／二参数agreement、源字段EX消去、四分支合并 | 任意深度frame下完整原子程序双条件 | 本批完成 |
| 统一内部frame归纳 | 对mode/depth/P/a/b/c/e/R/S/q十个变化参数量化，接真实历史及原binder闭包 | 全部内部合法公式的原Run3↔实际完整执行 | 下一步 |
| forall节点 | 原嵌套node9头、四查询及四赋值界，接完整mode1公式变换 | 原完整纯关系节点双条件 | 待完成 |
| logical／theory／Proof／Con | 原27模式、完整ZF/U、共享quotation／Bool、内部编译及解释 | 原nativeZF内部Con_ZF→Con_target | 未证明 |

旧统一归纳的Bool frame要求源／目标绑定界相同并携带I/J索引图，不能直接套用于mode1。下一步须保留独立a/c绑定界，使用已证真实frame及其提升闭包，在对象归纳谓词内部量化全部变化参数，随后实际消去IH。
