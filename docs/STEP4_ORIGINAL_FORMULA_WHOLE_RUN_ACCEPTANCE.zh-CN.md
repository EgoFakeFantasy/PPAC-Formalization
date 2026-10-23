# 原十一公式整体运行方程验收

基点：0a70586aae55e53dff4fbeac778502adcd919d17。完成S3.4c.2b.2c.3c.2c.2b.3e.2／3e.3。这里证明原运行的精确递归方程；完整有类型公式变换对应和最终内部Con仍待证明。

## 对象合同

保持YesMetaZFC原等词／成员语言、原nativeZF完整Collection及原FirstOrder.Derives。背景不加AC、不可达、外部标准ω或模型良基性。最终句子仍为Derives nativeZF [] (Con_ZF → Con_target)，其中target=ZF+PP+ACwo+¬AC，内部Con量化全部内部ω证明码，要求原六规则／27模式及完整Separation／Collection。内部Con定义及证明码规格沿用OBJECT_TARGET，不以宿主Consistent替代。

每组新句子都有实际Source.Derives，经TheoryTransport.sentence及ZFReplay.replay到原核。three、tag、kind及原规则成员证书为固定外部模式索引；全部运行时变量、组件、赋值和后继深度均由对象变量或内部存在量词处理。没有定义内部统一真值谓词，没有调用退役反射。

## 整体方程与量词

OriginalFormulaRunEquation.run_iff实际证明，在Omega(w)、Num0或Num3(μ)、depth∈w及parameter∈w守卫下：

```text
Run₃(w,μ,depth,parameter,n,q) ↔ Outcomes(w,μ,depth,parameter,n,q).
```

Outcomes严格按原十一规则顺序排列：

| 分支 | 对象数值条件 |
|---|---|
| constant 0、1 | 两个零元构造码，输入／输出同tag |
| application 3 | ∃symbol,args,newArgs，两个真实App结构且Run₂(args,newArgs) |
| binary 3 1 | ∃x,y,X,Y，两个等词构造码且两个真实Run₁子运行 |
| unary 4 false | ∃x,X，两个否定构造码且深度不变的真实Run₃ |
| binary 5、6、7、8 3 | 各∃x,y,X,Y，同tag构造码且两个深度不变Run₃ |
| unary 9 true、10 true | 各∃D，Successor(D,depth)且∃x,X，同tag构造码及深度D的Run₃ |

析取末尾保留⊥以逐字匹配原HornStepSyntax.step的空表值，不增添成功分支。所有子运行均沿用原完整28规则表。没有预给n／q自然性、对应形状或类型；这些性质在原application比较中恢复，并由Outcomes正式推出n,q∈w。

关系App仍是此前实际Scalar、Cons载荷、Num2及RawNode的三对象存在定义。纯成员memberCode的固定symbol0／两参数森林连接尚未证明，不能把一般App视为已完成纯成员原子迁移。

## 赋值消去和重建

正向逐原arity=3／5／6／7消去实际赋值存在块。实际head五字段图给出mode、depth、parameter与赋值前三字段的对象等式，再用等词传输对齐真实子运行。反向从原根行取得前三字段自然性，从真实子运行恢复组件自然性，从App的实际Scalar结构恢复符号索引自然性，重建原自然赋值、实际head搜索界和原规则应用。

量词分支保留实际对象Successor。不同后继见证用原外延性证明唯一并正式传输整个一元分支。Pairing／Union在对象ZF内构造后继见证，消去后不残留外部D或宿主depth+1前提。

十一组application双条件按原selected列表合成。原Separation构造的实际通用轨迹集合V在证明内取得并消去；随后从各分支的真实构造恢复输入／输出自然性，构造真实五字段根行并消去。最终Run₃方程不要求预给V、根行、赋值或输入／输出自然性。

## 文件和原核闭句

| 模块 | 对象产物 |
|---|---|
| OriginalFormulaApplicationNaturality | App输出及实际符号索引自然性 |
| OriginalFormulaCaseSyntax | 二元／一元／量词／应用内部存在公式、重命名及引入 |
| OriginalFormulaDataSubstitution | 子运行元数据及整个一元分支的对象等词传输 |
| OriginalFormulaBinderDepth | 不同真实后继见证对齐 |
| OriginalFormulaArityApplications | 常量／二元／否定／应用arity双向消去 |
| OriginalFormulaBinderApplication | 量词arity双向消去及内部后继存在消去 |
| OriginalFormulaTraceEquation | 十一分支合成及实际V消去 |
| OriginalFormulaOutcomesNaturality | 全部内部组件分支的自然输入／输出 |
| OriginalFormulaRunEquation | 去预给根行的整体Run₃双条件 |
| ObjectOriginalFormulaEquation | 十组Source→TheoryTransport→ZFReplay闭句 |

闭句族为：

- originalFormulaConstantAssignmentEliminated
- originalFormulaBinaryAssignmentEliminated
- originalFormulaNonbinderAssignmentEliminated
- originalFormulaBinderAssignmentEliminated
- originalFormulaApplicationAssignmentEliminated
- originalFormulaBinderAtActualSuccessor
- originalFormulaElevenCasesAtTraceValue
- originalFormulaElevenCasesAtRow
- originalFormulaElevenCasesInputOutputNatural
- originalFormulaWholeRunElevenCases

## 实际验收

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalFormulaEquation与C:/Python314/python.exe -X utf8 scripts/verify.py实际退出0。全仓1438构建任务，15722项审计（380无公理／15342允许依赖），零警告。九命令及五个--trust=0入口全部退出0，构建严格串行且LEAN_NUM_THREADS=1。

新增10模块84显式声明，10组核心证书依赖精确为propext、Classical.choice、Quot.sound；native证书精确为这三项加原七固定句子语法证书。全仓1748对精确证书足迹、13378项Internal显式声明覆盖。独立回读1302份工作区SHA256无差异，七锁及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态均不变。没有新增自定义公理或对象AC；隔离Choice桥未修改。

此前45个执行／分支定义和两个独立字段像定义的直接oracle检查保留；纯公式定义检查从六项扩至十五项，新增八个内部存在body／case和Outcomes。不调用宿主Expr.eval或旧变换答案作为执行原语。实际日志及独立证据保留本地verification/commands.json、audit.log、formula-equation-readback.json；未推送或创建PR，未运行OpenAI全仓／Comparator。

## 状态门与下一步

原arity赋值消去与Run₃整体十一分支方程两个细门现为true，已验收参数列表全内部字段对应保持true。

3f.1须先连接原App结构与纯成员symbol0／实际两参数森林；3f.2建立对变化运行参数内部量化的公式归纳性质，并证明量词真实环境／像列表提升，随后取得有类型全公式双向对应、实际输出与唯一性。不能只把原子／连接词有限分支检查当作全内部公式归纳。

原扩展语言quotation总桥、完整数值Option接口、ProofZF/U全内部检查／编译、内部解释和最终内部Con蕴含均未完成。局部或全仓构建与公理审计不替代这些对象证明。
