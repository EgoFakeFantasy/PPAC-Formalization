# 原十一公式分派与局部数值矩阵验收

基点：43d25e64165c1e8d88054490fd0338b8eae428a4。完成S3.4c.2b.2c.3c.2c.2b.3e.1：原kind3全部十一规则的完整表分派、局部数值矩阵及真实子运行合成。尚未消去原arity赋值块、尚无去预给根行的Run₃整体方程，不能称完整公式递归已迁移。

## 对象合同及模式索引

固定原YesMetaZFC纯等词／成员语言、原nativeZF完整Collection和原FirstOrder.Derives。最终目标保持Derives nativeZF [] (Con_ZF → Con_target)，target为ZF+PP+ACwo+¬AC；内部Con仍要求全部内部ω证明码、原六规则／27模式和完整Separation／Collection。最终Con未证明。

每组闭句都有实际Source.Derives证明，经TheoryTransport及ZFReplay返回原核。没有增加对象AC、标准ω、外部良基、模型或新公理核，没有使用退役反射。Rule、tag、childKind、binder是外部固定模式索引；静态成员证书只证明模式属于原十一条，不是内部RuleCode检查器。运行时环境分量、元数据、输入／输出及中间码均为对象变量或对象存在见证，定理模式不误变成内部统一真值断言。

## 原完整表精确分派

原表28条不变。kind3五字段行上，全部原一步推导精确等价于以下十一条的原application析取：

| 原规则 | 含义 | 原子／公式子运行 |
|---|---|---|
| constant 0、constant 1 | 两个零元常量 | 无子运行，保留mode<4原守卫 |
| application 3 | 关系应用 | kind2参数列表运行 |
| binary 3 1 | 等词 | 两个kind1项运行 |
| unary 4 false | 否定 | 一个kind3公式运行，深度不变 |
| binary 5／6／7／8 3 | 四个二元连接词 | 两个kind3公式运行，深度不变 |
| unary 9 true、unary 10 true | 两个量词 | 一个kind3公式运行，深度为实际后继 |

其他17条的原head外层kind为0、1或2，由对象原节点标签互斥拒绝。分类静态核查全部原规则；实际排除及dispatch双条件均在Source.Derives中完成。在实际通用轨迹集合V处，原Trace也精确等价于该十一规则原step。这里仍要求原kind3候选行和实际V，不把此分派当成整条Run₃方程。

## 关系应用的纯数值结构

令App(w,symbol,args,n)为三重对象存在：

```text
∃s ∃payload ∃two
  Scalar(w,symbol,s) ∧
  (ConsCode(w,s,args,payload) ∧
   (Num2(two) ∧ RawNode(w,two,payload,n))).
```

对自然对象赋值env，原rawNode 2 (cons (node (env symbolIndex) []) args)表达式图与App双向对应。正向在原对象ZF中实际取得符号零字段节点、Cons载荷和Num2见证，再用原表达式唯一性／raw双条件取得节点结构；反向正式消去三个对象量词，组合真实符号、载荷及原节点图。不调用宿主表达式eval或旧语法变换结果。

该App支持一般内部符号索引；它没有单凭名称就被认作纯成员原子。纯成员FormulaCode的固定symbol0、两参数森林与此原application结构的连接仍须在后续明确证明。

## 全部局部矩阵

本批数值矩阵比较的是原tracedMatrix：保留真实原head、原guards和全部实际子轨迹，且与此前在实际通用V处的原matrix双条件衔接。共同前提是Omega、实际EnvNat及真实五字段原行Row₃(w,env₀,env₁,env₂,n,q,r)。n／q不额外预给相应输入／输出构造形状或公式类型；所需形状从矩阵证明中恢复。

```text
ConstantData(tag,w,n,q) := Ctor₀,tag(w,n) ∧ Ctor₀,tag(w,q).
BinaryData(tag,kind,...) :=
  (Ctor₂,tag(w,[x,y],n) ∧ Ctor₂,tag(w,[X,Y],q))
  ∧ (Run_kind(w,μ,depth,param,x,X) ∧ Run_kind(w,μ,depth,param,y,Y)).
UnaryData(tag,...) :=
  (Ctor₁,tag(w,[x],n) ∧ Ctor₁,tag(w,[X],q))
  ∧ Run₃(w,μ,childDepth,param,x,X).
ApplicationData(...) :=
  (App(w,symbol,args,n) ∧ App(w,symbol,newArgs,q))
  ∧ Run₂(w,μ,depth,param,args,newArgs).
```

常量在对象Num0／Num3守卫下实际证明原mode<4，消去多余guard和尾truth。二元／一元／应用矩阵分别精确合成对应head结构及全部真实子运行，未将合取子前提替换成析取。

否定的childDepth=env₁；量词局部定理要求对象Successor(childDepth,env₁)，实际succ表达式图给该深度上的五字段子行。该Successor仍是显式对象前提，不以宿主自然数加一替代，也没有声称本批已完成所有内部赋值消去。

## 真实轨迹合成

对每个静态选中的真实原规则，局部数值Data反向给实际tracedMatrix，再调用此前原head变量搜索界和原规则引入，实际取得原完整表Trace。共同通用轨迹集合和原有界赋值／搜索见证在原证明内部取得并消去；这些正向合成端点没有未解共享V前提。自然环境和原行仍显式保留。

## 文件与闭句

| 模块 | 对象产物 |
|---|---|
| OriginalFormulaClasses | 原28条中全部十一kind3规则的静态精确分类 |
| OriginalFormulaDispatch | 对象标签排除、原step精确分派及实际V处Trace展开 |
| OriginalFormulaRowGraph | 通用五字段head拆分、元数据等式及变量行子运行桥 |
| OriginalFormulaScalarExpr | 变量符号码零字段节点的图双条件 |
| OriginalFormulaApplicationSyntax／Expr | App三对象见证及原关系应用图双向对应 |
| OriginalFormulaExpr | 四个规则族的head数值构造及真实原premise表达式 |
| OriginalFormulaChildren | 等词／连接词／应用／否定／量词真实子运行桥 |
| OriginalFormulaLocalData | 常量、二元、一元、应用纯数值局部数据 |
| OriginalFormulaMatrix | 覆盖原十一条的完整局部矩阵双条件 |
| OriginalFormulaTraceRules | 由实际数值Data及原head搜索界合成真实原Trace |
| ObjectOriginalFormulaMatrix | 16组Source→原核→原nativeZF闭句 |

16组闭句包括两组完整表／轨迹分派、通用元数据、应用图结构、五族局部数值矩阵、量词实际子运行、全部选中规则的真实轨迹组合及五族Data到Trace。任意静态通用tag矩阵不被误当作原表成员；组合定理保留已核查的外部原十一成员索引证书。

## 实际验收

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalFormulaMatrix和C:/Python314/python.exe -X utf8 scripts/verify.py实际退出0。全仓1428构建任务、15638项审计（380无公理／15258记录允许依赖）、零警告。九命令及五trust=0入口全部退出0；Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增12模块143显式声明及16组闭句；每组核心证书精确为标准三项依赖，native精确为标准三项加原七固定句子证书依赖。全仓1738对精确证书足迹、13294项Internal显式声明覆盖；1292份工作区独立哈希无差异。

七锁、隔离Choice桥及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变。此前45个执行／分支定义及两个独立字段像定义检查保留，新增App的body／application及四族LocalData共六个纯数值对象定义的直接oracle检查通过。验证summary的scope已改为当前准确范围，历史“项／列表仍未完成”说明不再覆盖已验收结论。

实际日志保留本地verification/commands.json、verification/audit.log、verification/formula-matrix-readback.json；未运行OpenAI全仓构建／Comparator，未推送或创建PR。

## 未完成与下一门

通过原kind3十一规则精确分派、App纯数值结构、全部局部矩阵、量词实际后继深度、实际子轨迹合成及定义独立性六个细门。原arity赋值消去和Run₃整体十一分支方程两个细门明确为false。

下一步先把arity=3／5／6／7的实际存在赋值和根行元数据对齐，给每条原application的数值分支；再实际构造根行，消去共享V和预给行码，取得整体Run₃方程。随后连接纯成员原子并处理完整内部公式归纳及真实量词环境／像列表提升。

原扩展语言quotation总桥、完整数值Option接口、原规则兼容、ProofZF/U全内部检查／编译、内部解释和最终内部Con蕴含仍未完成。局部编译、全部局部矩阵及公理审计不能替代这些终点。
