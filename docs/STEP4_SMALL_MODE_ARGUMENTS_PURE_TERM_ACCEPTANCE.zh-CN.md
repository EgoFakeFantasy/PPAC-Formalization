# 原小模式参数列方程与 mode1 全部纯项数值对应验收

基点：14ed68f9bef95a5d1ff4ba53fb0d26f783ca7adb。单元3f.2c.3b.2d.6c；8模块60项显式声明、11组闭句。

## 对象背景与边界

继续使用固定原 YesMetaZFC 的纯等词／成员语言、完整 Separation／Collection 的 nativeZF 和原 FirstOrder.Derives。内部 Con 仍覆盖全部内部 ω 证明码、原六规则／27逻辑模式及完整 ZF 模式，不假定内部自然数外部标准。最终要求尚未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批完成原参数列 Run2 的全候选 nil／cons 方程，并把 mode1 变量数值合同提升到所有有效纯项。尚未证明参数列与实际抽象码表的完整映射、完整 mode1 公式操作或 forall 节点。

## 每个固定 k<4 的原 nil 守卫

旧 OriginalArgumentsModeGuard 只支持外部 Bool 索引的 mode0／3。本批保留旧文件，新增 SmallModeArgumentsGuard.nil_guard：对任意固定自然索引 k 和外部证明 k<4，实际构造对象 Num4 见证，以对象数码比较 SyntaxNumerals.less 和真实 Expr 图证明原 nilArguments 的完整守卫。

运行时 mode、赋值、深度、参数、输入／输出均为内部对象。外部 k 是固定有限规则模式索引；11组 native 闭句使用 k : Fin 4，CheckStep4 明确展开 k=1 和 k=2 两个实例。没有以旧 Boolthree=false（mode0）冒充 mode1。

## 原完整参数列运行方程

SmallModeArgumentsNil 组合真实原头与守卫，证明 nil 矩阵在真实候选行上等价于输入／输出均为 Nil。SmallModeArgumentsNilApplication 消去原 arity=3 的全部赋值 EX；反向重新构造实际自然赋值、原头图和搜索界，得到完整 nil 应用双条件。

SmallModeArgumentsTrace 与原 cons 应用双条件组合。cons 沿用固定原 arity=7、两项原子查询和四个组件的对象 EX，未把子查询替换为数值规格。实际 Separation 全根集合 V 经对象 EX 构造并消去。

SmallModeArgumentsRun 最后消去／构造真实 kind2 五字段根行，得到：

```text
Ω(w), Numk(mode), depth∈ω, P∈ω
  ⊢ Run2(w,mode,depth,P,input,output) ↔
       [Nil(input) ∧ Nil(output)]
       ∨ ∃h,t,H,T [Cons(h,t,input) ∧ Cons(H,T,output)
                    ∧ Run1(w,mode,depth,P,h,H)
                    ∧ Run2(w,mode,depth,P,t,T)].
```

这是原运行的完整递归方程，对所有内部候选 input／output 成立；不预给根行、输入／输出自然性、列表合法性、轨迹、赋值或归纳假设。输入／输出自然性由实际分支推导。

它仍含真实子运行，尚不是这些子运行与实际抽象环境的列表映射程序已经对应。

## mode1 所有有效纯项

SyntaxTermSyntax.term 的有效项在目标无函数符号语言中只有绑定／自由变量分支。AbstractTermValueSyntax 定义独立数值关系：保留真实 bound／free 长度和索引作用域，在对象 EX 内绑定变量索引，并使用上一批已证 AbstractVariableValueSyntax.valueSpec。

接受定义不引用原 Run／闭轨迹／规则表或公式变换程序。AbstractTermValue 的两个分支分别消去索引、调用整条变量 Run1 数值双条件；反向从数值分支恢复原作用域、真实变量码和原运行。

最终主要合同把类型守卫保留在结论内部：

```text
Ω(w), Num1(mode), metadata(w,depth,P)
  ⊢ [Term(w,a,b,n) ∧ Run1(w,mode,depth,P,n,q)]
       ↔ PureTermNumericValue(w,a,b,depth,n,q).
```

typed_iff 另外提供给定真实 Term 前提下的 Run1 双条件。所有自然数、项码和输出均为内部候选，没有宿主语法枚举或 Type 数据选择。未把任意无效输入自动当作有效纯项。

这修正了上一阶段流程里“递归应用项”的表述：完整原规则表保留 application1，目标纯成员语言的合法项证明使用真实类型守卫排除函数项分支。原 checker 在全部码上的正确性仍需后续装配。

## 实际验收

1703构建任务、18348项审计（398无公理／17950允许依赖）、零警告；九命令及五trust=0入口全部退出0；1538份独立哈希一致、2106对精确证书足迹、16004项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail、九命令及五个 trust=0 入口实际退出0；60项新增声明全部进入 Audit。
- 11组新增核心／native闭句保持精确既有足迹：核心三项标准公理，native额外继承固定七个基础句子证书，无新自定义公理。
- CheckStep4 显式检查 mode1／2 的完整 Run2 方程，以及类型守卫在结论内部的纯项合同。
- 独立读回核查 Num4 实际见证、原 nil 赋值消去／重建、Separation 全根集合及根行码见证消去、原 cons 两子查询未替换、纯项索引的对象绑定。
- 全部原 nil／cons 接受定义、原三／七赋值结构、参数列 outcomes、原 Run、纯项语法和上一批变量数值引擎保持基点 Git 字节不变。
- 七锁、固定 YesMetaZFC 提交及上游干净状态不变；没有修改底座或恢复退役反射。

证据：verification/small-mode-arguments-readback.json、verification/summary.json、verification/commands.json；本地工作脚本在 .local。

## 后续工程流程

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 原小模式参数列方程 | Numk守卫、原nil／cons、全部EX及根行 | 每个固定k<4的全内部Run2递归方程 | 已验收 |
| mode1有效纯项数值对应 | 真实两个变量类型分支与作用域 | 类型守卫在结论内部的Run1↔独立数值关系 | 已验收 |
| 实际抽象码表／列表映射 | 数值分支接真实AbstractFreeTop环境，消去列表归纳IH | 原项／参数列运行与实际码表程序对应 | 下一阶段 |
| 完整mode1公式 | 11构造、量词深度递增、实际环境提升 | 任意内部合法公式的原运行正确性 | 待完成 |
| forall节点 | 原嵌套node9头、四查询、全部四赋值界 | 完整纯关系式节点双条件 | 待完成 |
| logical／theory及Proof／Con | 27模式、完整ZF／U公理、quotation／Bool、内部编译及解释 | 原nativeZF内部Con蕴含 | 未证明 |

此前 substitution／MP／strengthening 完整纯关系式节点仍已验收。新增小模式方程／有效纯项数值门禁为 true；实际抽象环境列表映射、完整公式、forall 和最终 Con 门禁保持 false。
