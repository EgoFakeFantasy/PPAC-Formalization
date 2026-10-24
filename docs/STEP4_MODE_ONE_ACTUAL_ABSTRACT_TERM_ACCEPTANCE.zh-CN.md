# 原 mode1 零深度纯项与实际首槽抽象操作验收

基点：0b5f8b459b81769c161bab640aec945f448d7f95。单元3f.2c.3b.2d.6d；7模块84项显式声明、15组闭句。

## 对象背景和边界

继续采用固定 YesMetaZFC 的纯等词／成员对象语言、完整 Separation／Collection 的 nativeZF 和原 FirstOrder.Derives。内部 Con 仍覆盖全部内部 ω 证明码、原六规则／27逻辑模式及完整 ZF 模式，内部自然数不假定外部标准。最终要求仍未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批从上一阶段独立数值关系进一步接到实际 AbstractFreeTop 码表、独立项程序和原混合项操作，并消去两张码表见证。范围精确为原 mode1 的零绑定深度；量词提升后的非零深度环境、参数列实际映射、完整公式及 forall 节点尚未完成。

## 全内部数值分支化简

AbstractVariableSpecialization 证明：

- 深度为空集 z、索引 i 为内部自然数且 Succ(j,i) 时，BoundValue(w,z,i,x,y) 当且仅当 y 是绑定变量 j 的码。
- 索引为空集时，FreeValue 当且仅当 y 是当前深度的绑定变量码。
- 索引是内部后继 Succ(i,k) 时，FreeValue 当且仅当 y 是自由变量 k 的码。
- i∈depth 时，BoundValue 当且仅当输出等于输入。

证明使用原后继唯一性／前驱唯一性、内部自然顺序与空集／后继不交性，实际消去数值关系中的后继和前驱对象 EX。最后一条可供后续量词提升环境使用；本批不据此声称完整提升已证明。

## 实际原自然码表逐点对应

AbstractTopVariablePoint 直接调用 SyntaxTopCodedEnvironmentFields.abstract_bound／abstract_zero／abstract_free，不另造比较表。原环境类型给出真实 source／target 长度及后继关系；后继自由索引的原域成员界由 SyntaxIndexLiftOrder.predecessor_member 推导。

AbstractTopVariable.numeric_field_iff 使用实际对象后继存在性，以及原 Separation／内部ω归纳给出的零／后继分解，覆盖全部内部作用域索引和候选输出：

```text
Empty(z), ActualAbstractCodedEnvironment(w,a,b,A,B,R,S), i∈sourceLimit
  ⊢ NumericMode1Value(bound,w,z,i,input,output)
       ↔ Field(selected R/S,i,output).
```

原 mode1 变量 Run1 数值合同再与 TermTransformProgramVariable.at_variable 合并，得到真实原运行与既有独立项程序的逐点等价。没有把“表应当一致”作为新的外部假设。

## 全部有效纯项接原混合项操作

AbstractTopTerm.program_iff 对纯成员语言的两个真实变量类型分支消去内部索引，覆盖全部有效纯项。coded_iff 再使用实际环境的 termLists 和既有 TermTransformProgramCorrectness，接到原 SyntaxCodedMixedTermSyntax.substituted：

```text
Run1(w,mode,z,P,n,q)
  ↔ TermProgram(w,R,S,n,q)
  ↔ CodedMixedTermSubstitution(w,R,S,a,B,A,b,n,q).
```

这里 Num1(mode)、Empty(z)、自然深度／参数、实际抽象环境和真实项类型均有对象证书。参数 P 保留为任意内部自然数，未限制输入／输出为外部标准码。

## 实际码表见证消去

AbstractTopTermSyntax.abstracted 是真实两变量对象 EX：其 state 恰为实际 abstractCoded 环境与原 coded mixed term substitution 的合取。定义不引用原 Run、闭轨迹或独立数值关系作为接受预言机。

AbstractTopTermOperation.at_codes_iff 在给定实际码表时证明等价；反向消去抽象操作自带的任意两码表，并直接在这些真实码表上调用 coded_iff，不预设所选码表相等。

run_iff 使用 SyntaxTopCodedEnvironmentExistence.abstract_exists 实际构造两张码表，再以原对象两个 EX 规则消去。source_type 从原混合项操作恢复输入项类型。最终 guarded_iff 把类型守卫保留在结论内部：

```text
Ω(w), Num1(mode), metadata(w,z,P), Empty(z), AbstractInput(w,a,b,A,B)
  ⊢ [Term(w,a,B,n) ∧ Run1(w,mode,z,P,n,q)]
       ↔ ActualAbstractPureTerm(w,a,b,A,B,n,q).
```

最终没有给定 R／S、解码图、后继索引、输出自然性、轨迹、赋值、比较程序一致性或输入类型前提。AbstractInput 仅保留实际操作要求的内部自然长度与 Succ(A,a)、Succ(B,b)；全部运行项码和输出仍在对象理论层。

该零深度接口不会把新的 TopAbstract 环境直接当作量词下的提升环境。后续必须证明原 depth 递增与实际绑定码表提升对应。

## 实际验收

1710构建任务、18432项审计（398无公理／18034允许依赖）、零警告；九命令及五trust=0入口全部退出0；1545份独立哈希一致、2121对精确证书足迹、16088项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail、九命令及五个 trust=0 入口实际退出0；84项新增声明全部进入 Audit。
- 15组新增核心证书保持三项标准公理足迹；native 证书额外继承固定七个基础句子证书。没有增加自定义公理。
- CheckStep4 显式展开抽象操作的两个内部码表 EX，以及最终类型守卫在结论内部、没有给定码表的合同。
- 独立读回核查实际原码表字段、内部零／后继分解、作用域索引 EX、两码表实际存在性及消去、输入类型恢复和最终前提集合。原投影批次的 StructuralListField 全禁规则在本批仅对三个显式比较模块放行 field／field_rename；新操作接受定义仍禁止原 Run、轨迹和数值规格预言机，旧执行定义仍逐字核对。
- 原环境、原混合项操作、独立项程序及原 Run 定义保持基点 Git 字节不变；新操作 state 不依赖原接受器或数值比较规格。
- 七锁、固定 YesMetaZFC 提交与上游干净状态不变。未改底座、未恢复退役反射、未外部发布。

证据：verification/abstract-top-term-readback.json、verification/summary.json、verification/commands.json；本地工作脚本在 .local。

## 后续工程流程

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 零深度实际纯项抽象 | 数值关系接真实码表／项程序／混合项操作，消去码表EX | 类型守卫在结论内部的原Run1双条件 | 已验收 |
| 参数列实际映射 | 小模式Run2方程接实际抽象码表的逐项映射，消去内部列表IH | 全内部参数列运行与码表程序对应 | 待完成 |
| 绑定提升环境 | 原depth递增与实际R/S提升对应，处理全部作用域索引 | 无未证兼容性假设的mode1环境提升 | 下一阶段 |
| 完整mode1公式 | 原11构造与量词递归，消去统一对象IH | 任意内部合法公式的原运行正确性 | 待完成 |
| forall节点 | 原嵌套node9头、四查询和全部四赋值界 | 完整纯关系式节点双条件 | 待完成 |
| logical／theory及Proof／Con | 27模式、完整ZF/U、quotation／Bool、内部编译和解释 | 原nativeZF内部Con蕴含 | 未证明 |

已有 substitution／MP／strengthening 节点、小模式参数列方程及mode1数值合同保持已验收。新门禁仅把零深度实际纯项操作标为 true；完整提升／列表映射／公式／forall／最终 Con 仍为 false。
