# 原量词整条运行与实际历史程序验收

基点：1ec46454f688a660add4de7e27b7bc31dd760549。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.2b：原 mode0／3 的两个量词局部分支与真实 advanced 历史程序双向对应，原十一分支中的其余十个分支逐一排除，取得整条量词 Run₃ 双条件。统一对象归纳前提仍明确保留；完整十一情况装配、成员归纳消去与最终 Con 尚未完成。

## 对象合同

保持原 YesMetaZFC 纯等词／成员语言、原 nativeZF 完整 Collection 与原 FirstOrder.Derives。最终目标是 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 保留全部内部 ω 证明码、原六规则／27模式和完整 Separation／Collection。没有新增对象 AC、标准 ω、外部良基、新核或退役反射。

七组新闭句均有实际 Source.ZF 推导，经 TheoryTransport.sentence 和 ZFReplay.replay 返回原 nativeZF。固定 Bool 索引 three 对应运行模式3／0，universal 对应量词标签9／10；所有实际深度、绑定界、像表、字段、公式码与输出都保留在对象公式中。

## 后继子运行与真实读取

OriginalBinderStepSyntax.step(w,mode,depth,parameter,x,X) 是对象存在公式：

```text
∃D, successor(D,depth) ∧ Run₃(w,mode,D,parameter,x,X).
```

successor_exists 直接由内部 Ω 的归纳闭包推出 ∃D(D∈ω ∧ successor(D,depth))，没有使用外部标准自然数后继。

OriginalBinderReadAtLift.read_at_lift_iff 在真实 frame、全参数对象归纳前提、源父 FormulaCode、实际源量词构造码、真实递归图以及实际混合提升下证明：

```text
Run₃(w,mode,D,opParam(three,P,S),x,X)
  ↔ read(w,h,x,K,H,A,b,C,c,X).
```

D 的后继是原运行深度 depth；A、C 分别提升源／目标绑定变量界 a。二者没有被预设相等。统一对象归纳在实际提升环境中实例化，源子 FormulaCode 由父类型和实际量词构造恢复，严格成员 x∈n 由原构造器推出。实际 A=C、H=S 等词把规范子执行与真实历史字段执行对齐；目标 X 无预给形状或类型。

## 完整 advanced 双条件

OriginalBinderAdvance.step_iff_advanced 在同一实际背景下证明：

```text
∃D, successor(D,depth) ∧ Run₃(w,mode,D,opParam(three,P,S),x,X)
  ↔ advanced(w,h,x,R,S,a,b,a,c,X).
```

正向在对象量词内构造源绑定后继 A，取目标绑定界同为 A；由实际混合像表提升存在定理构造 K、H，再用提升点双条件重建真实 read 与 advanced 四元存在块。

反向消去实际 advanced 的 A、C、K、H，独立构造运行深度后继 D，使用实际读取逆向恢复子 Run₃，再构造原后继子运行存在块。全部见证通过原 exI／exE 引入和消去，没有宿主函数选择，也没有把内部量词提升见证当作外部给定数组。

## 量词局部分支与整条运行

OriginalBinderCaseBridge.quantified_iff 对两个量词都证明：

```text
原 binderCase(tag,w,mode,depth,opParam(three,P,S),n,q)
  ↔ FormulaTransformLogicalSyntax.single(tag,true,w,h,R,S,a,b,a,c,n,q).
```

局部定理只保留源父类型及真实 frame／graph／统一对象归纳前提，没有要求外部给定源子字段。两个方向分别消去原 binder 深度块及字段块，或既有 single／advanced 字段块，再用原规则重建相反分支。

OriginalBinderRunDispatch 对源标签9／10，排除其余十个原分支，包括实际 App 的异标签冲突；在原 Num0／Num3 和自然 metadata 下，与既有完整 Run₃ 方程合成整条运行分派。此分派消去不需要归纳假设。

OriginalBinderProgram.quantified_iff 最终在以下明确前提下取得：

```text
Ω(w), actualFrame, sourceFormulaCode, knownSourceQuantifierCode,
actualGraph(w,h,n), allFramesIH(three,w,n)
  ⊢ Run₃(w,mode,depth,opParam(three,P,S),n,q)
       ↔ single(tag,true,w,h,R,S,a,b,a,c,n,q).
```

q 为任意内部输出候选，无目标自然性、目标形状、根行或共享原数值轨迹集合前提。allFramesIH 仍是尚待全公式成员归纳消去的对象公式；本批没有宣称全部公式根的正确性已经成立。

## 新增文件与原核闭句

| 模块 | 实际产物 |
|---|---|
| OriginalBinderStepSyntax | 独立深度后继子运行、内部后继存在及原规则接口 |
| OriginalBinderReadAtLift | 实际提升点的子运行／read 对应及字段等词对齐 |
| OriginalBinderAdvance | 完整后继子运行与真实 advanced 双条件 |
| OriginalBinderCaseBridge | 两种量词的局部分支双向推导 |
| OriginalBinderRunDispatch | 量词处完整十一分支筛选与整条 Run₃ 分派 |
| OriginalBinderProgram | 真实 frame／graph 与统一对象归纳下的整条量词运行接口 |
| ObjectOriginalBinderProgram | 七组 Source→TheoryTransport→ZFReplay 原核闭句 |

闭句为 naturalSuccessorWitness、liftedChildExecutionAlignmentIff、quantifierChildReadAtLiftIff、quantifierStepAdvancedIff、quantifierLocalCaseIff、quantifierWholeRunDispatchIff、quantifierWholeRunFromUniformInductionIff。

## 实际验收

定向 `lake build PPAC.Migration.Internal.ObjectOriginalBinderProgram --wfail` 与 `C:/Python314/python.exe -X utf8 scripts/verify.py` 均实际退出0。Lean／Lake 严格串行，LEAN_NUM_THREADS=1；本批未跟踪新源码也在验收前检查 UTF8／LF 和行尾空白。

- 1505 构建任务、16296 项声明审计：385 无公理，15911 有允许的记录依赖，零警告。
- 九条命令全部退出0，其中五个原核 `--trust=0` 入口全部退出0。
- 新增7模块、45项显式声明、7组闭句；核心证书精确依赖标准三项，native 精确为标准三项加原七项固定句子语法证书。
- 全工程1835对精确证书足迹、13952项 Internal 显式声明覆盖、1369份独立 SHA256 一致。
- 七锁及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变，隔离 Choice 桥不变。
- 原独立编译9模块、原子两定义和45+2+6+17+2项执行定义防护保留。本批 step 为原始子运行关系的显式存在分解，不是新独立执行器或比较 oracle。

实际证据保留本地 verification/commands.json、audit.log、binder-program-readback.json。没有推送／PR，未运行 OpenAI 全仓或 Comparator。

## 后续工程与范围

| 单元 | 实现／状态 | 对象验收要求 |
|---|---|---|
| 3f.2c.2b | 本批完成：真实量词局部程序与整条运行对应 | 七组原核闭句；统一对象归纳前提明确保留 |
| 3f.2c.3a | 下一步：装配全部十一情况及实际完整程序根方程 | 原子四分支不可替代完整 formulaProgram；处理真实图上的完整步骤、目标合法性及 executed 对应 |
| 3f.2c.3b | 全内部 FormulaCode／成员归纳 | 证明 correct 对全部内部合法根成立，消去 allFramesIH；不使用宿主 WellFounded 或外部标准性 |
| 适用性 | 模式3自由变量像表合同对最终检查器的适用性 | 保持全部内部 Proof 码范围，不能人为限制合法输入来完成证明 |
| 后续 | quotation、数值 Option、原六规则／27模式、全 ProofZF/U、内部解释与 Con | 全内部 ω 证明码上的检查／传输与最终 Con 蕴含 |

本批仅开启量词后继子运行／advanced、局部分支、完整量词分派和统一对象归纳下整条量词运行四个细门。全部十一情况已装配、统一归纳已消去、最终检查器模式3合同已适用、完整公式执行、quotation、Option、ProofZF/U、内部解释和最终 Con 门继续为false。
