# 原参数列表整体运行方程验收

基点：26f09952af7543e5093bd0c375b84af5b3365772。完成S3.4c.2b.2c.3c.2c.2b.2：原arity=3／7存在赋值与预给根行均消去的mode0／3整体nil／cons方程。对象公式量化所有内部候选输入、输出和Cons组件。尚未完成有类型列表的变换对应／总性／唯一性或内部列表归纳。

## 对象目标保持不变

语言为纯等词／成员，背景为原nativeZF完整Collection呈现，推导固定原FirstOrder.Derives。目标仍为原核Derives nativeZF [] (Con_ZF → Con_target)，目标理论ZF+PP+ACwo+¬AC；内部Con量化全部内部ω证明码，原六规则／27模式及完整Separation／Collection不变。

本批是锁定原Horn规则表的纯语言关系式运行方程；原扩展语言Condition公式整体消去／quotation及宿主SyntaxTransform数值Option接口的总对应仍是独立未完成门。未增加选择、标准ω、外部有限轨迹、模型或新核前提。

## 精确整体方程

沿用原五字段Row_k和Run_k，其中Run_k(w,μ,d,p,n,q)为实际存在原根行r及其原完整表闭轨迹。定义纯对象分支：

```text
NilData(w,n,q) := NilCode(w,n) ∧ NilCode(w,q)
ConsData(w,μ,d,p,n,q,h,t,H,T) :=
  (ConsCode(w,h,t,n) ∧ ConsCode(w,H,T,q))
  ∧ (Run_1(w,μ,d,p,h,H) ∧ Run_2(w,μ,d,p,t,T))
ConsCase(w,μ,d,p,n,q) := ∃h ∃t ∃H ∃T ConsData(...)
Outcomes := NilData ∨ ConsCase.
```

对固定的原mode0或mode3，在Omega(w)、相应Num0／Num3(μ)、d∈w及p∈w下，对所有内部n、q实际证明：

```text
Run_2(w,μ,d,p,n,q) ↔ Outcomes(w,μ,d,p,n,q).
```

不预给n／q自然性、合法结构、外部列表、外部长度、根行码、任何共享轨迹集合、原arity赋值或四个Cons组件。四个组件由对象存在量词绑定；不是宿主有限List的归纳模式。d∈ω、p∈ω仍是原赋值／原行需要的守卫，没有删去。

此为精确递归方程。它尚未单独证明任意有类型内部列表存在唯一输出或与独立项程序逐字段相同，不能据此通过整个列表变换正确性门。

## 实际消去链

OriginalRowMetadataSubstitution对原行和Run逐一证明mode／depth／parameter的对象等词替换，再组合三字段传输。OriginalArgumentsMetadata从真实原head的前三字段恢复μ=env₀、d=env₁、p=env₂，并从实际候选行取得三个元数据的内部自然性。

nil正方向消去原arity=3存在块，用原矩阵双条件恢复Nil输入／输出；反方向以真实μ,d,p作为内部赋值，实际取得原head／guard／搜索界和原application。cons正方向消去原arity=7块，对齐全部元数据，并把四个实际组件装入ConsCase；反方向正式消去ConsCase的四个对象量词，构造原七分量赋值及其原搜索界。

cons反方向没有假定仅凭ConsCode就能得到全部组件自然性：h,H的自然性来自真实Run_1，t,T来自真实Run_2的实际五字段行。这些内部自然性用于重构原EnvNat₇，不抽取宿主自然值或轨迹函数。

在实际通用轨迹集合V处，两条原application分别与NilData／ConsCase双向对应。完整原表kind2精确分派和原轨迹一步展开给每个实际根行的Trace↔Outcomes；随后由原Separation实际取得V并消去其存在量词，移除共享轨迹前提。

整体运行正方向消去真实根行，将点态方程传到所有候选。反方向从Outcomes恢复n、q自然性，实际构造原五字段根行，再用点态方程取得真实原Trace，构造Run_2。实际赋值、四组件、共享V及根行全部留在对象量词的正式引入／消去中。

## 模块和验收

| 模块 | 对象证明 |
|---|---|
| OriginalRowMetadataSubstitution | 行／运行三个元数据的等词传输 |
| OriginalArgumentsMetadata | 原head字段等式及实际行的元数据自然性 |
| OriginalArgumentCaseSyntax | NilData、四组件ConsData／ConsCase及Outcomes对象公式 |
| OriginalArgumentsNilApplication | 原arity=3 application双向消去／重建 |
| OriginalArgumentRunNaturality | 真实原运行的内部输入／输出自然性 |
| OriginalArgumentsConsApplication | 原arity=7与四组件内部存在块双向对应 |
| OriginalArgumentsTraceEquation | 原完整表Trace点态方程；共享V前提实际消去 |
| OriginalArgumentRoots | 分支的实际自然范围和根行存在 |
| OriginalArgumentsRunEquation | 不预给根行及输入／输出自然性的整体双条件 |
| ObjectOriginalArgumentRun | 8组Source.Derives→TheoryTransport→ZFReplay闭句 |

1386构建任务、15195项审计（378无公理／14817允许依赖）、零警告；九命令及五trust=0入口全部退出0；1250份工作区独立哈希一致、1681对精确证书足迹、12851项Internal显式声明覆盖。

新增10模块66声明、8组闭句及8对精确证书。核心严格为std3，native严格为std3加原七固定证书依赖。45个执行／分支定义直接oracle检查通过；新五个分支定义仅引用实际Nil／Cons和原子运行，不调用旧列表变换规格／宿主算子。七锁、隔离Choice桥及固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。

Lean/Lake严格串行，LEAN_NUM_THREADS=1。定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalArgumentRun及C:/Python314/python.exe -X utf8 scripts/verify.py均退出0；五个入口使用--trust=0。实际命令在本地verification/commands.json，独立回读在verification/argument-run-readback.json。未运行OpenAI全仓构建、Comparator、推送或PR。

## 下一门

在有类型原结构列表上做对象内部成员／长度归纳，将Run_1与已验收原项程序对齐，取得完整列表变换对应、实际合法输出存在／唯一性及精确拒绝接口。随后处理原kind3十一公式、量词深度后继与实际环境提升。

全内部有类型列表变换正确性新细门明确为false，既有全列表归纳总门仍为false。原扩展语言quotation总桥、完整原数值接口、全mode0／3公式、原规则5／4兼容且无FreeClosed、ProofZF/U及全内部检查／编译、完整解释和最终Con均未完成。
