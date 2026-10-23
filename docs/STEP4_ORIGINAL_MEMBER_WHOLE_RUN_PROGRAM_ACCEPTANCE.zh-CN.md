# 原完整成员Run₃与独立项程序验收

基点：b2a6c232a75bf786a282b3537bca94636f250860。完成S3.4c.2b.2c.3c.2c.2b.3f.2b.1：已知纯成员输入处，原mode0／3整条Run₃与独立成员结果规格对所有内部公式输出候选的双条件。尚未完成既有完整公式程序接口和所有原子／公式桥。

## 对象合同

保持YesMetaZFC原纯等词／成员语言、原nativeZF完整Collection及原FirstOrder.Derives。最终仍要求Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC；内部Con量化全部内部ω证明码，要求原六规则／27模式和完整Separation／Collection。没有添加对象AC、标准ω、外部模型良基、新核或退役反射。

每组闭句均有实际Source推导，经TheoryTransport.sentence和ZFReplay.replay返回原核。所有运行时索引、参数、森林、符号及输出均是对象变量／存在见证。构造森林使用对象存在推导，不抽取宿主集合选择数据。

## 独立成员结果及比较合同

MemberProgramSyntax.returned(w,R,S,c,d,s,x,y,q)是以下两个内部存在量词：

```text
∃X ∃Y
  TypedInputs₂(w,c,d,[X,Y]) ∧
  (MemberCode(w,s,X,Y,q) ∧
   Runs₂(w,R,S,[x,y],[X,Y])).
```

Runs₂包含两个独立TermTransformProgramSyntax.termProgram运行和真尾。该规格不调用原Run₃／Run₂、旧公式变换或完整公式程序执行结果作为答案。源ZeroScalar(w,s)在具体端点保留，关系编号Num0与符号树码Num2分开。

MemberPairAgreementSyntax.agreement是比较用对象公式：对全部内部源参数码A和输出参数码Q量化，实际SourceForest₂(w,[x,y],A)蕴含原Run₂(A,Q)与已验收独立参数程序结果的双条件。它不是独立执行规格或新公理。MemberPairAgreement.replace_agreement／weaken_agreement使用实际模式／元数据／恒等／位移／转换列表及源项类型，实际证明整个对象∀A∀Q公式；具体最终端点不残留agreement前提。

## 对象森林见证的构造与消去

正向消去原成员applicationCase的编号、源参数森林和输出参数码。真实Run₂经已证明agreement取得两个实际输出项及目标森林；原App在该森林处给同一候选q的成员构造码，合成独立成员结果。

反向从独立成员结果消去两个输出项。先由源项自然性构造实际源参数森林，再由有类型目标项构造实际目标参数森林，最后构造内部Num0见证。已证明agreement反向给同一真实Run₂，成员构造码及实际目标森林反向给原App，从而重建原成员applicationCase。三个存在见证逐个正式消去；具体端点不预给参数列表码、目标形状、目标自然性、外部见证数组或抽象比较前提。

## 完整原Run₃分派

OriginalMemberRunDispatch在已知MemberCode(w,s,x,y,n)处，用原构造器异标签互斥排除常量0／1、等词、否定、四个二元连接词及两个量词，共十条公式分支。二元／一元／量词的原存在组件仍通过对象exE消去，不借宿主解析候选码。

原Outcomes精确等价于applicationCase，再与已验收原Run₃整体十一分支方程相接。在Num0／Num3及自然深度／参数守卫下，整条原Run₃精确等价于该成员分支。

OriginalMemberProgram.replace_run_iff／weaken_run_iff进一步得到：

```text
原mode3及实际替换环境：
 Run₃(w,mode,depth,L,n,q) ↔ MemberReturned(w,R,L,a,c,s,x,y,q).
原mode0及实际位移环境：
 Run₃(w,mode,depth,parameter,n,q) ↔ MemberReturned(w,R,S,a,B,s,x,y,q).
```

共同源守卫是Omega、ZeroScalar、实际源MemberCode及两个源项类型。q为任意内部集合候选，无输出自然性或公式构造形状前提。实际恒等／位移／转换列表和固定层元数据沿用原已验收接口，不将任意混合替换表自动视为量词稳定。

## 文件与原核闭句

| 模块 | 对象产物 |
|---|---|
| MemberProgramSyntax | 独立成员结果的内部存在公式、重命名和引入 |
| MemberPairAgreementSyntax | 全内部源／目标参数码的对象比较公式 |
| MemberPairAgreement | 实际模式0／3推导整个agreement |
| MemberProgramOutput | 真实App及独立双参数结果合成为成员结果 |
| MemberProgramIntro | 源／目标森林和Num0逐个构造并消去 |
| MemberProgramCase | 原成员applicationCase的全候选双条件 |
| OriginalMemberRunDispatch | 已知成员输入处拒绝其余十支并分派完整Run₃ |
| OriginalMemberProgram | 实际模式下applicationCase／完整Run₃的具体程序端点 |
| ObjectOriginalMemberProgram | 十组Source→TheoryTransport→ZFReplay原核闭句 |

十组闭句：

- replaceMemberPairAllInternalAgreement
- weakenMemberPairAllInternalAgreement
- originalMemberWholeElevenCaseDispatchIff
- originalMemberWholeRunApplicationIff
- originalMembershipCaseProgramIff
- originalMemberApplicationProgramIff
- replaceOriginalMemberApplicationProgramIff
- replaceOriginalMemberWholeRunProgramIff
- weakenOriginalMemberApplicationProgramIff
- weakenOriginalMemberWholeRunProgramIff

## 实际验收

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalMemberProgram及C:/Python314/python.exe -X utf8 scripts/verify.py实际退出0。全仓1462构建任务、15922项声明审计（380无公理／15542允许依赖）、零警告。九命令及五个--trust=0入口全部退出0；Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增9模块68显式声明、10组闭句。核心证书精确依赖标准三项，native精确为标准三项加原七固定句子语法证书；隔离Choice桥未修改。1776对精确证书足迹、13578项Internal显式声明覆盖、1326份独立SHA256无差异。七锁及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变。

此前45个执行／分支定义、两个独立字段像、六个独立有限森林／双输出规格及十七个纯公式定义检查保留；新增MemberProgramSyntax.body／returned两个独立结果定义有直接oracle检查。比较公式agreement独立标为比较前提并在具体模式端点实际推导，不作为程序执行原语。

日志及独立证据保留本地verification/commands.json、audit.log、member-program-readback.json；没有推送或PR，未运行OpenAI全仓／Comparator。

## 未完成与下一门

本批MemberProgramSyntax结果由独立项程序运行组成，尚不等于既有FormulaTransformAtomSyntax.membership或完整FormulaTransformExecutionSyntax执行定理。下一步须把这两个成员接口正式对齐，并完成等词／常量分支；完整原子门明确为false。

随后仍需连接词、正确的实际量词环境／像列表提升和完整对象公式成员归纳。归纳性质必须在对象公式中量化所有变化运行参数。原mode3保持L不变，不能混淆已证明同码稳定的实际自由变量像表与固定层任意Mixed.termList。

既有完整公式程序接口、所有原子／公式总桥、quotation、完整数值Option、ProofZF/U检查／编译、内部解释及最终Con均未完成。当前成员对象定理及全仓构建不能替代这些终点。
