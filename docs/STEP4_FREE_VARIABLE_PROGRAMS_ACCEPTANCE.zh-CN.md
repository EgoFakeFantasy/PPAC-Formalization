# 原自由替换与弱化的全内部程序特化验收

2026-10-23；S3.4c.2b.2c.3b；基点f7ab445f6f2a3f82deff839761e3cb4f71b31155。

本批把已验收的独立固定公式程序接到原自由替换和头槽弱化的内部规格。对象语言为纯等词／成员语言，背景为原nativeZF的完整Collection呈现。证明在Source.Derives中构造，经TheoryTransport及ZFReplay取得原FirstOrder.Derives nativeZF []闭句证书；没有新增对象公理、替代推导核或模型前提。

最终要求仍为原nativeZF中的Con_ZF → Con_(ZF+PP+ACwo+¬AC)，Con遍历全部内部ω证明码，保留原六规则／27模式和全部Separation/Collection。原SyntaxTransform严格Option数值接口及规则检查兼容、ProofZF/U、内部解释和最终Con均未完成。

## 原替换参数同码保持

原自由替换项表L保存真实项码。纯成员签名没有函数符号，原替换项的bound上下文为空，所以每个合法替换项只能是fvar；SyntaxFreeSubstSyntax.termList的branch false限制与原接口一致。

FreeSubstImageGraph.image_map证明：同一实际自由项图f，对任意合法目标bound长度c，仍是目标(c,d)的完整项像图。read_at_edge／reads从原编码图实际消去索引见证，利用原函数图单值性得到所有内部字段的准确变量码对应；mapped装配完整VariableImage关系。

FreeSubstImageCode.same_code给出以下对象推导，字母均为对象变量：

```text
Omega(w), c∈w, CodeConversion(w,a,d,L,J)
  ⊢ Converted(false,w,J,L,a,c,d).
```

结果中的列表码正是原L。converted_unique_same_code进一步证明：任意其他转换码T都等于L；没有把参数替换成索引列表J。identity_image_exists从原实际bound恒等码取得实际变量项像码。

## 两项程序特化

两个执行关系只调用上一批独立固定公式执行、实际数值码转换和合法输入关系。对照证明引用旧操作规格；新执行公式不以旧完整自由替换／弱化判断为定义。

FreeSubstProgramSyntax的执行关系为：

```text
FreeExec(w,b,a,c,L,n,q) := TermList_free(w,a,c,L) ∧
  ∃I R (IdentityCode(w,b,I) ∧ Converted(true,w,I,R,b,b,c)
         ∧ Executed_formula(w,R,L,b,a,b,c,n,q)).
```

free表直接使用原L；bound表R由实际恒等索引码转换取得。forward消去旧内部I/J，再实际取得R，使用same_code构造环境并传入新执行。reverse实际从原L取得内部解码码J，构造相同环境，再把新执行传回原判断。所有见证均留在对象存在量词中。

WeakenFreeProgramSyntax的执行关系为：

```text
WeakExec(w,a,b,B,n,q) := ∃I J R S (
  IdentityCode(w,a,I) ∧ ShiftCode(w,b,B,J) ∧
  Env(w,I,J,R,S,a,b,a,B) ∧ Executed_formula(w,R,S,a,b,a,B,n,q)).
```

ShiftCode保留原头槽位移和B为b后继的内部条件。forward从原I/J实际取得R/S；reverse把执行传回旧重命名后装配原弱化判断。没有为原规则附加FreeClosed前提。

两个Correctness.executed_iff分别证明：

```text
Omega(w) ⊢ FreeExec(...) ↔ OriginalFreeSubst(...)
Omega(w) ⊢ WeakExec(...) ↔ OriginalWeakenFree(...).
```

全部上下文长度、原列表L、输入码n和候选输出q都是任意内部变量。不是外部Tree的逐例quotation，也不要求映射单射、标准内部ω或外部深度界。

## 实际输出与原核闭句

| 接口 | 自由替换 | 头槽弱化 |
|---|---|---|
| 精确输入 | 原FormulaCode(w,n,b,a)及原自由项表L | 原FormulaCode(w,n,a,b)及successor(B,b) |
| 正反向执行规格 | FreeSubstProgramCorrectness.executed_iff | WeakenFreeProgramCorrectness.executed_iff |
| 实际有类型唯一输出 | FreeSubstProgramValue.actual_fiber | WeakenFreeProgramValue.actual_fiber |
| 纤维恰等于合法输入 | fiber_iff_input | fiber_iff_input |
| 全内部候选唯一性／值 | unique、unique_output、at_candidate | 同左 |
| 非法候选拒绝 | 列表环境、源码、完整输入、目标类型、非自然数输出 | 非后继关系、源码、完整输入、目标类型、非自然数输出 |
| 实际新上下文长度 | c由原替换输入给定 | actual_state从合法源码实际取得B和输出纤维 |

value包含执行、目标FormulaCode、q∈w和对全部内部执行候选的唯一性。actual_fiber消去旧对象输出总性取得的实际见证，再用本批双向桥传入新执行。actual_state通过原Pairing／Union取得实际后继B，在该B上构造新程序的唯一有类型输出。

ObjectFreeVariablePrograms提供39组Source闭句、sourceZF原核及nativeZF原核证书。native_freeSameListCode、native_freeExecutionIff、native_weakExecutionIff、native_freeActualFiber、native_weakActualSuccessorState等目标类型均为原FirstOrder.Derives nativeZF []。close在对象语言中全称闭合所有自由变量；例如选取m=7及七个不同坐标，得到同一句子对w,b,a,c,L,n,q的内部全称量化，而不是外部逐个自然码的验证。

## 实际验收

- 全仓lake --no-cache --wfail build：1201 jobs，退出0；九条命令和五个--trust=0入口均退出0。
- 13511项声明审计，357项无公理依赖、13154项符合记录依赖，零警告；禁止补洞标记检查通过。
- 新增11模块、232条显式声明、39组闭句；累计11167条Internal显式声明全部纳入审计。
- 新39组及累计1471对core/native证书逐项匹配精确足迹：core恰为propext、Classical.choice、Quot.sound；native为该三项加原固定七项。原独立Choice桥依赖未扩散。
- 1099份工作区文件的独立SHA-256全部一致；原公式程序核心8模块的直接引用门继续通过。
- 七项锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
- 五项本批细分门为true；原规则兼容、原严格数值接口、专用证明检查器和最终Con等总门保持false。

命令为LEAN_NUM_THREADS=1，C:\Python314\python.exe -X utf8 scripts/verify.py。独立读回位于本地verification/free-variable-readback.json；日志及生成器留在本地。本批没有推送、创建PR、运行原OpenAI全构建或Comparator。

## 下一项：严格数值接口与规则检查

| 工作单元 | 输入与实施 | 必须验收 |
|---|---|---|
| 3c.1 | 原SyntaxTransform.lookup及原列表码字段 | 非法外壳／越界失败，全部内部合法索引的精确读取；不能用宿主lookup_list替代 |
| 3c.2 | 原boundValue／freeValue模式0／3 | bound恒等，free位移／同一L查表；对象数值接口对应 |
| 3c.3 | 原全11公式分支和depth+1量词递归 | 全内部数值变换与新受检特化执行对应；含真实binder下L保持和恒等码提升，不以外部encode定理替代 |
| 3c.4 | 原free_strengthening／free_substitution及上下文码 | 模式0／3的strictOption接口与原规则检查兼容，保留准确上下文且不加FreeClosed |
| 5／6／7 | 专用ProofZF/U、完整内部解释、准确内部Con | 六规则／27模式和全Separation/Collection检查／编译，最终原nativeZF对象Con蕴含 |

固定源文件：YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxTransform.lean。模式0／3的boundValue恒等，freeValue分别为fvar(index+1)和lookup(parameter,index)；公式量词仍把depth增加1。宿主函数本身及外部SyntaxTransformInstances quotation不是上述全内部对象验收的替代品。
