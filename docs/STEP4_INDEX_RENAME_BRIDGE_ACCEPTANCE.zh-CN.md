# 任意内部公式码的索引重命名与独立程序传输验收

2026-10-23；S3.4c.2b.2c.3a；基点68ced6d43553c501dfa75e5da7cba42cef2eb078。

本批完成原规则5／4所需的一般索引重命名桥。对象语言仍为纯等词／成员语言；背景是原nativeZF的完整Collection呈现。全部证明先在Source.Derives中构造，再经TheoryTransport及ZFReplay返回原FirstOrder.Derives nativeZF []。没有新增对象公理、替代推导核或模型前提。

最终目标仍是原nativeZF中Con_ZF → Con_(ZF+PP+ACwo+¬AC)。内部Con遍历全部内部ω证明码，保留原六规则／27模式及全部Separation/Collection。原规则5／4特定数值操作、专用证明检查器、内部解释和最终Con仍未完成。

## 实际对象接口

所有字母均为对象变量。a,b是源bound/free上下文长度，c,d是目标长度；I,J为旧索引列表码，R,S为变量项像列表码。

```text
Converted(bound,w,I,R,a,c,d) :=
  ∃r f (IndexEncoded(w,r,a,limit(bound,c,d),I)
        ∧ VariableImage(bound,w,r,a,c,d,f)
        ∧ TermImageEncoded(w,f,a,c,d,R)).
Env(w,I,J,R,S,a,b,c,d) :=
  Converted(true,w,I,R,a,c,d) ∧ Converted(false,w,J,S,b,c,d).
```

IndexTermImageCodeExistence.exists_code及IndexTermImageCodeUnique.actual_fiber在合法输入上实际取得唯一转换码；exists_iff_input刻画转换存在的准确输入域。IndexTermImageEnvironment.exists_environment从两份原MapCode实际取得R/S；unique证明整对唯一。图和码见证均在对象存在量词中取得、使用和消去。

| 模块／定理 | 交付的对象推导 |
|---|---|
| IndexTermImageEnvironment.term_program_iff | 对任意内部n/q及I/J的指定解码图r/s，新独立受检项程序等价于原索引项重命名 |
| IndexVariableTermReading.source_iff | 对已知源变量码和实际索引边，目标变量码的准确刻画；不预设目标码已成立 |
| IndexVariableBinderReading.bound_reads／free_reads | 全部内部字段上的提升后图读取；覆盖新零变量、后继bound变量和free变量 |
| IndexTermCodedBinderTransport.coded_lift | 从Env、原索引提升和新双表提升，推导Env(w,L,J,K,H,A,b,C,d) |
| IndexFormulaRenameAtoms.membership_iff／equality_iff | 实际内部两个项调用的双向原子公式对应 |
| IndexFormulaRenameCheck.check_forward | 在对象量词中取得旧三见证和新双表见证后，传输量词子调用 |
| IndexFormulaRenameLogical.single_forward／binary_forward | 全部逻辑分支保留原节点码和严格子码界 |
| IndexFormulaRenameInduction.all_properties／forward | Foundation及完整Separation在内部源码上闭合九参数成员归纳；不留下Earlier前提 |
| IndexFormulaRenameBridge.rename_iff／program_iff | 所有内部公式候选码的双向判断对应及独立程序执行对应 |

coded_lift中旧free索引码J保持不变，而新free项像码从S变成H；量词需要提升两份项像表。规范头部、位移图、源／目标后继长度等都通过对象见证处理。

核心归纳性质是同一对象公式：

```text
Property(w,n) := ∀I J R S a b c d q,
  Env(w,I,J,R,S,a,b,c,d) →
  Rename(w,I,J,a,b,c,d,n,q) → MixedSubst(w,R,S,a,b,c,d,n,q).
```

归纳指标n为内部源码，以实际x∈n的严格子码事实调用归纳假设；量词改变元数据后仍可用上述九个全称量词实例化。没有对外部语法树归纳，没有标准性或外部深度界，没有要求索引映射单射。

反方向先由旧重命名的对象总性取得实际输出v，把v正向传入混合判断，再由已验收的对象唯一性证明v=q，最后用原等词代换回写原判断。由此得到：

```text
Omega(w) ∧ Env(...) ⊢ Rename(...,n,q) ↔ MixedSubst(...,n,q)
Omega(w) ∧ Env(...) ⊢ Executed_fixedFormulaProgram(...,n,q) ↔ Rename(...,n,q).
```

这里Env有独立的对象存在唯一性证明，不是未实现的未来图构造前提。n/q及所有运行时元数据均为任意内部候选；非法候选由原受检判断的准确域处理。外部Bool只索引bound/free两个固定闭句族。

ObjectIndexFormulaRename提供15组Source闭句、sourceZF原核及nativeZF原核证书，包含转换存在／唯一／域、双环境存在唯一、项／原子对应、量词环境传输、闭合归纳、公式正反向及执行对应。可直接使用native_formulaRenameIff和native_formulaProgramIff；它们的目标类型确为原FirstOrder.Derives nativeZF []。

## 实际验收

- 全仓lake --no-cache --wfail build：1190 jobs，退出0；九条命令及五个--trust=0入口全部退出0。
- 13279项声明审计：357项无公理依赖，12922项符合记录依赖，零警告；禁止补洞标记检查通过。
- 新增26模块、177条显式声明、15组闭句；累计10935条Internal显式声明全部纳入审计。
- 新15组及累计1432对core/native证书逐项验证精确足迹：core为propext、Classical.choice、Quot.sound；native为该三项加原固定七项。原独立Choice桥依赖未扩散。
- 1088份工作区文件的独立SHA-256全部一致；原公式程序核心8模块的直接引用门仍通过。
- 七项锁文件不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
- 一般全内部索引公式重命名门及五项新细分门置真；原规则兼容、任意程序解释器、专用Proof检查／编译和最终Con总门仍为false。

命令为LEAN_NUM_THREADS=1，C:\Python314\python.exe -X utf8 scripts/verify.py。独立读回见本地verification/index-rename-readback.json；日志和生成器留在本地。本批没有推送、创建PR、运行原OpenAI全构建或Comparator。

## 下一项实施与验收

| 单元 | 输入与动作 | 必须完成的对象推导 | 状态 |
|---|---|---|---|
| 3a | 原索引列表码、变量项像码、原全11递归 | 实际唯一环境及量词交换，所有内部公式码双向桥，原nativeZF证书 | 本批完成 |
| 3b | 原codeConversion及identityCode、freeShiftCode | 原替换参数L保持原项码列表；证明转换回同一L；实际bound恒等环境和free位移特化；接入新程序 | 下一步 |
| 3c | 原SyntaxTransform模式0／3、原六规则中的free_strengthening／free_substitution | 全内部strictOption数值接口与正确上下文的规则检查兼容；不添加原规则没有的FreeClosed前提 | 待完成 |
| 5 | 专用ProofZF/U纯AST、六规则／27模式、全Separation/Collection | 全内部ω检查／编译正确性 | 待完成 |
| 6／7 | 完整内部解释及准确内部Con | 原nativeZF中最终Con蕴含 | 未证明 |
