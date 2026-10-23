# 统一内部原子程序验收

基点：5a5d5599f8476450e1ce075ac0db3d17db1fd556。完成 S3.4c.2b.2c.3c.2c.2b.3f.2b.3：在实际内部 SyntaxAtomSyntax.atomic 输入守卫下，消去成员／等词的内部字段存在块，证明原 mode0／3 整条 Run₃ 与既有 Program 编译器的四分支原子程序双条件。完整十一分支公式执行、量词环境适用性、归纳及最终 Con 仍未完成。

## 对象合同

对象语言保持原 YesMetaZFC 单排序纯等词／成员语言，背景保持原 nativeZF 的完整 Collection，正式关系保持原 FirstOrder.Derives。最终目标仍是 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 覆盖全部内部 ω 证明码、原六规则／27 模式及完整 Separation／Collection。没有添加对象 AC、标准 ω、外部良基、新核或退役反射。

七组新闭句均有实际 Source.ZF 推导，经 TheoryTransport.sentence 和 ZFReplay.replay 返回原 nativeZF。源输入 n、输出候选 q、历史 h、所有模式环境及运行时字段都是对象变量。原子类型是原有内部公式，不以宿主 Formula AST 或外部四分支匹配替代。

## 实际统一结论

记 atomProgram 为 FormulaAtomicProgramSyntax.program，即用既有 Program.branch／either 构造的 nullary false、nullary true、membership、equality 四分支。FormulaAtomicProgramSyntax.run_eq_program 验证该四分支公式恰为既有 FormulaTransformProgramSyntax.run 对该程序的编译结果，历史参数 h 可为任意内部集合。

在已验收的具体 mode3 环境下，OriginalAtomicProgram.replace_program_iff 证明：

```text
Ω(w), Num3(mode), metadata(w,depth,L),
identityCode(w,a,I), converted(true,w,I,R,a,a,c),
Mixed.termList(w,b,a,c,L), atomic(w,a,b,n)
  ⊢ Run₃(w,mode,depth,L,n,q)
       ↔ Program.run(atomProgram,w,R,L,a,b,a,c,h,n,q).
```

在已验收的具体 mode0 环境下，OriginalAtomicProgram.weaken_program_iff 证明：

```text
Ω(w), Num0(mode), metadata(w,depth,parameter),
identityCode(w,a,I), shiftCode(w,b,B,J),
converted(true,w,I,R,a,a,B), converted(false,w,J,S,b,a,B),
atomic(w,a,b,n)
  ⊢ Run₃(w,mode,depth,parameter,n,q)
       ↔ Program.run(atomProgram,w,R,S,a,b,a,B,h,n,q).
```

其中 metadata 是 depth∈w 与 parameter∈w 的合取。输入 n 与输出 q 均为任意内部候选；源项、源符号和所有目标字段都不再作为外部给定参数。没有额外预给目标形状、输出自然性、根行、共享完整轨迹集合或抽象比较公理。

四分支原子程序使用既有编译器及实际受检项程序。这里的结论尚不等于含连接词和量词的完整 formulaProgram 执行定理；未将全公式程序中的其他分支视为已经处理。

## 对象证明链

1. FormulaAtomicProgramSyntax.membership_source／equality_source 消去既有原子程序中的五元／四元内部存在块。由 checked 项调用自身的 inputGuard 恢复真实源项类型，再组合源 ZeroScalar／构造码，用原 intro_member／intro_equality 规则重建源内部类型。此处仅用原推导规则，不需要 ZF 语义或宿主见证选择。
2. OriginalTypedAtomicCases 的四条定理消去源 membership／equality 的三元／二元内部字段存在块。实际 mode0／3 环境在存在量词下逐项重命名，源项类型组成 typedInputs，再调用已验收的已知字段整条 Run₃ 双条件。结论恢复原作用域，没有任何源字段的外部参数。
3. AtomicProgramMerge 在对象析取与蕴含规则中组合四条源类型条件下的双条件。正向对实际 atomic 的四个分支作对象析取消去；反向从程序分支恢复其源类型后使用对应双条件。无须额外假定分支分类结果。
4. OriginalAtomicProgram 从真实列表环境推导常量所需目标 contexts，实际推导四条条件双条件，取得统一结果，并改写为既有 Program 编译公式。
5. ObjectUnifiedAtomicProgram 逐组闭合所有对象变量，实际传输至原 nativeZF；CheckStep4 检查每组原核 Derives 类型。

## 文件与闭句

| 模块 | 产物 |
|---|---|
| FormulaAtomicProgramSyntax | 四分支原子程序、实际编译等式、重命名和源内部类型恢复 |
| OriginalTypedAtomicCases | mode0／3 的源 membership／equality 字段存在块消去 |
| AtomicProgramMerge | 原对象逻辑中的四分支组合 |
| OriginalAtomicProgram | 内部 atomic 守卫下统一运行及实际编译程序双条件 |
| ObjectUnifiedAtomicProgram | 七组 Source→TheoryTransport→ZFReplay 原核闭句 |

七组闭句：compiledAtomicProgramSource、replaceTypedMembershipWholeRunIff、replaceTypedEqualityWholeRunIff、replaceUnifiedAtomicProgramIff、weakenTypedMembershipWholeRunIff、weakenTypedEqualityWholeRunIff、weakenUnifiedAtomicProgramIff。

## 实际验收

定向 `lake build PPAC.Migration.Internal.ObjectUnifiedAtomicProgram --wfail` 与 `C:/Python314/python.exe -X utf8 scripts/verify.py` 均实际退出0。Lean／Lake 始终串行，LEAN_NUM_THREADS=1。

- 1480 构建任务、16068 项声明审计：381 无公理，15687 有允许的记录依赖，零警告。
- 九条命令全部退出0，其中五个原核 `--trust=0` 入口全部退出0。
- 新增5模块、45项显式声明、7组闭句；核心证书依赖精确为标准三项，native 精确为标准三项加原七项固定句子语法证书。
- 1800 对全工程精确证书足迹、13724 项 Internal 显式声明覆盖、1344 份独立 SHA256 一致。
- 七锁不变；YesMetaZFC 固定提交039c8e132cc19671d73a3933c66b4799d2599dd6干净；隔离 Choice 桥未修改。
- 既有45个执行定义、2个独立字段像、6个参数森林／双输出规格、17个纯公式定义和2个独立成员结果规格的 oracle 防护保留。
- 独立编译核心防护从原8模块扩展为9模块；新增 program／run 两个定义另行禁止调用原数值轨迹、旧替换判断或宿主求值器，独立复核也逐定义检查。

实际证据保留本地 verification/commands.json、audit.log、unified-atomic-readback.json。没有推送／PR，未运行 OpenAI 全仓或 Comparator。开发中曾修正局部公式名遮蔽目标变量 B，以及重复 raise 下对整个 Derives 类型作 simp 导致的上下文对齐问题；最终用显式公式相等传输，验收对应修正后的源码，没有禁用 linter。

## 工程流程与后续门

| 单元 | 状态与实现 | 对象验收 |
|---|---|---|
| 3f.2b.3 | 本批完成：消去内部字段，统一四类原子 | 具体模式环境与内部 atomic 守卫下，对任意内部 n／q 的原核闭句 |
| 3f.2c.1 | 下一步：连接词分支与实际子运行历史对齐 | 非量词 single／binary 的全候选对象双条件及整条 Run₃ 分派消去 |
| 3f.2c.2 | 实际变量像表的量词环境适用性与后继深度提升 | 同表稳定性／双表提升／真实子运行推导；不把任意固定层 Mixed.termList 当成稳定表 |
| 3f.2c.3 | 内部 FormulaCode 成员归纳，性质中量化全部变化参数 | 完整十一分支公式程序执行与替换对应的原核证书 |
| 后续 | quotation、数值 Option、原六规则／27模式、全 ProofZF/U、内部解释与 Con | 全部内部 ω 证明码上的检查／传输与最终 Con 蕴含 |

object_original_all_atomic_formula_program_cases_proved 本批开启为true；新增内部源字段消去、全候选实际编译程序双条件及独立原子子程序定义检查细门为true。完整公式执行／归纳、实际量词环境适用性、quotation、Option、ProofZF/U、内部解释及最终内部 Con 门继续为false。此后不得把本批原子终点当作最终主句完成。
