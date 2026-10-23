# 非量词连接词分派与实际历史条件桥验收

基点：aee0819ea539dd3ff17cab14d0265fa36ced0db2。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.1a：原 mode0／3 的否定与全部四种二元连接词完整 Run₃ 分派消去；在显式内部子码历史比较前提下，取得与既有实际 history read 程序分支的双条件。本批尚未消去该归纳比较前提，不是无条件的连接词总正确性，也不是最终 Con。

## 对象合同与比较公式

保持原 YesMetaZFC 单排序纯等词／成员语言、原 nativeZF 完整 Collection 和原 FirstOrder.Derives。最终要求 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC；内部 Con 覆盖全部内部 ω 证明码、原六规则／27 模式及完整 Separation／Collection。没有添加对象 AC、标准 ω、外部良基、新核或退役反射。

OriginalFormulaHistoryAgreementSyntax.agreement 是实际对象公式：

```text
∀x ∀X, (x∈n ∧ FormulaCode(w,x,a,b)) →
  (Run₃(w,mode,depth,parameter,x,X)
     ↔ FormulaTransformHistorySyntax.read(w,h,x,R,S,a,b,c,d,X)).
```

其中 x、X、n、h 以及所有环境参数都是对象变量；read 使用既有真实图边和七字段状态，不是宿主函数。比较仅要求严格子码且完整有类型的公式，保留后续 FormulaCode 成员归纳可用的守卫，没有把全部内部集合都当成合法公式。

该比较是明确的对象蕴含前提；本批没有假定新公理或宣称实际历史已经满足它。后续须从真实递归图、对象归纳假设及全变化参数的适用性实际推导这个公式，再在最终全公式正确性中消去归纳假设。

## 实际证明结果

OriginalLogicalChildTypes.negation／binary 从源父公式的完整 FormulaCode、实际构造码和 Ω(w)，恢复否定子公式或二元两个子公式的完整 FormulaCode。四种二元连接词由固定 Fin4 模式索引覆盖，各实例仍证明对象句子；不对运行时语法码作宿主解码。

OriginalLogicalCaseBridge.negation_iff／binary_iff 在 Ω(w)、源父 FormulaCode 和上述内部 agreement 下证明：

```text
原 unaryCase(4,w,mode,depth,parameter,n,q)
  ↔ FormulaTransformLogicalSyntax.single(4,false,w,h,R,S,a,b,c,d,n,q)
原 binaryCase(binaryTag(kind),3,w,mode,depth,parameter,n,q)
  ↔ FormulaTransformLogicalSyntax.binary(kind,w,h,R,S,a,b,c,d,n,q).
```

正向消去原局部两元／四元内部字段块，由实际源构造器推出子码严格属于父码，再恢复子 FormulaCode，实例化内部 agreement，把真实 Run₃ 子调用换成真实 read。反向消去既有程序的内部字段块，用实际严格子码守卫与恢复的完整类型实例化 agreement，重建原真实子调用和原节点。源／目标字段始终是对象存在见证。

OriginalLogicalRunDispatch.outcomes_iff_negation／binary 逐一排除原十一分支中的其余十个分支，包括实际 App 的异标签冲突。run_iff_negation／binary 在内部 Num0／Num3、depth／parameter 自然性与已知源构造码下，取得整条原 Run₃ 与相应局部分支的双条件。该分派消去不需要 history agreement。

OriginalLogicalProgram.negation_iff／binary_iff 合成整条原运行与既有逻辑程序分支：

```text
Ω(w), Num(mode0或3), metadata(w,depth,parameter),
FormulaCode(w,n,a,b), 已知源否定／二元构造码,
内部子码 history agreement
  ⊢ Run₃(w,mode,depth,parameter,n,q)
       ↔ 对应既有 single(false)／binary 程序分支。
```

q 仍是任意内部输出候选，没有预给目标形状、自然性、根行或共享完整轨迹集合。实际历史 h 是否存在、是否满足上述比较，仍由后续递归图和归纳工程解决。

## 新增模块与闭句

| 模块 | 对象产物 |
|---|---|
| OriginalFormulaHistoryAgreementSyntax | 严格且有类型子码上的全内部比较、重命名及实例化 |
| OriginalLogicalChildTypes | 否定与四种二元连接词的完整子 FormulaCode 恢复 |
| OriginalLogicalCaseBridge | 两个方向消去原／既有字段块，连接真实子 Run₃ 与 read |
| OriginalLogicalRunDispatch | 五类非量词连接词的原十一分支排除及整条运行双条件 |
| OriginalLogicalProgram | 带显式内部比较前提的整条原运行／既有分支对应 |
| ObjectOriginalLogicalProgram | 九组 Source→TheoryTransport→ZFReplay 原核闭句 |

九组闭句：logicalHistoryAgreementAt、negationChildFormulaCode、binaryChildrenFormulaCode、negationLocalHistoryIff、negationWholeRunDispatchIff、negationWholeRunHistoryConditionalIff、binaryLocalHistoryIff、binaryWholeRunDispatchIff、binaryWholeRunHistoryConditionalIff。

所有闭句具有原 nativeZF 中实际 Derives 证书；条件桥的原生句子中保留 agreement 蕴含前提。没有把条件证书改写成无条件主句。

## 实际验收

定向 `lake build PPAC.Migration.Internal.ObjectOriginalLogicalProgram --wfail` 与 `C:/Python314/python.exe -X utf8 scripts/verify.py` 实际退出0；Lean／Lake 始终串行，LEAN_NUM_THREADS=1。

- 1486 个构建任务，16117 项声明审计：381 无公理，15736 有允许的记录依赖，零警告。
- 九条命令全部退出0，其中五个原核 `--trust=0` 入口全部退出0。
- 新增6模块、49项显式声明、9组闭句；核心证书依赖精确为标准三项，native 精确为标准三项加原七项固定句子语法证书。
- 全工程1809对精确证书足迹、13773项 Internal 显式声明覆盖、1350份独立 SHA256 一致。
- 七锁不变，YesMetaZFC 固定提交039c8e132cc19671d73a3933c66b4799d2599dd6干净；隔离 Choice 桥不变。
- 既有独立编译9模块、原子 program／run 两定义及45+2+6+17+2项执行定义防护全部保留。本批新 agreement 是显式比较公式，不是独立执行原语。

实际证据保留本地 verification/commands.json、audit.log、logical-history-readback.json。没有推送／PR，未运行 OpenAI 全仓或 Comparator。开发中修正了一个未使用的 simp 参数和生成的一个多余括号；实际验收对应修正后源码，没有禁用 linter。

## 工程流程与验收门

| 单元 | 实现／状态 | 对象层验收 |
|---|---|---|
| 3f.2c.1a | 本批完成：非量词连接词完整分派与实际 read 条件桥 | 上述九组原核闭句；比较前提显式保留 |
| 3f.2c.1b | 下一步：从实际递归图和适当对象归纳假设构造 history agreement | 先证明实际 read↔executed，再量化严格有类型子码，合成归纳比较；不把尚未证明的归纳假设当作全正确性 |
| 3f.2c.2 | 实际量词环境适用性及后继深度／双表提升 | 真实同表稳定性、环境提升及子运行推导，不能使用任意固定层 Mixed.termList 的伪稳定性 |
| 3f.2c.3 | 全内部 FormulaCode 成员归纳，性质中量化全部变化参数 | 消去归纳比较前提并完成十一分支公式执行／替换对应 |
| 后续 | quotation、数值 Option、原六规则／27模式、全 ProofZF/U、内部解释与 Con | 全内部 ω 证明码上的检查／传输与最终 Con 蕴含 |

本批仅开启非量词完整分派、真实子 FormulaCode 恢复、显式 history 前提下条件双条件三个细门。统一原子门保持true；object_original_formula_actual_history_agreement_discharged_proved、object_original_nonbinder_logical_program_cases_proved 及完整公式／量词／归纳／quotation／Option／Proof／Con 门保持false。
