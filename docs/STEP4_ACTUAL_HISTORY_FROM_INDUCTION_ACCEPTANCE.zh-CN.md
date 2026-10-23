# 实际递归历史与对象归纳比较构造验收

基点：8b801fa802f779c83f9a172b9bb72d46f5234d73。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.1b：实际递归图上的 read 与完整执行关系对应；从明确的对象归纳假设推出完整历史比较，并在对象存在量词中构造同时携带真实递归图和比较公式的历史。全公式归纳假设仍待消去，最终 Con 尚未证明。

## 对象合同

保持 YesMetaZFC 原纯等词／成员语言、原 nativeZF 完整 Collection 和原 FirstOrder.Derives。最终要求 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 覆盖全部内部 ω 证明码、原六规则／27模式和完整 Separation／Collection。没有添加对象 AC、标准 ω、外部良基、新核或退役反射。

六组闭句具有实际 Source.ZF 推导，经 TheoryTransport.sentence 与 ZFReplay.replay 返回原 nativeZF。运行时域、历史、公式码、项像表与所有输出都是对象变量；历史见证仅经原 exI／exE 引入和消去，不抽取为 Lean 宿主函数。

## 实际历史读取与执行对应

OriginalHistoryRead.read_iff_executed 对任意内部序数域 D、x∈D 和真实 FormulaTransformRecursionSyntax.graph(w,h,D)，在 Ω(w) 下证明：

```text
FormulaTransformHistorySyntax.read(w,h,x,R,S,a,b,c,d,q)
  ↔ FormulaTransformExecutionSyntax.executed(w,R,S,a,b,c,d,x,q).
```

证明实际传输同一个递归图，使用已证明的 read_iff 与 execution_iff 组合；真实独立程序 read 与已验收查询 read 的定义对齐已由 Lean 检查。没有修改独立程序定义或用旧替换判断作为执行原语。

## 对象归纳假设与内部历史存在

OriginalFormulaInductionSyntax.prefixIH 是固定当前环境下的对象公式：

```text
∀x ∀X, (x∈n ∧ FormulaCode(w,x,a,b)) →
  (Run₃(w,mode,depth,parameter,x,X)
     ↔ executed(w,R,S,a,b,c,d,x,X)).
```

它保留严格子码和完整源 FormulaCode 守卫，并对全部内部输出 X 量化。prefixIH_rename／prefixIH_at 提供实际重命名和对象全称实例化。它仍是须由后续对象成员归纳证明的前提；没有作为新公理引入。

OriginalHistoryFromInduction.from_graph 在 Ω(w)、内部 ordinal(n)、真实 graph(w,h,n) 和 prefixIH 下，实际推导上一批的整个内部 history agreement。证明在两个对象全称量词下引入严格有类型守卫，实例化 prefixIH，并与实际 read↔executed 反向合成。

OriginalHistoryFromInduction.exists_agreed_history 进一步在 Ω(w)、源父 FormulaCode(w,n,a,b) 和 prefixIH 下证明：

```text
∃h, FormulaTransformRecursionSyntax.graph(w,h,n)
      ∧ historyAgreement(w,mode,depth,parameter,h,R,S,a,b,c,d,n).
```

根 n 的自然性由源 FormulaCode.guards 推出，内部序数性由原 ZF 中的自然数序数定理推出，无额外根序数前提。原递归存在定理构造 graph；消去其内部历史见证后，用同一个 h 证明全内部比较，再重新装入存在包。这里没有把内部自然数当成外部标准数。

agreedHistory 的构造不含根输出 q，携带的比较已对全部子码输出 X 量化；没有为每个候选输出分别在宿主层选择历史。

## 非量词连接词接入

OriginalLogicalFromInduction.negation_iff／binary_iff 保留原 mode0／3、metadata、源父类型和源构造码前提，把上一批单独保留的 history agreement 替换为真实 graph(w,h,n) 与上述对象 prefixIH，再实际推导比较并调用整条原 Run₃ 条件桥：

```text
真实递归图 + 对象 prefixIH + 实际源模式／类型／构造前提
  ⊢ 原完整 Run₃ ↔ 既有否定／四种二元连接词实际历史程序分支。
```

此处 q 为任意内部候选，无目标形状、目标自然性、根行或共享原数值轨迹集合前提。归纳假设仍然保留；本批不能据此宣称全公式或完整非量词正确性无条件成立。

## 新增模块与原核闭句

| 模块 | 实际产物 |
|---|---|
| OriginalHistoryRead | 真实递归图上的 read↔executed |
| OriginalFormulaInductionSyntax | 内部 prefixIH、实际历史存在包及其原规则接口 |
| OriginalHistoryFromInduction | 从真实图和对象归纳假设推导比较，并构造存在历史 |
| OriginalLogicalFromInduction | 否定／二元连接词的真实历史与对象归纳接口 |
| ObjectActualFormulaHistory | 六组 Source→TheoryTransport→ZFReplay 闭句 |

闭句为 actualHistoryReadExecutedIff、prefixInductionAt、actualHistoryAgreementFromInduction、agreedActualHistoryExists、negationActualHistoryFromInductionIff、binaryActualHistoryFromInductionIff。

## 实际验收

定向 `lake build PPAC.Migration.Internal.ObjectActualFormulaHistory --wfail` 及 `C:/Python314/python.exe -X utf8 scripts/verify.py` 实际退出0。Lean／Lake 严格串行，LEAN_NUM_THREADS=1；本批新增源码在全仓验收前已逐行检查空白及 UTF8／LF。

- 1491 构建任务、16154 项声明审计：381 无公理，15773 有允许的记录依赖，零警告。
- 九条命令全部退出0，其中五个原核 `--trust=0` 入口全部退出0。
- 新增5模块、37项显式声明、6组闭句；核心证书精确依赖标准三项，native 精确为标准三项加原七项固定句子语法证书。
- 1815 对全工程精确证书足迹、13810 项 Internal 显式声明覆盖、1355 份独立 SHA256 一致。
- 七锁及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变，隔离 Choice 桥不变。
- 独立编译9模块、原子 program／run 两定义及45+2+6+17+2项执行定义防护保留。本批新定义是显式归纳比较／存在包，不是独立执行原语。

实际证据保留本地 verification/commands.json、audit.log、actual-history-readback.json。没有推送／PR，未运行 OpenAI 全仓或 Comparator。

## 后续工程与范围

| 单元 | 实现／状态 | 对象验收要求 |
|---|---|---|
| 3f.2c.1b | 本批完成：实际 read／执行对应，图与对象 IH 构造比较及内部历史 | 六组原核闭句，IH 前提明确保留 |
| 3f.2c.2a | 下一步：明确可在量词下提升的实际模式环境及量化全部变化参数的归纳性质 | 对象环境公式与逐参数实例化；不能把当前固定环境 prefixIH 当成全环境归纳 |
| 3f.2c.2b | 实际量词环境、后继深度及双表提升 | 使用真实自由变量像表稳定性及原后继规则证明 binder 分支，不能假定任意 Mixed.termList 同表稳定 |
| 3f.2c.3 | 全内部 FormulaCode 成员归纳及完整程序方程装配 | 消去对象 IH，连接完整十一分支 formulaProgram／executed；四分支 atomProgram 不能直接替代它 |
| 后续 | quotation、数值 Option、原六规则／27模式、全 ProofZF/U、内部解释与 Con | 全内部 ω 证明码的检查／传输与最终 Con 蕴含 |

本批仅开启真实 read／executed、真实图与对象归纳推出比较、对象归纳下实际历史存在、连接词历史前提被真实图与归纳替换四个细门。统一原子门保持true；全局实际历史比较已消去、完整非量词、完整公式／量词／归纳、quotation、Option、ProofZF/U、内部解释及最终 Con 门继续为false。
