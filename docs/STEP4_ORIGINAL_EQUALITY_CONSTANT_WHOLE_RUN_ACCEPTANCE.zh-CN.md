# 原等词与常量完整运行验收

基点：83c01c163ae0731c1e6dbe69f48b35e184d5d110。完成 S3.4c.2b.2c.3c.2c.2b.3f.2b.2b：在已知有类型原等词／常量输入处，原 mode0／3 整条 Run₃ 与既有 equality／nullary 原子程序接口双向对应。统一内部 atomic 谓词的总桥及最终 Con 尚未完成。

## 对象合同与具体结论

对象语言仍为原 YesMetaZFC 单排序纯等词／成员语言。背景为原 nativeZF，含完整 Collection；正式关系仍为原 FirstOrder.Derives。最终目标是 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 保持全部内部 ω 证明码、原六规则／27 模式及完整 Separation／Collection，不添加对象 AC、标准 ω、外部良基、新核或退役反射。

本批闭句的每个实例有 Source.ZF 中的实际推导，经 TheoryTransport.sentence 和 ZFReplay.replay 返回原 nativeZF。自然标签、固定构造器元数、Bool 模式及变量位置是外部模式索引；运行时输入、输出、载荷、子项及数码见证均在对象公式中量化。闭句构造不携带无用的宿主标签不等证明参数；实际推导使用该固定标签不等式。

OriginalAtomicExistingAtom.replace_equality_iff／weaken_equality_iff 保留已经验收的实际恒等／位移／转换列表环境、内部 metadata、源 EqualCode 和两个源项类型，得到：

```text
mode3 实际环境下：
 Run₃(w,mode,depth,L,n,q)
   ↔ FormulaTransformAtomSyntax.equality(w,R,L,a,b,a,c,n,q)
mode0 实际环境下：
 Run₃(w,mode,depth,parameter,n,q)
   ↔ FormulaTransformAtomSyntax.equality(w,R,S,a,b,a,B,n,q)
```

OriginalAtomicExistingAtom.constant_iff 对两个模式和两个 truth 固定实例，在 Ω(w)、对应 Num0／Num3、metadata、源 nullary 类型和目标 contexts 下得到：

```text
 Run₃(w,mode,depth,parameter,n,q)
   ↔ FormulaTransformAtomSyntax.nullary(truth,w,a,b,c,d,n,q).
```

q 在所有结论中仍是任意内部集合候选。没有预给目标构造码、输出自然性、共享完整轨迹集合或根行；等词的受检项比较沿用上一批已经实际证明的全内部 agreement，没有新增比较公理。

## 分派消去与证明链

1. OriginalFormulaTagRejection 对任意已知 Ctor(k,tag,xs,n) 给出错误 constant／binary／unary／binder 标签排除。
2. 原 App 由三个内部见证给出 Scalar、实际 Cons 载荷、Num2 和 Raw 节点。载荷自然性由 StructuralConsCore.range 推出，Num2 自然性由 SyntaxNumerals.range 推出。消去已知构造器的实际标签见证后，用 SyntaxNodeInjective.raw_tag_eq 得到标签相等，再用 SyntaxNumerals.different 导出矛盾。没有假设参数森林自然性，也没有宿主解码或 Type 层见证选择。
3. 将该结果提升到原 applicationCase 的内部三元存在块。OriginalAtomicRunDispatch 在源标签0、1、3处逐一排除完整十一分支中的其余十个分支，给出 outcomes 双条件；再与已验收 OriginalFormulaRunEquation.run_iff 合成整条 Run₃ 双条件。
4. OriginalAtomicExistingAtom 接上上一批实际等词／常量局部接口。成员整条运行的既有接口沿用上一批证书。
5. ObjectWholeAtomicInterfaces 的八组闭句全部回放原核；CheckStep4 中逐组检查原生 Derives 类型。

## 新增文件及闭句

| 模块 | 对象产物 |
|---|---|
| OriginalFormulaTagRejection | 通用构造器异标签排除及原 App 的实际标签2排除 |
| OriginalAtomicRunDispatch | 源常量0／1和等词处的完整十一分支筛选及 Run₃ 双条件 |
| OriginalAtomicExistingAtom | 实际 mode0／3 等词、两个常量的既有原子程序接口 |
| ObjectWholeAtomicInterfaces | 八组 Source→TheoryTransport→ZFReplay 闭句 |

八组闭句为 rawApplicationWrongTagRejected、applicationCaseWrongTagRejected、wholeFalseDispatchIff、wholeTrueDispatchIff、wholeEqualityDispatchIff、replaceWholeEqualityExistingAtomIff、weakenWholeEqualityExistingAtomIff、wholeConstantExistingAtomIff。

## 实际验收

定向 `lake build PPAC.Migration.Internal.ObjectWholeAtomicInterfaces --wfail` 与 `C:/Python314/python.exe -X utf8 scripts/verify.py` 实际退出0。构建始终串行，LEAN_NUM_THREADS=1。

- 1475 构建任务，16023 项声明审计：380 无公理，15643 有允许的记录依赖，零警告。
- 九条命令全部退出0，其中五个原核 `--trust=0` 入口全部退出0。
- 新增4模块、48项显式声明、8组闭句；核心证书依赖精确为标准三项，native 精确为标准三项加原七项固定句子语法证书。
- 1793 对全工程精确证书足迹、13679 项 Internal 显式声明覆盖、1339 份独立 SHA256 一致。
- 七个锁文件未变；YesMetaZFC 固定提交039c8e132cc19671d73a3933c66b4799d2599dd6干净；隔离 Choice 桥未修改。
- 既有45个执行定义、2个独立字段像定义、6个参数森林／双输出规格、17个纯公式定义和2个独立成员规格的 oracle 防护保留。本批只增加推导，不增加独立执行 AST 定义。

`verification/commands.json`、`audit.log`、`whole-atomic-readback.json` 为本地实际证据。没有推送／PR，未运行 OpenAI 全仓或 Comparator。第一次闭句定向构建发现两个未使用标签不等证明参数；已从句子构造中移除后重建，全仓验收对应修正后的源码。

## 下一步及验收门

| 单元 | 具体实现 | 对象层验收 |
|---|---|---|
| 3f.2b.2b，本批完成 | 原等词／常量整条运行接上既有接口 | 八组原 nativeZF 闭句及上述实际审计 |
| 3f.2b.3 | 消去 SyntaxAtomSyntax.atomic 中源成员／等词的内部字段存在块，统一四类原子与既有原子程序分支 | 实际内部 atomic 输入守卫下的全输入／输出 Derives 双条件，届时才开启完整原子门 |
| 3f.2c.1 | 连接词的原子运行与实际历史子运行对齐 | 各连接词完整 Run₃ 与既有分支的对象推导 |
| 3f.2c.2 | 实际变量像表在量词后继深度的适用性及环境提升 | 同表稳定性／提升和真实子运行推导，不能以任意固定层 Mixed.termList 替代 |
| 3f.2c.3 | 对内部 FormulaCode 作成员归纳，性质中量化全部变化参数 | 完整公式执行／替换双条件的原核证书 |
| 后续 | quotation、数值 Option、原六规则／27模式、全 ProofZF/U、内部解释与 Con | 全部内部 ω 证明码上的检查／传输及最终 Derives nativeZF [] (Con_ZF → Con_target) |

本批只把实际 App 标签2排除、等词完整运行既有接口、常量完整运行既有接口三个细门设为true。object_original_all_atomic_formula_program_cases_proved 保持false：四种外部已知形状的端点尚未合成为带内部存在字段的统一 atomic 定理。完整公式／归纳、量词适用性、quotation、Option、ProofZF/U、内部解释及最终 Con 门保持false。
