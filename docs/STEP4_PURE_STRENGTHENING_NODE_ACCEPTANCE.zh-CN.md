# 原 mode0 完整公式运行与 strengthening 完整节点验收

基点：e09c878ac89b82e79775b0d05ebb6f989cef9173。单元3f.2c.3b.2d.5；8模块110项显式声明、16组闭句。

## 对象背景和边界

固定纯等词／成员对象语言、原 nativeZF 的全 Separation／Collection 和原 FirstOrder.Derives。内部 Con 对全部内部 ω 证明码量化，包含原六规则／27逻辑模式与完整 ZF 模式；不要求内部自然数外部标准。最终目标仍未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批完成原 mode0 在所有内部合法公式上的自由头槽弱化对应，以及原 strengthening 的完整有界纯关系式局部节点。所有新闭句通过 Source→TheoryTransport→ZFReplay 传输至原 nativeZF。共享扩展条件的原数值 quotation／Bool 对应及最终 Con 没有因此完成。

## mode0 完整公式运行

OriginalWeakenFormulaRun.at_codes_iff 取实际恒等索引码 I、自由位移码 J、两张项像码 R／S，使用已验收的 OriginalFormulaCorrectnessInduction.run_iff_execution false 和 OriginalOperationFrameRules.from_weaken。再经实际 IndexFormulaRenameBridge 及 SyntaxWeakenFreeUnique，得到：

```text
Ω(w), Num0(mode), metadata(w,depth,P), FormulaCode(w,n,a,b), Succ(B,b)
  ⊢ Run3(w,mode,depth,P,n,q) ↔ Weakened(w,a,b,B,n,q).
```

typed_iff 从原对象存在性取得 I、J，并用 IndexTermImageEnvironment 取得 R／S；全部四个见证经原对象 EX 消去，不作为最终前提。深度和参数 P 仍是任意内部自然值，输入／输出 q 没有被限制为外部可枚举的标准码。program_iff 进一步接独立 WeakenFreeProgramSyntax.executed；output_type 给出输出的正确自由变量界 B。

这是完整公式的运行合同，不是先前仅自由变量分支的 OriginalFreeWeaken 结果。证明复用已有全公式对象归纳，没有恢复退役反射或新增公理。

## 原 strengthening 四查询

所有查询直接取 strengtheningShape.queries[0…3].2，actual_* 用 rfl 核查查询种类和 Expr：

| 索引 | 原查询 | 对象对应 |
|---|---|---|
| 0 | formula(v0,v1) | FormulaCode(w,v1,z,v0) |
| 1 | projection(v2,0,succ(v0)) | Succ(B,v0) 下 RawField(w,v2,z,B) |
| 2 | projection(v2,1,v3) | atOne(w,v2,v3) |
| 3 | transform0(literal0,v1,v3) | 第0查询及 Succ(B,v0) 下完整 WeakenFreeProgram(w,z,v0,B,v1,v3) |

原第3查询实际行是 node3[0,0,0,v1,v3]。transform_at_zero 将其真实 Expr 图接到原完整变换轨迹；guarded_transform_iff 用第0真实公式查询推出输入类型，再调用本批完整 mode0 公式定理。第3查询的类型条件没有被略去。

ProofStrengtheningSyntax.bundle 按原顺序合并全部四个真实查询，接受定义不使用类型、RawField、弱化程序或宿主求值规格作为预言机。at_successor_iff 在给定真实后继 B 时证明全部四查询双条件；bundle_iff 再用原 Pairing／Union 的 InsertExistence 构造 B 并在对象 EX 内消去。所得规格是：

```text
∃B [Succ(B,env0) ∧ FormulaCode(w,env1,z,env0) ∧
  RawField(w,env2,z,B) ∧ atOne(w,env2,env3) ∧
  WeakenFreeProgram(w,z,env0,B,env1,env3)].
```

B 是共同的内部见证；不从宿主 Nat 计算，也不预给位移码表或解码轨迹。

## 全部四赋值及原有界节点

原 arity=4，实际头为 node4[v0,v1,v2]，只有三个字段。前三赋值从原头图取得界；隐藏 env3 由实际第2查询得 env3≤env2，再传递到父码。无需假设前驱是合法证明。

ProofStrengtheningNodeSyntax.node 是原四赋值的有界对象 EX 块，内含自然赋值、全部搜索界、实际原头和全部四查询。specification 保留相同四赋值 EX、自然性与原头，使用上一节四查询规格。反向搜索界由实际第2查询重新推导，最终：

```text
Ω(w) → Empty(z) → [PureStrengtheningNode(w,row) ↔ StrengtheningSpecification(w,z,row)].
```

无预给 envNat／bounds／后继值／码表／查询／合法前驱／归纳假设。四个赋值及后继 B 均在对象公式内部绑定。原 HornApplicationBounds.existsMany_congr 逐四个 EX 传递局部矩阵的实际对象推导。

## 实际验收

1683构建任务、18126项审计（398无公理／17728允许依赖）、零警告；九命令及五trust=0入口全部退出0；1518份独立哈希一致、2072对精确证书足迹、15782项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail；九命令及五个 trust=0 入口实际退出0。110项新增显式声明全部纳入 Audit。
- 16组新增核心／native证书符合精确既有足迹：核心三项标准公理；native额外继承固定七个基础句子证书。没有新增自定义公理。
- CheckStep4 核查原 arity4、三字段头、全部四查询数、第1后继投影和第3 mode0查询，并展开最终四个对象 EX 合同。
- 独立读回检查完整 mode0 的输入前提集合、实际四张码表的构造／消去、后继值来自 Pairing／Union、搜索界来自真实查询，以及最终节点只有 Ω／空集零值前提。
- 原 MP／替换节点、原变换查询、弱化程序和全公式归纳引擎保持基点 Git 字节不变；七份锁及 YesMetaZFC 固定提交／干净状态不变。

机器证据：verification/proof-strengthening-node-readback.json、verification/summary.json、verification/commands.json；本地生成／读回脚本位于 .local。

## 下一阶段流程

| 单元 | 实现动作 | 原核验收合同 | 当前状态 |
|---|---|---|---|
| substitution／MP／strengthening | 确切原查询、全部赋值界、完整有界EX | Ω／空集零值下纯关系式节点双条件 | 已验收 |
| forall | 原嵌套node9头、succ自由界投影、mode1完整公式操作 | 完整局部节点及全部四赋值，不能仅交付条件式程序合同 | 下一阶段 |
| logical／theory | 原27逻辑模式与完整ZF／U公理检查 | 真实内部判定的对象正确性 | 待完成 |
| 共享原条件 | 纯关系式合同与扩展条件、数值quotation、Bool／Option | 实际定义间的对象推导 | 待完成 |
| 内部Proof与编译 | 原六规则、完整公理、任意内部证明序列 | ProofZF／U正确性与内部编译 | 待完成 |
| 内部解释与Con | 逐公理解释、内部推导传输 | Derives nativeZF [] (Con_ZF→Con_target) | 未证明 |

旧通用 strengthening兼容性／共享checker和最终Con门禁仍是false；新增完整mode0运行／strengthening纯关系式门禁为true。固定有限模式索引为外部参数，运行自然数、公式码、函数图和全部存在见证均在对象理论中处理。
