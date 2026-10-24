# 实际首槽公式与原全称化节点验收（2026-10-24）

本批 3f.2c.3b.2d.6j 完成 mode1 完整公式运行到实际 AbstractFreeTop 的对象对应，并完成原全称化的完整局部纯关系节点：原四查询、四赋值界及实际嵌套头规范化。最终内部 Con 蕴含尚未证明。

## 背景及最终目标

对象语言为纯等号／成员语言，背景是原 nativeZF，保留完整 Separation／Collection，不加入 Choice。最终目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

内部 Con 覆盖全部内部 ω 证明码、原六规则与 27 逻辑模式。专用 Proof_ZF／Proof_U、全内部码检查／转换、完整内部解释及最终主句仍未完成。

## 本批实际对象接口

`AbstractTopFormulaOperation.run_iff` 从 Ω、Num1、原零深度元数据、empty(z)、实际首槽输入及合法源公式，推出原 Run3 与既有 `SyntaxTopFormulaSyntax.abstracted` 的双条件。证明组合完整公式运行、执行／混合公式判断等价及实际码表唯一性；两张码表由原对象存在性定理构造，再在对象 EX 中消去。

最终 guarded_iff 将源类型放在结论内部：

```text
FormulaCode(w,n,a,B) ∧ Run3(w,mode,z,P,n,q)
  ↔ abstracted(w,a,b,A,B,n,q)
```

其前提不含源类型、R/S、历史图、IH 或 Promise。右端推出源类型的既有对象定理支撑反向守卫；未加类型守卫的原 Run3 不在本批无效输入拒绝结论之内。

原 `ObjectProofNode.forallShape` 保持 arity=4，head 为 `node3[v0,node9[v1],v2]`；原四查询依序为 Formula(succ(v0),v3)、Projection(v2,0,succ(v0))、Projection(v2,1,v3)、Transform(1,0,v3,v1)。接受判断直接引用原表达式与原完整数值变换轨迹，比较规格使用实际 FormulaCode、前驱原始字段和 AbstractFreeTop。

A=succ(z) 与 B=succ(v0) 分别用原 Pairing／Union 构造并由对象 EX 消去；Num1(A) 实际由 empty(z) 与 successor(A,z) 推出。第四赋值 v3 通过前驱的第 1 原始字段取界，再与 v2<row 传递组合。其他三赋值在实际头中取界，包括嵌套 node9 内的 v1；不要求前驱预先是合法证明。

`ProofForallHead.head_iff` 将原头求值等价于内部存在中间码的两个真实数值构造判断：constructor(1,9) 与 constructor(3,3)。中间码由实际表达式的对象存在性取得并消去，没有调用宿主 Expr.eval。

最终 `ProofForallNode.normalized_node_iff` 只有 Ω 与 empty(z) 两个对象前提，覆盖四个原赋值存在量词及全部搜索界。14 组闭句经 TheoryTransport.sentence 与 ZFReplay.replay 返回原 FirstOrder.Derives nativeZF []。CheckStep4 含展开的完整操作及完整节点闭句。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句 | 9／121／14 组 |
| 定向编译 | 实际操作1434、四查询1549、节点1564、嵌套头1563、native接入1566项任务，全部通过 |
| 全仓构建 | 1772 项任务，通过 |
| 声明审计 | 18961：399无公理、18562允许依赖；零警告 |
| 检查命令 | 9条退出0，含5个trust=0入口 |
| 独立工作区哈希 | 1607份一致 |
| 精确证书足迹 | 2195对一致 |
| Internal显式覆盖 | 16617项 |
| 上游与锁文件 | 固定039c8e132cc19671d73a3933c66b4799d2599dd6、上游干净、7个锁文件不变 |
| 原定义 | 原Run／查询／字段／公式类型、实际top判断、执行及上批完整归纳与基点Git字节一致 |

核侧闭句依赖恰为 propext、Classical.choice、Quot.sound；native 侧另含上游锁定的7项固定公理原生计算证书依赖。本批未增加新公理或改写信任基线；trust=0通过不表示既有依赖消失。

证据为 verification/forall-node-readback.json、verification/summary.json、verification/commands.json。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`，Lean/Lake串行。

报告写入时C盘耗尽；随后仅对本工程verification／.local中的1427份生成文件实施NTFS压缩，全部逻辑字节SHA256与长度不变，没有删除其他项目或应用。

## 后续 agent 工程流程

| 顺序 | 实现工作 | 对象交付与状态 |
|---|---|---|
| 1 | 原source19规则、rename／instantiate、背景公理传输 | 原核Derives证书，既有批次已验收 |
| 2 | 原mode0／3及mode1项／列表／完整公式、真实binder | 全内部合法码对应及IH／历史消去，相应批次已验收 |
| 3 | mode1实际AbstractFreeTop及原全称化节点 | 原四查询、四搜索界、嵌套数值头，本批已验收 |
| 4 | 原mode2实际InstantiateTop | 从原变量点／前驱规则到实际环境及全内部项／列表／公式，真实binder闭包与根，下一单元 |
| 5 | 原27逻辑模式、理论公理及剩余证明节点 | 准确arity／头／查询／赋值界及完整ZF/U公理实例，待完成；若采用共享Bool作桥，须证明准确对应 |
| 6 | 专用纯ℒ Proof_ZF／Proof_U及内部证书转换 | 六规则／27模式、全部内部ω、完整Separation／Collection及检查／编译正确性，待完成 |
| 7 | 完整数学内部解释与目标理论 | 原核内解释设施及ZF、PP、ACwo、¬AC，待完成 |
| 8 | 最终内部Con蕴含 | 原Derives nativeZF [] (Con_ZF→Con_target)，尚未证明 |

下一单元先盘点原mode2数值规则与既有实际InstantiateTop环境。原逻辑模式20／23／25使用transform2，21／24使用transform1；不能用mode1结果或外部标准quotation模式替代mode2全内部正确性。每批执行定向编译、原核闭句、全仓构建／禁止缺口／精确足迹、独立回读、本地提交及提交后字节核对。

本批是完整局部纯关系节点；共享扩展语言quotation／Bool、全Proof检查器及最终内部Con仍未完成。
