# mode1 完整公式对象归纳验收（2026-10-24）

本批 3f.2c.3b.2d.6i 完成实际 mode1 在任意内部深度、任意内部合法公式码上的完整递归正确性。全部 11 个原公式构造子均覆盖，包括量词；公式对象归纳假设和真实历史存在见证已消去。最终内部一致性主句尚未证明。

## 背景及最终目标

对象语言为纯等号／成员语言 ℒ，背景为原 `nativeZF`（完整 Separation、Collection，不加入 Choice）。源推导经 `TheoryTransport.sentence` 返回原 FirstOrder 核，再由 `ZFReplay.replay` 返回原 `nativeZF`。源推导、原核证书和 native 证书均为可检查证明项。

最终目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

这里 Con 是待完成的内部闭句规格，不能把宿主 `Consistent` 作为替代品。内部 ω 全部量化；Proof_T 精确核验原六规则／27 逻辑模式、完整 Separation／Collection。专用 ZF/U 检查器及其全内部码正确性尚未完成，故不能宣称上述主句已得到证明。

## 本批对象接口

`AbstractFormulaCorrectnessInduction.run_iff_execution` 的全部对象前提只有：

```text
Omega(w)
frame(w,mode,depth,P,a,b,c,e,R,S)
FormulaCode(w,n,a,b)
```

结论为原真实数值运行与既有独立执行的双条件：

```text
Run3(w,mode,depth,P,n,q)
  ↔ executed(w,R,S,a,b,c,e,n,q)
```

frame 包含真实 Num1、内部深度／参数元数据、实际两张项像码表及两类变量数值兼容。源 bound 长度 a 与目标 bound 长度 c 独立，free 目标长度为 e。该前提具有既有实际根环境构造及真实 binder 提升闭包证明，不是将最终运行等价式包装成 frame。

统一归纳公式使用对象 `ALL10` 绑定 mode、depth、P、a、b、c、e、R、S、q。原 ZF 集合归纳使用 Separation、Foundation 及已证传递覆盖；不依赖内部自然数外部标准性。每一步实际取得历史图并消去 EX 见证；binder 分别构造源／目标后继界，再取得实际提升表，不假定两界相等或自由表保持同码。

`AbstractTopFormula.run_iff_execution` 进一步从实际 `AbstractFreeTop` coded 环境、空深度及原元数据推导根 frame；该根接口也返回原核闭句证书。它仍要求实际环境及合法输入，尚未完成共享扩展语言 quotation／Bool 检查器的统一对应。

新增 14 模块、91 项显式声明、9 组闭句（每组均有源推导、原核传输及 native 证书）。`CheckStep4.lean` 包含展开的最终闭句验收，防止把 IH／历史前提隐入接口。

## 实际验收

| 项目 | 本批实际结果 |
|---|---|
| 定向编译 | 完整公式归纳 1432 项任务；接入实际根及闭句后 1434 项任务，均通过 |
| 全仓构建 | 1763 项任务，通过 |
| 声明审计 | 18840 项：399 无公理、18441 使用已记录依赖；零警告 |
| 检查命令 | 9 条退出 0；其中 5 个 `trust=0` 入口全部退出 0 |
| 工作区哈希 | 1598 份独立回读一致 |
| 证书足迹 | 2181 对精确核／native 证书足迹一致 |
| Internal 覆盖 | 16496 项显式声明纳入审计 |
| 新闭句足迹 | 核侧恰为 propext／Classical.choice／Quot.sound；native 侧另含锁定上游的 7 项固定公理原生计算证书依赖 |
| 上游与锁文件 | YesMetaZFC 固定于 039c8e132cc19671d73a3933c66b4799d2599dd6、上游工作区干净、7 个锁文件保持一致 |
| 原定义保存 | 原数值 Run、11 分支接受式、公式类型、独立执行／程序／历史及实际 binder 定义与验收基点 Git 字节一致 |

完整证据见 `verification/abstract-formula-readback.json`、`verification/summary.json`、`verification/commands.json`。本地复验命令：`C:/Python314/python.exe -X utf8 scripts/verify.py`；Lean/Lake 串行执行。

`trust=0` 的通过不代表清除了上游 7 项已记录依赖；本批没有引入新公理，也没有改写信任基线。

## 后续 agent 工程流程

| 顺序 | 输入与实现工作 | 对象层交付及验收 | 当前状态 |
|---|---|---|---|
| 1 | 原核 rename／instantiate、源 19 规则及 ZF 公理传输 | 返回原 FirstOrder.Derives 证书；保留完整背景与语言 | 既有批次已验收 |
| 2 | 实际 mode1 变量／项／参数列及 binder frame | 任意内部深度项／列表双条件，实际根及提升闭包；消去 Promise 与列表 IH | 既有批次已验收 |
| 3 | 本批完整公式递归 | ALL10 统一谓词、原集合归纳、真实历史 EX 消去、全部 11 构造子、原核闭句 | 本批已验收 |
| 4 | 原 Hilbert forall_generalization 节点 | 核对 arity=4、原嵌套头、4 条真实查询及全部赋值界；接实际 top 公式操作；返回完整节点双条件 | 下一步 |
| 5 | 其余原规则／27 模式／完整理论检查及共享 quotation | 保留原字段与准确作用域，证明原数值关系／共享 Bool 对全部内部合法码对应 | 待完成 |
| 6 | 专用 Proof_ZF／Proof_U 的有限纯 AST | 六规则、27 模式、完整 Separation／Collection；全部内部证明码的检查正确性 | 待完成 |
| 7 | 内部证书转换与完整数学解释 | 对象内部编译／检查传输；目标 ZF、PP、ACwo、¬AC 的原核证明 | 待完成 |
| 8 | 固定内部 Con 及最终蕴含 | 原 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，全内部 ω 证明码 | 尚未证明 |

执行下一单元时先固定精确目标句及所需原查询；只修改该单元模块。每批按定向编译、闭句传输、全仓构建／禁止缺口审计／精确足迹、独立回读、本地提交及提交后 Git 字节核对验收。历史批次日志不充作当前验收；不恢复退役反射实现。

公式构造中的全称／存在量词递归已经覆盖；原 Hilbert 全称化证明节点仍待完成。这两项不是同一验收目标。
