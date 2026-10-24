# mode2 源码进展（未编译，2026-10-24）

本文件记录按用户“先继续不依赖编译的代码工作”要求保存的源码草稿。**本批没有运行 Lean/Lake，没有新增已验收对象定理。** 最后完整验收基点仍为 b22054a34c9ff1d88fc37666adf82f6ee1cbdf9a。

最终目标保持原 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target=ZF+PP+ACwo+¬AC；纯等号／成员语言、完整 Separation／Collection、六规则／27模式及全部内部ω证明码的 Con 规格不变。最终 Con 仍未证明。

## 本批实现源码

7 个模块、71 个显式声明，均标记待编译：

| 模块 | 已写入源码的职责 |
|---|---|
| OriginalInstantiateClasses | 按完整原28规则逐项分类，保留mode2的boundIdentity／boundPoint／boundPredecessor／freeIdentity／application五条项规则；变量再分绑定三条及自由一条 |
| OriginalInstantiateDispatch | 使用真实Num2行字段消去错误模式，再按实际变量输入分派；结论为原完整step与选定原规则step的对象双条件 |
| OriginalInstantiatePositive | 原四条变量规则的真实守卫及完整表闭轨迹引入；复用原head赋值界与原闭轨迹构造 |
| OriginalInstantiateTrace | 取得并对象EX消去原全根集合，返回原condition与真实变量规则step的双条件 |
| InstantiateVariableValueSyntax | 独立变量数值规格、重命名、后继分支EX引入及输出自然性辅助；定义不含原Run／Trace／程序比较器 |
| InstantiateVariableSound | 从实际原五字段行及规则矩阵推导四类数值分支；绑定点的输出确为参数字段；实际application赋值EX消去 |
| InstantiateOperationFrameSyntax | 真实Num2、元数据、空绑定参数、实际两张像表、内部ALL3变量兼容及精确上下文长度不变量；已写取自由参数分支的对象推导源码 |

数值分支按原规则保持：bound索引i∈depth时输出原变量；i=depth时输出参数码P；i=succ(k)且depth∈i时输出bound变量k；free变量输出原变量码。这里i、depth、P和输出均为内部对象变量，不限制外部标准自然数。

## 原入口决定的关键约束

固定上游原逻辑模式20、23、25均要求替换项的bound上下文为0，源公式bound上下文为1，并调用transform2。原量词递归增加depth而保持参数P原码。实际InstantiateTop允许更一般的目标bound长度，后续数值对应须先严格覆盖原入口所需的空绑定参数范围。

frame因此显式包含内部存在空集z及Term(w,z,e,P)。已写的closedParameter_free消去这个内部z，并复用既有EmptyBoundFreeInputs.term_free，取得实际自由变量分支。参数在实际binder bound提升后保持同码的证明仍待补齐。

frame还包含sourceBound=succ(depth)、targetBound=depth、targetFree=sourceFree。该不变量符合原bound1公式在量词下逐步增加上下文的路线；实际根和binder保持这些关系的正式推导尚待完成。它也允许在合法源索引范围内排除大于depth的不可达分支，同时完整原28规则分类保持不变。

## 目标接口与剩余源码

后续目标尚未实现：

```text
Omega(w), Num2(mode), metadata(w,z,t), empty(z),
successor(A,z), Term(w,z,b,t), FormulaCode(w,n,A,b)
  ⊢ Run3(w,mode,z,t,n,q)
      ↔ instantiated(w,z,b,A,t,n,q)
```

该接口须覆盖全部内部合法公式码和候选输出，实际R/S在对象EX中构造／消去，并提供源推导、原核传输及nativeZF闭句。完整对象公式归纳不能保留外加IH／历史／Promise。

| 后续顺序 | 必须补齐的对象推导 |
|---|---|
| 1 | 四数值分支逆向重建真实赋值、head和闭轨迹；与本批矩阵soundness组合，取得变量数值双条件 |
| 2 | 消去实际五字段根行EX，推出整条Run1双条件；点输出自然性由参数自然性取得 |
| 3 | 实际InstantiateTop零深度根frame；空绑定参数实际bound提升同码；真实binder提升frame闭包与上下文不变量 |
| 4 | mode2全部合法项与参数列的程序对应，实际输出纤维，消去Promise与列表IH |
| 5 | 全部11公式构造子及内部ALL参数归纳；原ZF集合归纳消去IH，构造／消去真实历史见证 |
| 6 | 接实际InstantiateTop，消去两张码表并返回原nativeZF闭句，再接原模式20／23／25 |

## 已执行的静态核查

可复跑 `.local/check-mode2-source-static.py`。结果写入 `verification/mode2-source-static.json`；本批声明清单及未来Audit片段在 `.local/mode2-source-batch.json`、`.local/mode2-source-audit.txt`。

已检查：禁止缺口词、导入存在性、七模块依赖无环、分隔符与命名空间、UTF-8/LF及行尾；原28分类／五条选定项规则；Num2实际守卫；数值规格和frame不含原接受预言机；原模式20／23／25的bound0项／bound1公式守卫。原验收1607份工作区文件SHA256保持一致，固定上游039c8e132cc19671d73a3933c66b4799d2599dd6且干净。

PPAC.lean、Audit.lean、CheckStep4.lean和所有既有源码均未修改；本批尚未接入全仓证明入口。71声明未经过Lean解析／类型检查、公理足迹、trust=0或全仓构建；静态核查不构成形式化验收。mode2完整操作和最终内部Con状态仍为未证明。
