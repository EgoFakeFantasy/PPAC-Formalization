# mode2 变量完整运行与条件项框架验收（2026-10-24）

本批完成原 mode2 的全部变量分支数值双条件、完整 Run1 与独立变量规格的双条件，以及兼容框架前提下全部内部合法纯项的程序／混合项传输。真实根框架、binder 闭包、完整公式操作和最终内部 Con 蕴含尚未证明。先前 source-only 草稿 531ee19 的七个模块现已实际编译修复；旧草稿报告保留为历史记录。

## 对象背景与最终目标

对象语言为纯等号／成员语言；背景为原 nativeZF，保留完整 Separation／Collection，不添加对象 Choice。最终交付仍为：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

Con 覆盖全部内部 ω 证明码、原六规则及 27 逻辑模式。宿主构造、语义模型与构建通过均不替代该目标。

## 实际完成的对象证明

OriginalInstantiateClasses 对原全部 28 个变换规则分类，真实 Num2 选出五条项规则；变量分支为三个 bound 规则及一个 free 规则。OriginalInstantiateDispatch／Positive／Trace 使用原五字段行、真实赋值界、全部应用赋值量词及原闭轨迹，不改写接受判断。

InstantiateVariableValueSyntax 独立规定：bound 索引小于 depth 时输出原变量，等于 depth 时输出参数 P，大于 depth 时输出其前驱 bound 变量；free 变量输出原变量。该规格不含 Run／Trace／程序或实际字段作为接受 oracle。Sound／Complete／Numeric 双向构造和消去实际数值行及轨迹；前驱见证在对象存在量词内消去。

InstantiateVariableRun.run_iff 的最终对象前提只有 Ω、Num2、原 depth/P 自然性元数据及输入变量码。候选输出自然性由规格推出；点分支使用元数据中的 P∈ω。实际根行在对象 EX 中构造、消去，不假设候选自然性、存在根行或标准自然数。

InstantiateOperationFrameSyntax 保留真实 termLists、独立变量兼容关系、闭绑定参数及上下文几何：source=succ(depth)、target=depth、自由上下文相同。closedParameter 通过空绑定纯项推出 free 分支。InstantiateFrameTerm 将全部内部合法纯项的原 Run1 对应到独立项程序及既有 coded mixed substitution；guarded_coded_iff 将源类型守卫置于结论内部。

上述项结果仍以兼容 frame 为前提。实际 InstantiateTop 根 frame 的构造和量词内真实 binder 提升闭包尚未完成，不能从条件项定理推出整个 mode2 正确性。原 binder 增加 depth 而保留 P，故后续须利用参数无绑定变量证明其提升不变，不能假设任意绑定参数在提升下不变。

ObjectInstantiateVariable 提供 14 组源／core／native 闭句，返回原 FirstOrder.Derives nativeZF []；CheckStep4 含展开的完整变量运行与 guarded 条件项契约。完整源规则、原接受 AST、既有程序 AST 与上批证明保持 Git 字节一致。

## 清理及实际验收

用户授权先清理工作区再继续编译。检查未发现失效 Lean／Lake／相关工作区进程；删除 247 个确认无用、未跟踪的 .local 顶层临时文件：113 个一次性脚本、74 个失败／空调试日志、6 个废弃探针、54 个旧生成片段。删除前逐文件校验路径、长度和 SHA256，未递归删除，跳过数为零。逻辑删除 1091989 字节；实测可用空间 103116800→104210432 字节。源码、已验收证据与必要工具及编译缓存保留。

| 验收项 | 实际结果 |
|---|---|
| 本批模块／显式声明／闭句 | 12／145／14组 |
| 全仓构建 | 1784项任务，通过 |
| 声明审计 | 19106：400无公理、18706允许依赖；零警告 |
| 验收命令 | 9条全部退出0，含5个trust=0入口 |
| 独立哈希回读 | 1619份一致 |
| 精确证书足迹 | 2209对一致 |
| Internal显式覆盖 | 16762项 |
| 上游及锁文件 | 固定039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁文件不变 |

core 证书保持 propext／Classical.choice／Quot.sound 精确依赖；native 侧另含锁定的七项上游证书依赖。未增加对象公理或改动信任基线。五个 trust=0 入口通过不表示既有依赖消失。

证据：verification/mode2-variable-readback.json、summary.json、commands.json；清理清单为 .local/workspace-cleanup-20261024-{plan,result}.json。复验命令：`C:/Python314/python.exe -X utf8 scripts/verify.py`，Lean／Lake 串行。后续 C 盘再次耗尽；对本工程生成文件的压缩尝试保持逻辑字节一致，但未验证到额外空间收益，不将其计为清理收益。

## 面向最终对象目标的后续工程表

| 顺序 | 下一实现 | 必须验收的对象交付 |
|---|---|---|
| 1 | 实际 mode2 根与 binder frame | 从实际 InstantiateTop 环境推出 frame；实际独立源／目标后继、真实提升表、闭参数提升不变，全部内部见证在对象 EX 内消去 |
| 2 | mode2 项纤维、列表及完整公式 | 复用四小模式展开，全部公式构造子；真实历史与对象集合归纳消去 IH，最终接实际 InstantiateTop |
| 3 | 原27逻辑模式、理论实例及剩余证明节点 | 原准确 arity／头／查询／赋值界；完整 ZF/U 公理实例 |
| 4 | 内部 Proof_ZF／Proof_U 与证书转换 | 覆盖全部内部ω、原六规则／27模式及完整 Separation／Collection，检查与编译正确性 |
| 5 | 内部数学解释与目标理论 | 原核中解释设施及 ZF、PP、ACwo、¬AC 的推导 |
| 6 | 最终内部 Con 蕴含 | 原核 Derives nativeZF [] (Con_ZF→Con_target)，保持未证明直到完整验收 |
