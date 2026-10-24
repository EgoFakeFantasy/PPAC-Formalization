# mode2 真实 binder 框架闭包验收（2026-10-24）

本批完成原 mode2 实际完整码表 binder 提升下的框架闭包。原始参数 P 保持不变；独立的源／目标后继在对象推导内对齐；原变量码、旧字段值与实际两层四重提升见证全部在对象 EX 内消去。mode2 完整公式、实际 InstantiateTop 完整操作、Proof_ZF/U、内部解释和最终内部 Con 蕴含仍未证明。

## 对象背景与最终目标

纯等号／成员语言；原 nativeZF 背景，保留完整 Separation／Collection，不添加对象 Choice。最终仍须得到：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

要求覆盖全部内部 ω 证明码、原六规则与27逻辑模式。宿主构造、模型语义及构建成功不替代该目标。

## 实际对象推导

InstantiateBinderGeometry 使用原外延性后继唯一性对齐实际独立后继。旧框架规定 source a=succ(depth)、target c=depth、free e=b。真实 lifted 给出 A=succ(a)、C=succ(c)，给定深度后继 D=succ(depth)，对象唯一性分别推出 a=D、C=D，再用对象等号替换得到 A=succ(D)。没有预先假设源／目标后继相同。

InstantiateBinderVariablePoint 的 preserved 分支把原数值输出原变量与实际 bound 后继重命名对应。point 分支先对齐新索引与新深度，再使用已验收的闭参数实际重命名保持：renamed(P,q)↔q=P。旧字段值 t=P 通过对象等号替换进入真实重命名判断，未假设一般参数提升不变。

InstantiateBinderVariable 对原源作用域 i∈a 和 a=succ(depth) 应用原插入集成员分解，得到 i∈depth 或 i=depth，覆盖全部合法内部旧 bound 索引。深度以内分支由旧独立 valueSpec 推出原变量码；阈值点由旧规格推出 t=P，分别接上述协变证明。free 分支的旧值严格使用 mode2 的恒等数值关系，通过实际 free 恒等图及变量码唯一性证明；不复用 mode1 的 freeValue 行为。

InstantiateFrameLiftPoint／Values 使用原 SyntaxCodedMixedBinderFields.zero_iff、bound_iff、free_iff，证明新 bound0、旧 bound 后继及旧 free 的实际列表字段兼容。真实旧变量码与旧字段值分别由既有对象存在性定理取得，在两个对象 EX 内消去，未留作框架端点前提。

InstantiateFrameLiftCompatibility 在全部内部候选索引／变量码／输出上作对象 ALL3，使用原内部自然数零／前驱分解覆盖新源作用域，继而合成两类变量兼容性。新元数据、原闭参数、真实输出 termLists 与新上下文几何共同构成新 frame。

InstantiateOperationFrameBinder.lifted 消去实际 coded lifting 的四个见证，再消去内部 mixed lifting 的另四个见证，最终原对象接口为：

```text
Ω(w), frame(w,mode,depth,P,a,b,c,e,R,S), succ(D,depth),
  actualLift(w,R,S,a,b,c,e,A,C,K,H)
⊢ frame(w,mode,D,P,A,b,C,e,K,H)
```

端点只有上述四个对象前提，不要求 U/V/head、旧变量码／字段值、候选自然性、历史、IH、Promise 或任意语义模型。A/C 与 K/H 均为实际提升关系中的对象变量；P 在结论保持原码。前批实际 InstantiateTop 零深度环境已给出旧根 frame，本批证明其真实 binder 闭包。

ObjectInstantiateBinder 提供12组源／core／native闭句，经 TheoryTransport.sentence 与 ZFReplay.replay 返回原 FirstOrder.Derives nativeZF []。CheckStep4 包含每组闭句及展开的最终四前提接口。未修改原接受定义、独立值规格或此前 PPAC 证明文件。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 8／65／12组 |
| 定向 binder 构建 | 1324项任务，通过，零警告 |
| 定向 native 闭句构建 | 1325项任务，通过 |
| 全仓构建 | 1797项任务，通过 |
| 声明审计 | 19220：402无公理、18818允许依赖；零警告 |
| 检查命令 | 9条全部退出0，含5个trust=0入口 |
| 独立工作区哈希 | 1632份一致 |
| 精确core/native足迹 | 2230对一致 |
| Internal显式覆盖 | 16876项 |
| 上游及锁文件 | 039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core证书依赖恰为propext、Classical.choice、Quot.sound；native侧另含锁定的七项上游证书依赖。未增加对象公理或修改信任基线，未从类型层抽取选择数据。

证据：verification/mode2-binder-readback.json、summary.json、commands.json；.local/mode2-binder-directed.log、mode2-binder-native-directed.log、mode2-binder-full-verify.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点7ec664ea4ee8e3b4f6fe42c6c72e213ff13d7162；提交后回读记录accepted_commit。

本轮继续遵守用户清理范围：只清理本任务已被成功日志替代的失败调试日志，保留实际源码、证据、生成／回读工具与编译缓存。此前已清理247个无用临时文件和一个合并检查副本，无失效进程。本轮C盘可用空间曾在约4至21MiB之间波动；用户回复“释放后通知你”尚不是已完成5GiB释放的确认。没有清理其他项目或应用。

## 后续实现表

| 顺序 | 实现 | 对象验收要求 |
|---|---|---|
| 1 | mode2任意深度项纤维和完整参数列表 | 从实际Run1／独立程序推出有类型唯一纤维；实际Run2与字段程序对应，消去term Promise及列表IH，使用真实Num2 |
| 2 | mode2四原子及全部公式构造子 | 真Num2展开、真实历史、独立source/target上下文及本批真实binder闭包；对象ALL10和原ZF集合归纳消去IH |
| 3 | 实际InstantiateTop完整操作 | 原根与完整公式合成；两张实际码表由对象存在性构造并消去，源类型在结论内部 |
| 4 | 原逻辑／理论节点与内部Proof转换 | 六规则／27模式、完整Separation／Collection、全部内部ω；检查与编译／源核传输正确性 |
| 5 | 内部数学解释与最终Con | 原核中目标ZF、PP、ACwo、¬AC解释及Derives nativeZF [] (Con_ZF→Con_target)，保持未证明直到完成 |
