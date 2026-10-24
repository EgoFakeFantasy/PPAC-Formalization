# mode2 全内部公式与实际 InstantiateTop 验收（2026-10-24）

本批完成原 mode2 的全内部合法纯项纤维、完整参数列表、四原子和全部11种公式构造子递归正确性。原 ZF 集合归纳消去公式 IH；实际历史与 binder 见证在对象 EX 内消去。完整运行已连接既有实际 InstantiateTop 判断，两张实际码表由原对象存在性构造并消去。共享 quotation／Bool、剩余证明／理论节点、专用 Proof_ZF/U、内部编译／数学解释和最终内部 Con 仍未完成。

## 对象背景及最终目标

纯等号／成员语言；背景为原 nativeZF，完整 Separation／Collection，不添加对象 Choice。最终目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

该内部 Con 规格要求专用 Proof_T 覆盖原六规则／27逻辑模式、完整理论模式与全部内部 ω 证明码；这些后续构造与最终蕴含尚未证明。宿主 Consistent、语义模型或构建成功均不替代最终原核推导。

## 全内部推导链

InstantiateFrameTermFiber 由已证明的原 Run1／独立项程序对应及既有对象程序有类型唯一输出，推出原 Run1 的有类型唯一纤维和 term Promise。InstantiateFrameArguments 使用真实 Num2，即 SmallModeArgumentFieldCompletion 的固定模式2实例，消去 term Promise 和列表 IH，得到任意内部长度合法参数列表的 Run2／字段程序双条件。guarded 列表接口将源列表类型保留在结论内部，不要求调用方提供归纳假设。

InstantiateFrameAtomicAgreement／Existing／TypedAtomic／Atomic 从实际项与列表对应推出实际 term/pair agreement、成员／相等及两常量情况；使用 Num2 的原全 Run3 分派，原子端点不假设 agreement、参数对结构或字段见证。原独立程序 AST 保持不变。

InstantiateUniformInductionSyntax 构造对象 ALL10，量化所有变化参数 mode、depth、P、a、b、c、e、R、S、候选输出 q。correctAt 的内容是实际 frame、合法源公式条件下的 Run3／独立执行双条件，属于归纳命题，不作为接受程序定义。InstantiateUniformInductionRules 在实际当前 frame 和已验收的真实 mode2 binder 提升 frame 上实例化 IH，并由真实历史图推出内部读取 agreement。

InstantiateBinderReadAtLift／Advance／CaseBridge／Program 使用实际 source/target 后继与完整 coded mixed lifting；深度后继、两张提升表和历史见证均由原对象存在性取得并消去，P 保持原码。量词分派采用真 Num2。InstantiateFullFormulaProgram 以原四原子、否定、四种二元联结词及两量词合成全部11构造子。该中间步具有显式统一 IH，未把它直接当成最终定理。

InstantiateFormulaCorrectnessPoint 构造并消去真实历史图，再引入全部对象 ALL10。InstantiateFormulaCorrectnessInduction 使用原完整 Separation、Foundation 和对象传递覆盖导出的 SetInduction.all_holds 消去公式 IH。最终覆盖全部内部合法公式码、任意内部深度与候选输出，不限制为宿主可报价的标准码，不假设内部 ω 外部标准。

完整公式执行端点只有 Ω、实际 frame 和源 FormulaCode；不要求 IH、Promise 或历史图。另提供真实历史图下的完整程序端点及已消去 IH 的历史存在／agreement 定理。

## 实际 InstantiateTop 端点

InstantiateTopFormula 从原 instantiateCoded(w,z,b,A,P,R,S) 与 empty(z) 得到实际根 frame；参数／深度自然性由真实环境推出。InstantiateTopFormulaOperation 将完整公式执行对应接上既有 SyntaxTopFormulaCodes.instantiate_at_codes。原对象存在性构造两张码表，在对象 EX2 中消去，再由既有 InstantiateTop 源类型定理将源类型守卫移入最终结论：

```text
Ω(w), Num2(mode), empty(z), instantiateInput(w,z,b,A,P)
  ⊢ [FormulaCode(w,n,A,b) ∧ Run3(w,mode,z,P,n,q)]
       ↔ instantiated(w,z,b,A,P,n,q)
```

instantiateInput 是原环境入口：参数 P 是目标纯项，A 是 z 的实际后继。这里目标绑定界为空，正是纯 EqMem 原 mode2 调用所需的闭绑定参数范围；不声称任意带绑定变量参数都在原 binder 保持原码。上述端点不含元数据、frame、码表 R/S、历史、IH、Promise 或候选自然性前提。实际入口参数类型仍是明确对象前提；本批不声称未加源类型守卫的无效输入拒绝，也不声称整个原宿主 quotation／Bool checker 已对应。

ObjectInstantiateFormula 提供23组源／core／native闭句，经 TheoryTransport.sentence 与 ZFReplay.replay 返回原 FirstOrder.Derives nativeZF []。CheckStep4 含展开的完整公式及实际 guarded InstantiateTop 契约。此前全部 PPAC 证明和原接受／程序／类型／码表 AST 均保持 Git 字节一致；15个既有 mode1 证明文件的来源 SHA256 另由独立回读核对，本批只新增 mode2 证明，不改写旧证明。

## 实际验收

| 验收项 | 结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 18／161／23组 |
| 定向全公式归纳 | 1444项任务，通过 |
| 定向实际InstantiateTop | 1446项任务，通过 |
| 定向native闭句 | 1447项任务，通过 |
| 全仓构建 | 1815项任务，通过 |
| 声明审计 | 19381：402无公理、18979允许依赖；零警告 |
| 检查命令 | 9条全部退出0，含5个trust=0入口 |
| 独立工作区哈希 | 1650份一致 |
| 精确core/native足迹 | 2253对一致 |
| Internal显式覆盖 | 17037项 |
| 上游及锁文件 | 039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core证书依赖恰为propext、Classical.choice、Quot.sound；native侧另含上游锁定的七项证书依赖。未增加对象公理、未改变信任基线，未抽取宿主选择数据。

证据：verification/mode2-formula-readback.json、summary.json、commands.json；.local/mode2-{full-formula,actual-top-formula,formula-native}-directed.log、mode2-formula-full-verify.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点69fc4cf091bed9d92bf95b7efc180a1e55e511bb；提交后回读记录accepted_commit。

本轮开始实测 C 盘恢复约16.5GiB，原空间障碍已解除，因而恢复了完整串行编译。保留本批实际使用的生成／回读脚本、证明证据和编译缓存；没有新增废弃探针或需终止的失效编译进程，也未清理其他项目或应用。Agent广场本轮进场连接失败，写回状态须待服务恢复。

## 后续面向最终目标的工程表

| 顺序 | 实现工作 | 对象验收边界 |
|---|---|---|
| 1 | 原mode2调用的逻辑节点与其余27模式 | 原准确arity／头／查询／所有赋值搜索界，使用本批真实InstantiateTop；独立局部接受与数学规格双条件 |
| 2 | 共享原quotation／Bool桥 | 纯EqMem类型和操作到原共享语言checker的准确对应，核查语言、参数与上下文，避免仅有限重放或外部标准码 |
| 3 | 完整ZF/U理论模式与专用内部Proof | 完整Separation／Collection、原六规则／27模式及全部内部ω证明码；保持原接受定义，不能用结论充当checker |
| 4 | 内部证书转换及数学解释 | 对象核内检查／编译正确性、原源推导传输、目标ZF、PP、ACwo、¬AC解释与相关构造 |
| 5 | 最终内部Con蕴含 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，仍未证明 |
