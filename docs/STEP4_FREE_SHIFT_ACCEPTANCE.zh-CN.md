# 原 free 头槽实际位移图与自然码验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 59bdf2f7761e2cebae68940b4890ec4387326411。
F2.4a 已完成：实际完整位移图、原自然列表码、存在唯一及任意候选识别，覆盖空 free 上下文。
全公式 WeakenFree、原 free_strengthening 兼容、捕获规避替换、ProofZF/U 与最终内部 Con 仍未完成。

## 固定对象合同与原规则方向

对象语言仍为 YesMetaZFC 原纯等词/成员语言，正式证书仍为原 FirstOrder.Derives。
背景仍为 nativeZF 的完整 Collection 呈现；源完整 Replacement 由既有对象互导与原核重放接入。
最终主句保持 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target 为 ZF+PP+ACwo+¬AC。
内部 Con 规格仍遍历全部内部 ω 证明码，保留原六规则、27 模式及完整 Separation/Collection。
专用 ProofZF/U 完整纯 AST、任意内部证明码正确性及最终 Con 原核主句尚未实现。

已逐字核对固定原库：Logic/FirstOrder/Derivation/Core.lean 的 free_strengthening 从
新增 free 头槽后的 formula.weakenFree 推导原上下文中的 formula。
Logic/Syntax.lean 的 Formula.weakenFree 是 Renaming.weakenFree，后者保持 bound 上下文并在 free 头部加入变量。
所以所需上行语法链接是 b→B=Succ(b)，旧索引 i→Succ(i)，fresh 新头槽 0 不被旧变量占用。
本批没有构造 Succ(b)→b 的全域逆映射；空源域 b=0 是合法输入。
此方向核对和索引图本身尚不构成完整 WeakenFree 公式定律或原规则兼容证明。

## 实际纯关系与全内部范围

SyntaxFreeShiftSyntax.matrix 是纯关系 Succ(j,i)。
原通用关系成图接口使用完整 functionOn，包含 entriesOn 和 totalOn，不容许杂项。
ShiftMap(w,b,B,r) 合取实际 Succ(B,b)、原 IndexMap(w,r,b,B) 和完整全边定律。
原核对全部内部候选 i,j 证明：

```
Edge(r,i,j) ↔ (i∈b ∧ Succ(j,i)).
```

图的存在使用原 Replacement：任意内部集合 i 的实际后继存在、且由 Extensionality 唯一。
ω 的内部序数成员界证明 Succ(i)∈Succ(b)，得到独立目标范围 B。
没有用宿主 Nat.succ、宿主函数图或外部标准码归纳代替内部集合关系。

ShiftCode(w,b,B,S) 在对象存在量词中绑定实际图 r，要求原 Encoded(w,r,b,B,S) 和 ShiftMap。
所有 S 都是原自然列表码，保留源长度 b 与独立目标范围 B；同码任意实际解码图都恢复 ShiftMap。
对任何给定实际 Encoded，ShiftCode 精确等价于该图的 ShiftMap。
原核证明实际图和码均唯一；码唯一性保留 Ω(w) 前提。

给定 Ω(w)，有精确合法输入双条件：

```
(∃S ShiftCode(w,b,B,S)) ↔ (b∈w ∧ Succ(B,b)).
```

从 Ω(w) 和 b∈w 还实际构造 B 及其实际唯一位移码纤维，结论没有后继存在前提。
所有存在见证通过原 exE/exI 使用，不抽取 Lean 数据。

## fresh 头槽与空源域

任意 Empty(z) 与 ShiftMap 都推出所有 Edge(r,i,z) 为假；后继非空排除 fresh 零头槽入边。
任意 Empty(b) 与 ShiftMap 都推出所有边不存在；完整 entriesOn 进一步证明 r 实际为空集。
Ω(w) 和 Empty(z) 本身给出 z 的实际后继/唯一位移码状态，不要求额外 z∈w 前提。
因此空 free 上下文的存在、无边和无杂项均有明确原核闭句，未采用非空上下文限制。
不同目标后继候选由原 Insert 唯一性对齐，后续不会把独立后继默认成同一对象。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py` 退出 0。
源规则/理论锁、版本、全仓 --no-cache --wfail 构建及五个 trust=0 入口，共九命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 全仓构建 | 818 jobs，退出 0 |
| 声明审计 | 9316 项；294 项无公理依赖，9022 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 5 模块、144 项，全覆盖 |
| Internal 累计显式声明 | 7001 项，无漏审 |
| 新增 Source/sourceZF核/nativeZF核闭句模式 | 23 对核心/native 精确足迹 |
| 累计模式 | 918 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 787 份，差异 0 |
| 九命令/五 trust=0 | 全部退出 0 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书的精确依赖为 propext、Classical.choice、Quot.sound；native 证书另含既定七项原证书。
这是固定 Lean 可信基足迹，不向对象背景增加 AC、标准 ω、外部良基、不可达、模型存在或一致性假设。
原 choice 额外闭性证书仍单独限域；本批没有扩大该范围或修改原库。
CheckStep4 新增23个原核模式实例；全部144项声明显式审计，新增四个细分门禁为True。
独立回读留在忽略目录 verification/free-shift-readback.json，生成辅助和详细日志仅留本地。
原 OpenAI 完整构建/Comparator 本批未运行；未推送。

## 后续工程表

| 单元 | 实现职责 | 原核验收条件 | 状态 |
|---|---|---|---|
| F2.4a | 实际 free 头槽位移图/原自然码、全部候选和空源域 | 全边双条件、实际唯一纤维、合法输入双条件、fresh零槽排除 | 完成 |
| F2.4b.1 | bound恒等与free位移的实际图码、纯WeakenFree | 任意合法内部公式的实际唯一弱化输出及精确参数识别 | 待完成 |
| F2.4b.2 | 全11构造、bound恒等真实binder提升和同一free位移 | 各构造精确定律及作用域/类型保持 | 待完成 |
| F2.4b.3 | 原weakenFree链接与原加强规则 | 精确原语法操作及内部六规则检查接口中的兼容证明 | 待完成 |
| S | 全内部替换序列、bound/free范围 | 捕获规避替换存在唯一、类型和代数，覆盖替换/绑定规则 | 待完成 |
| 5 | 原六规则/27模式及完整ZF/目标公理码 | ProofZF/U纯AST、任意内部证明码正确性与编译传输 | 待完成 |
| 6 | 内部解释和固定内部Con | 原nativeZF内最终Con蕴含的Derives | 待完成 |

原free_strengthening兼容、完整FormulaRename总门禁、替换、ProofZF/U与最终Con均继续为False。
实际位移图/码的本批验收不能替代后续全公式和完整内部证明码的验收。
