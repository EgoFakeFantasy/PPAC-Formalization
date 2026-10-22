# 四类原子实际唯一输出验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 7dfcfdcf9ad2469724ff2c365c080323fb377db4。
F1e.3b 已完成：成员式、等式的实际唯一输出，以及四类原子的共同内部六参数归纳基础情形。
此前两个空原子及量词提升参数对齐的验收保持。
完整公式重命名、捕获规避替换、ProofZF/U 及最终内部 Con 主句仍未完成。

## 对象合同与原核证书

对象语言仍是原 YesMetaZFC 的单排序纯等词/成员语言，背景仍为原 nativeZF 的纯语言像。
不加入 AC、不可达或 Con(nativeZF)；最终要求原 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)。
内部 Con 检查全部内部 ω 证明码，保留原六规则、27 逻辑模式及完整 Separation/Collection。
本批使用原19条源规则构造推导，再经 TheoryTransport 和 ZFReplay 取得真实原核 Derives。
宿主一致性、语义模型、AST 或编译本身均不替代这些对象推导。

Input(w,R,S,a,b,c,d,n) 仍为 FormulaCode(w,n,a,b) ∧ (MapCode(w,a,c,R) ∧ MapCode(w,b,d,S))。
Fiber 仍为实际 ∃q(RenameFormula(...,n,q) ∧ ∀t(RenameFormula(...,n,t)→t=q))。
Property(w,n) 仍内部量化 R,S,a,b,c,d，正文为 Input→Fiber；唯一性遍历全部内部候选 t。
所有映射图允许非单射，源长度及独立目标范围均保留。

## 任意候选解码图的精确对齐

给定 Encoded(w,r,a,c,R) 和 Encoded(w,s,b,d,S)，
原核证明 HistoryFreeLocal(w,R,S,a,b,c,d,n,q) ↔ Cases(w,R,S,r,s,a,b,c,d,n,q)。
正向以原 exE 取得任意候选解码图；同码的完整实际图唯一性给出候选图与 r、s 相等。
随后在完整 Cases 公式中分别作实际图参数的对象等词替换。
反向使用给定两个实际图作对象存在引入。
这条双条件本身不要求 n 或 q 是外部标准自然数，也不从列表码推断目标范围。

对 RenameFormula 使用已验收完整递归双条件，得到给定实际图下的全部 Cases。
再按给定原标签筛出对应原子分支；目标类型和实际 Cases 也可反向接回正式 RenameFormula 判断。
关键原核闭句：native_graphCases、native_casesFromJudgment、native_atomicFromJudgment、native_introFromCases。

## 成员式与等式的实际构造

给定原源构造和 Input，用原 FormulaCode 类型双条件取得合法源项。
对两个项分别使用实际项重命名存在定理；两个输出 X、Y 均由对象存在规则取得，没有宿主选择抽取。
目标项类型及自然性由项重命名保持定理给出。
原构造器实际生成等式码 Constructor(2,3,[X,Y]) 或成员式码 Constructor(3,2,[z,X,Y])。

成员式的 z 是原源码中的同一个零符号码。
其原 ZeroScalar 类型及内部自然性从源 FormulaCode 得到；构造目标时直接保留 z，未另选新符号。
原目标构造的完整类型双条件给出 FormulaCode(w,q,c,d)。
实际源/目标字段、项关系和两幅完整图组成无历史 Cases，再由完整递归判据反向得到真实 RenameFormula。
所有项、图、源码和目标码的存在见证最终都通过原 exE 消去。
关键原核闭句：native_equalAtOutputs、native_memberAtOutputs、native_equalExistsAtGraphs、native_memberExistsAtGraphs。

## 对所有内部候选的唯一性与实际纤维

两个候选原子重命名分支可能绑定不同源字段。
原同码字段单射先恢复源字段相等；对第二候选项关系作源项参数的对象等词替换。
项重命名唯一性给出两个对应目标项相等；目标原子字段替换后，原构造唯一性给出两个输出码相等。
成员式同时恢复同源码的零符号字段相等，保留全部原字段位置。
该论证不需要映射单射，也不只检查外部标准样本。

原四/五个对象存在量词正式消去，故完整原子分支对任意内部输出候选唯一。
对正式 RenameFormula 候选，先对齐所有候选解码图，再筛选原子分支并调用上述唯一性。
将实际输出存在与全候选唯一性结合，得到真实 Fiber。
之后消去两个 MapCode 的实际图见证，Fiber 仅保留 Ω、Input 和给定源原构造前提。
关键原核闭句：native_equalDataUnique、native_memberDataUnique、native_equalRelationUnique、native_memberRelationUnique、
native_equalUniqueAtGraphs、native_memberUniqueAtGraphs、native_equalFiberAtGraphs、native_memberFiberAtGraphs、native_equalFiber、native_memberFiber。

## 四类原子的共同内部基础情形

对成员式和等式，六次对象全称引入已经证明给定原构造下的完整 Property(w,n)。
其内部变量 R,S,a,b,c,d 均可为非标准内部对象；非法输入由 Input 前件处理。
再从原 SyntaxAtomSyntax.membership/equality 以对象 exE 取得真实字段，消去给定源字段前提。
与此前假/真两个模式一起，得到：

Ω(w) → Atomic(w,a,b,n) → Property(w,n)。

这里 Atomic 是原四类纯语言原子式类型公式，不是新公理或宿主 Prop 分类。
由 Property 正式实例化任意 R,S,a,b,c,d，得到 Ω、Input、Atomic 下的实际 Fiber 和输出存在。
没有 Earlier 归纳假设残留；这是全部四类原子的实际归纳基础情形。
关键原核闭句：native_equalAllParameters、native_memberAllParameters、native_equalBaseProperty、native_memberBaseProperty、
native_atomicProperty、native_atomicFiber、native_atomicExists。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py 退出 0。
两份源规则/理论锁、版本、全仓 wfail 构建及五个 trust=0 入口共九条命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 749 jobs，退出 0 |
| 声明审计 | 8201 项；284 项无公理依赖，7917 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 7 模块、134 项，全覆盖 |
| Internal 累计显式声明 | 5886 项，无漏审 |
| 新增闭句模式 | 25 对核心/native 精确足迹 |
| 累计闭句模式 | 733 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 718 份，差异 0 |
| 九命令/五 trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新核心证书精确依赖 propext、Classical.choice、Quot.sound；native 证书另含原七个固定 ZF 定义证书的既有依赖。
没有新增自定义公理，没有扩大原 choice 额外闭性证书的隔离范围。
Classical.choice 是宿主证明证书依赖，没有据此向对象 ZF 加 AC 或抽取内部集合选择函数。
CheckStep4 逐一核验全部25类 native 闭句，并以 rfl 固定源/目标项位置和成员式中同一个零符号字段。
独立复核留在忽略目录 verification/rename-atomic-output-readback.json。
本批未运行原 OpenAI 完整构建/Comparator；生成辅助和日志留本地；未推送。

## 下一关及完成边界

| 工作单元 | 对象输入与实现方向 | 必须验收的原核结论 |
|---|---|---|
| F1e.3c.0 | 标签4–10的原源构造及完整11类 Cases | 排除错误标签并恢复同码源子式字段；普通子式与量词字段位置精确保持 |
| F1e.3c.1 | Earlier、否定/四二元原构造及严格子码界 | 对每个内部子码实例化完整六参数 Property，实际构造唯一目标逻辑码 |
| F1e.3c.2 | Earlier、两个量词构造、真实后继与实际 CodedLift | 取得提升码，在提升后作用域实例化同一性质；对齐任意候选提升；free参数保持；实际唯一量词输出 |
| F1e.4 | 全11类推进、原 Foundation 与否定矩阵 Separation | 关闭内部ω成员归纳，消去 Earlier；全部合法内部输入实际∃!及单构造精确律 |
| F2/S/5/6 | 完整实际 Rename、内部替换序列、原核规则/模式 | 映射代数、捕获规避替换、ProofZF/U、全内部编译/解释及最终原核 Con 蕴含 |

四类原子实际唯一输出及其全内部参数性质提升为 True。
七类逻辑推进、归纳关闭、全部合法公式唯一输出、完整 FormulaRename、替换、ProofZF/U 和最终内部 Con 仍保持 False。
