# 实际提升参数与空原子唯一输出验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 f01621c51f74dcc6b202db984382dfd2a02fa38e。
本批完成 F1e.3a（输出合同、实际量词提升参数对齐）和 F1e.3b 的两个空原子模式。
属于实际对象推导；完整公式重命名、替换、ProofZF/U 与最终内部 Con 主句尚未完成。

## 固定背景与验收层次

对象语言仍为原 YesMetaZFC 的单排序纯等词/成员语言；B 仍为原 nativeZF（Collection 呈现）。
不增 AC、不可达或 Con(B) 前提；最终目标仍是 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)。
内部 Con 遍历全部内部 ω 证明码，检查原六规则、27 逻辑模式及完整 Separation/Collection。
本批所有闭句均有 Source.SetLanguage.ZF、经 TheoryTransport 的 sourceZF 原核，以及经 ZFReplay 的 nativeZF 原核推导。
没有用宿主 Consistent、语义模型或编译成功代替这些对象证明。

## 实际输出与内部归纳合同

SyntaxRenameOutputSyntax.input(w,R,S,a,b,c,d,n) 为
FormulaCode(w,n,a,b) ∧ (MapCode(w,a,c,R) ∧ MapCode(w,b,d,S))。
MapCode 实际绑定完整图、原源长度和独立目标范围，允许非单射。
Fiber 是实际对象句子 ∃q(RenameFormula(...,n,q) ∧ ∀t(RenameFormula(...,n,t)→t=q))。
唯一性量化全部内部候选 t，没有只比较外部标准码。

Property(w,n) := ∀R∀S∀a∀b∀c∀d (Input→Fiber)。
Earlier(w,n) := ∀x((x∈w ∧ x∈n)→Property(w,x))。
六个内部参数同时量化，为量词分支更换两个后继作用域及提升码留下正确归纳接口。
property_at/earlier_at 是对给定对象前提的真实实例化；本批没有证明任意 n 的 Property。
输入/输出自然性、从实际 Fiber 取输出存在、由实际判断与唯一性引入 Fiber 均有闭句证书。
关键证书：native_renamedInput、native_renamedNatural、native_inputNatural、
native_existsFromFiber、native_existsFromRenamed、native_fiberIntro、native_propertyAt、native_earlierAt。

## 实际提升参数对齐

任意实际 CodedLift(w,a,c,R,u,v,L) 恢复 Succ(u,a) 和 Succ(v,c)。
对同一原码 R 的两个实际提升候选 (u,v,L)、(U,V,M)，
原集合插入唯一性给 u=U、v=V；对齐作用域后，实际提升码唯一性给 L=M。
不能从有限列表码本身推断目标范围相等；这里范围相等来自两个真实后继。

在 Ω(w) 和一个给定实际 CodedLift 下，原核证明
AdvancedRename(w,x,R,S,a,b,c,d,q) ↔ RenameFormula(w,L,S,u,b,v,d,x,q)。
正向正式消去任意候选提升的三个存在见证，逐参数作对象等词替换；反向使用给定实际提升作存在引入。
free 码 S 及 free 作用域 b、d 保持不变。
关键证书：native_liftSuccessors、native_liftParameters、native_advancedAtLift。

## 原子分支筛选及两个实际唯一输出

给定原源构造的标签 0、1、2、3，完整 11 类重命名 Cases 正式筛回对应原子分支。
错误标签的 nullary、membership、equality、negation、四个二元和两个量词分支，
均由原构造标签互斥排除；对象存在见证由原 exE 消去。
外部 Fin 4 只索引四个原固定标签，全部码、作用域、图及输出仍是内部对象参数。
关键证书：native_atomicFilter。
这条筛选本身不提供 membership/equality 的实际输出。

两个空原子分别为原 falsum 和 verum（外部 Bool 只索引这两个固定模式）。
在 Ω、Input 和给定原空构造码 n 下，实际构造 RenameFormula(...,n,n)。
两端的作用域来自两个真实 MapCode；目标 FormulaCode 由原空构造类型双条件取得。
两个实际映射图通过对象 exE 取得，再组成无历史的完整递归判据；原递归双条件返回真实 RenameFormula。

对任意内部候选 q，RenameFormula(...,n,q) 推出 q=n。
证明正式取得两个解码图，对完整 Cases 筛选，得到同标签目标空构造，再用原构造唯一性。
于是实际 ∃! 输出纤维成立。进一步由六次对象全称引入，证明
Ω(w) → Constructor_0_or_1(w,n) → Property(w,n)。
此处 Property 的六个内部参数已经全部量化，并无 Earlier 前提；这是两个实际原子基础情形。
关键证书：native_nullaryLocal、native_nullarySelf、native_nullaryUnique、
native_nullaryFiber、native_nullaryAllParameters。

## 实际验收

运行 C:/Python314/python.exe -X utf8 scripts/verify.py，退出 0。
两份原源规则/理论锁、版本、全仓 wfail 构建和五个 trust=0 入口共九条命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 742 jobs，退出 0 |
| 声明审计 | 8067 项；284 项无公理依赖，7783 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 10 模块、123 项，全覆盖 |
| Internal 累计显式声明 | 5752 项，无漏审 |
| 本批闭句模式 | 17 对核心/native 精确足迹 |
| 累计闭句模式 | 708 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 711 份，差异 0 |
| 九命令/五 trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新核心证书精确依赖 propext、Classical.choice、Quot.sound；
native 证书另含原七个固定 ZF 定义证书的既有依赖。
没有新增自定义公理，没有扩大原 choice 额外闭性证书的隔离范围。
Classical.choice 是宿主证明证书依赖，不是新增对象 AC 或内部集合选择函数。
CheckStep4 逐一核验 17 个 native 闭句，并固定 Input、全候选唯一性、Fiber 和 Earlier 的 AST。
独立复核留在忽略目录 verification/rename-output-nullary-readback.json。
原 OpenAI 完整构建/Comparator 本批未运行；生成辅助与日志留本地；未推送。

## 后续工程单元

| 顺序 | 明确对象输入 | 必须交付与验收 |
|---|---|---|
| F1e.3b.2 | 原 membership/equality 构造、真实完整映射图、合法源项 | 实际唯一目标项和原目标构造；恢复同码源字段、对齐任意解码图、保留原零符号；实际唯一输出 Fiber |
| F1e.3c | Earlier(w,n)、七种真实逻辑构造、严格子码成员界 | 普通子式使用同一六参数性质；量词先取得实际 CodedLift，再按本批参数对齐实例化提升后的性质 |
| F1e.4 | 全11类逐分支、原 Foundation 和否定矩阵 Separation | 对内部 ω 关闭成员归纳；消去 Earlier，得到全部合法内部输入的实际唯一输出，再验收单构造精确律 |
| F2/S | 完整实际公式 Rename、任意内部替换序列 | 映射恒等/复合及捕获规避 Subst 的存在唯一、类型与规则兼容 |
| 5–6 | 原六规则/27模式、全 ZF 模式及精确目标公理码 | ProofZF/U、全内部编译正确性与解释；最终原核内部 Con 蕴含 |

本批仅提升量词参数对齐、合同和两个空原子的门禁。
membership/equality 实际输出、逻辑归纳、全输入唯一输出、完整 FormulaRename、替换、ProofZF/U 和最终 Con 均保持 False。
