# 全内部公式复合与14参数归纳关闭验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 3493b7c7842ac669fb9b6c70ae89201f9e16cad0。
F2.3c 已完成：全 11 原构造的公式复合、14 内部参数成员归纳关闭，以及存在实际中间公式码的完整双条件。
恒等与复合联合门禁已通过；原核加强规则兼容、捕获规避替换、专用 ProofZF/U、内部编译/解释和最终内部 Con 仍未完成。

## 固定对象合同

对象语言仍为原 YesMetaZFC 纯等词/成员语言；最终证书使用原 FirstOrder.Derives。
背景仍为 nativeZF 的完整 Collection 呈现，源完整 Replacement 通过既有原核传输与重放接入。
最终目标仍为 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target 为 ZF+PP+ACwo+¬AC。
内部 Con 规格遍历全部内部 ω 证明码，保留原六规则、27 模式及完整 Separation/Collection。
本批不新增对象 AC、标准 ω、外部良基、不可达、模型存在或 Con(nativeZF) 前提。
专用 ProofZF/U 完整纯 AST 和最终 Con 原核主句仍未实现。

记 CodedCompose(w,a,c,e,R,T,K) 为先 R:a→c 后 T:c→e 的实际自然映射码复合。
给定 Ω(w) 及 bound/free 两组实际复合：

```
CodedCompose(w,a,c,e,R,T,K)
CodedCompose(w,b,d,f,S,U,L),
```

对所有内部候选 n,v，原核证明：

```
RenameFormula(w,K,L,a,b,e,f,n,v)
  ↔ ∃q (RenameFormula(w,R,S,a,b,c,d,n,q) ∧
         RenameFormula(w,T,U,c,d,e,f,q,v)).
```

q 是对象存在量词见证，非宿主选择的字段或标准 AST。
六个作用域及六个映射码均显式保留；允许非单射、空域及内部非标准码。
没有附加源/目标自然性或额外 FormulaCode 前提；这些由真实判断及合法映射码恢复。

## 实际目标字段与四原子

已知源原构造及正式 Rename，原标签筛选实际取得同种目标构造字段。
单子、二元、等式、成员式分别使用对象 1/2/2/3 重存在量词；假/真无字段。
先取得中间 q 的实际字段，再取得最终 v 的实际字段。
已有两端精确律用同一个实际 q 构造恢复两阶段子判断，原同码字段单射负责对齐。
没有抽取 Lean 内部字段数组或限制外部标准深度。

四原子完整复合已证明：假/真使用根码相等；等式与成员式使用已证实际图项复合。
成员式显式传递 z=z1 与 z1=z2，保留原 ZeroScalar(z) 和结果符号相等。
两组 CodedCompose 内部消去为六幅实际图，保留原 Encoded 图/码对应及独立目标范围。
关键证书：native_targetNegation/targetForall/targetExists/targetBinary/targetEquality/targetMembership，
native_nullary/equalityFields/membershipFields/equality/membership/atomic。

## 14个参数确实在对象语言内部量化

Property(w,n) 是有限纯公式，内部全称量化 R,S,T,U,K,L,a,b,c,d,e,f,q,v。
内容为两组 CodedCompose 及两次 RenameFormula 推出结果 RenameFormula。
Earlier(w,n) 内部量化 x∈w 且 x∈n 时的同一个 Property(w,x)。
外部只索引固定有限公式/模式，没有以外部公式深度代替内部码范围。

否定及四二元用实际源子码的严格成员界调用同一 Property。
两个量词实际取得 A,C,Lr 及 D,E,Lt；原后继唯一性证明 C=D，并传输第二体判断的源范围。
原复合 K 实际取得 A→E 的提升码 Lk；已证提升/复合相容给出 Lr、Lt、Lk 的实际 CodedCompose。
在这个真实提升状态下实例化 Property；free 码 S,U,L 及范围 b,d,f 保持。
关键证书：native_advancedCompose/checkCompose、native_negationFields/forallFields/existsFields/binaryFields，
native_negation/forall/exists/binary、native_codeStep/diagramStep/mapCodeStep。

原 Foundation 与 Property 否定矩阵的完整 Separation 关闭全内部 ω 上的成员归纳。
Below 的蕴含守卫显式转为 Earlier 的合取守卫；最终定理没有 Earlier、图解码或历史存在前提。
关键证书：native_propertyStep/progressive/allProperties/naturalProperty/forward。

## 实例化工程与反向分解

14 层连环 allE 直接实例化大矩阵触发了 whnf 展开超时。
SyntaxBinderBlock.eliminate 逐个使用原 allE，证明有限全称块可一次重命名实例化，保持旧变量固定。
该引理只构造原 Source.Derives 证书；Property 本身仍含全部 14 个对象全称量词，没有增加规则或公理。
改用该证明后不再提高 maxHeartbeats，相关模块及完整验收均通过。

反向分解先从结果恢复源 FormulaCode，实际取得第一阶段中间码 q，再实际取得第二阶段输出 v'。
正向公式复合给复合结果 n→v'；既有输出唯一性证明 v'=v，再用原等词替换修正第二阶段输出。
因此取得完整存在中间公式码双条件，包含任意内部候选的正/负识别范围。
关键证书：native_factor/collapse/composeIff。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py` 退出 0。
源规则/理论锁、版本、全仓 --no-cache --wfail 构建及五个 trust=0 入口，共九命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 全仓构建 | 813 jobs，退出 0 |
| 声明审计 | 9172 项；294 项无公理依赖，8878 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 14 模块、221 项，全覆盖 |
| Internal 累计显式声明 | 6857 项，无漏审 |
| 新增 Source/sourceZF核/nativeZF核模式 | 35 对核心/native 精确足迹 |
| 累计模式 | 895 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 782 份，差异 0 |
| 九命令/五 trust=0 | 全部退出 0 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书依赖精确为 propext、Classical.choice、Quot.sound；native 证书另含既定七项原证书。
这是记录中的 Lean 可信基依赖，没有新增对象公理；原 choice 额外证书仍单独限域。
CheckStep4 新增 35 个原核模式实例；全部新声明纳入显式审计。
独立回读为忽略目录 verification/formula-compose-readback.json；日志和生成辅助仅留本地。
原 OpenAI 完整构建/Comparator 本批未运行；未推送。

## 后续 agent 工程表

| 单元 | 实现职责 | 原核验收条件 | 状态 |
|---|---|---|---|
| F2.3c | 全 11 构造、14 内部参数 Property、原成员归纳、实际中间码分解 | 无 Earlier 的全内部复合及两阶段双条件 | 完成 |
| F2.4a | 实际 free 头槽位移图 i↦Succ(i)，源范围 b、目标范围 Succ(b) | 全边双条件、实际唯一自然映射码，覆盖 b=0 | 待完成 |
| F2.4b | bound 恒等码与上述 free 位移码，全部构造/真实 binder | 精确 WeakenFree 链接、存在唯一与原核加强规则兼容 | 待完成 |
| S | 实际内部替换序列、全部 bound/free 范围 | 捕获规避替换存在唯一、类型与代数，覆盖原替换/绑定关系 | 待完成 |
| 5 | 原六规则/27 模式和完整理论公理码 | 专用 ProofZF/U 纯 AST 与任意内部证明码正确性、编译传输 | 待完成 |
| 6 | 原目标公理、全内部解释与一致性公式 | 原 nativeZF 内最终 Con 蕴含的 Derives | 待完成 |

已核对原 Core.free_strengthening 的实际方向：由新增 free 头槽后的 formula.weakenFree 推导原 formula。
所需语法链接沿原公式到其弱化式的上行位移 b→Succ(b) 构造，原规则再删除该未用 fresh 头槽。
恒等/复合联合门禁已为 True；完整 FormulaRename 总门禁保留为 False，直到上述原核规则兼容完成。
捕获规避替换、ProofZF/U 和最终 Con 继续为 False，不能据本批形式化完成宣称最终主句完成。
