# 真实 binder 提升与实际图/自然码复合相容验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 975e0f56225add5368d3e6fbbdb9f72daebda952。
F2.3b.2 已完成：真实提升与完整图、原自然码的复合相容，且均有任意候选的识别双条件。
独立取得的中间后继由原后继唯一性对齐；所有中间集合和图由对象存在量词取得。
全内部公式复合、原核规则兼容、捕获规避替换、ProofZF/U、内部编译/解释与最终内部 Con 仍未完成。

## 固定对象背景与目标

对象语言仍为原 YesMetaZFC 纯等词/成员语言，推导关系仍为原 FirstOrder.Derives。
背景保持 nativeZF 的完整 Collection 呈现；源完整 Replacement 通过既有原核理论传输和重放接入。
最终目标仍为 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target 为 ZF+PP+ACwo+¬AC。
内部 Con 规格遍历全部内部 ω 证明码，保留原六规则、27 模式及完整 Separation/Collection。
专用 ProofZF/U 完整纯 AST 和最终 Con 原核主句仍未实现；本批没有提高这些门禁。
没有新增对象 AC、外部标准 ω、外部良基、不可达、模型存在或 Con(nativeZF) 前提。

## 零边与实际中间后继

设 Composed(w,r,t,a,c,e,g)；先 r:a→c 后 t:c→e。
三个实际后继范围为 A,C,E；输入实际提升为 Lifted(w,r,a,c,A,C,ρ) 和 Lifted(w,t,c,e,C,E,τ)。

- 零边：Empty(i) 与 Empty(j) 时，以内部 i 本身作为中间点，原完整提升边律给出 ρ(i,i) 和 τ(i,j)。
- 后继边：原 g(k,l) 经实际复合边律取得内部 m，使 r(k,m) 与 t(m,l)。原 r 值域给 m∈c。
- 原 Pairing/Union 实际构造 M=Succ(m)；已有 i=Succ(k)、j=Succ(l) 给出提升边 ρ(i,M) 与 τ(M,j)。

因此实际提升结果图 γ 的每条边都满足 ∃z(Edge(ρ,i,z)∧Edge(τ,z,j))。
所有 k,l,m,M 都由原存在量词消去/引入处理；没有从 Lean Prop 抽取内部集合函数或选定标准后继。
关键证书：native_zero、native_shifted、native_valueForward、native_edgeForward。

## 完整同域图相等与全部候选识别

原 Replacement 实际构造 ρ 与 τ 的完整复合图 k。
正向点定理给出 γ 的边包含于 k；k 的原单值性给出两图相容。
原完整 functionOn 的同域相等定理证明 γ=k。两图的实际域均为 A；完整域和无杂项要求都保留。
原等词替换把 k 的完整 Composed 合同传给 γ，而不是停在单向边包含。

给定 Ω、原 Composed 及两幅实际输入提升，对任意内部图候选 γ：

```
Lifted(w,g,a,e,A,E,γ) ↔ Composed(w,ρ,τ,A,C,E,γ).
```

逆向识别实际取得 g 的一个提升图，再用完整复合图唯一性与给定候选对齐。
给定实际 γ 的提升，还取得全部内部 i,j 上的两个精确式：

```
Edge(γ,i,j) ↔ ∃z (Edge(ρ,i,z) ∧ Edge(τ,z,j))
LiftValue(g,a,i,j) ↔ ∃z (Edge(ρ,i,z) ∧ Edge(τ,z,j)).
```

关键证书：native_equalGraphs、native_graphComposition、native_graphEdges、native_graphValues、native_liftedIffComposed。
没有外部标准码或有限宿主深度限制，空域及非单射输入继续保留。

## 原自然码的完整相容与独立后继对齐

给定 CodedCompose(w,a,c,e,R,T,K) 和两组实际 CodedLift：
CodedLift(w,a,c,R,A,C,Lr)、CodedLift(w,c,e,T,C,E,Lt)。
原同码图唯一性在给定实际原图上解码每组提升，内部取得实际 ρ,τ,γ 及它们的原 Encoded 自然码。
实际图相容定理于是给出三组提升对应的 CodedCompose。

在 Ω 下，对任意内部候选输出码 Lk：

```
CodedLift(w,a,e,K,A,E,Lk)
  ↔ CodedCompose(w,A,C,E,Lr,Lt,Lk).
```

逆向识别从原复合输出 MapCode 实际取得一个提升码，再由自然复合码唯一性及原等词替换对齐 Lk。
没有给 Lk 额外添加自然性或预先存在的提升见证前提。
关键证书：native_atSources、native_codedComposition、native_codedIff。

若第二个提升的源后继独立给为 D，原 CodedLift 恢复 Succ(C,c) 与 Succ(D,c)。
原 Insert 唯一性证明 C=D；原等词替换把第二提升的源范围从 D 传输到 C，保持原码 Lt 及目标范围 E。
最终得到 C=D 与上述复合结论/识别双条件的合取。
关键证书：native_middleEqual、native_mixedMiddle、native_mixedIff。
独立源、目标范围始终显式保留；没有从列表码单独推断目标范围。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py` 退出 0。
源规则/理论锁、版本、全仓 --no-cache --wfail 构建及五个 trust=0 入口，共九命令全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 全仓构建 | 799 jobs，退出 0 |
| 声明审计 | 8951 项；293 项无公理依赖，8658 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 5 模块、87 项，全覆盖 |
| Internal 累计显式声明 | 6636 项，无漏审 |
| 新增 Source/sourceZF核/nativeZF核模式 | 17 对核心/native 精确足迹 |
| 累计模式 | 860 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 768 份，差异 0 |
| 九命令/五 trust=0 | 全部退出 0 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书依赖精确为 propext、Classical.choice、Quot.sound；native 证书另含既定七项原证书。
这些是既有 Lean 可信基依赖，没有新增对象公理；原 choice 额外证书仍单独限域。
CheckStep4 新增 17 个原核模式实例；全部新声明纳入 Audit 的显式覆盖检查。
独立回读为忽略目录 verification/compose-lift-readback.json；日志、生成辅助和后续详细草案只留本地。
原 OpenAI 完整构建/Comparator 本批未运行；未推送。

## 后续 agent 工程表

| 单元 | 实现职责 | 原核验收条件 | 状态 |
|---|---|---|---|
| F2.3b.2 | 真实零/后继点、完整同域图相等、三组实际码解码、独立后继对齐 | 实际图与码提升/复合相容；任意候选识别双条件 | 完成 |
| F2.3c.1 | 已知源构造下实际目标字段存在；复用全 11 构造精确律 | 源/中间/目标字段在对象量词内取得，两阶段子判断精确恢复 | 待完成 |
| F2.3c.2 | 四原子及已证项复合 | 原零符号和 bound/free 保持，取得原子复合推进 | 待完成 |
| F2.3c.3 | 14 内部参数 Property、否定/四二元/两量词 | 量词用 mixedMiddle 对齐真实中间后继，原 free 码及范围保持 | 待完成 |
| F2.3c.4 | 原 Foundation/Separation 与输出总性/唯一性 | 无 Earlier 的全内部公式复合及实际中间公式码双条件 | 待完成 |
| F2/S | 原核加强/替换规则与全部内部范围 | free_strengthening 兼容、捕获规避替换存在唯一、类型与代数 | 待完成 |
| 5–6 | 原六规则/27 模式及完整理论公理码 | ProofZF/U、全内部编译/解释及最终内部 Con 原核推导 | 待完成 |

Property 必须内部量化六个映射码 R,S,T,U,K,L、六个作用域 a,b,c,d,e,f，以及中间/最终公式码 q,v。
在两组 CodedCompose 和两次真实 RenameFormula 下证明复合 RenameFormula；不能用外部 AST 归纳替代这些量化。
提升相容门禁已为 True；公式复合、恒等/复合联合总门禁、完整 FormulaRename、替换、ProofZF/U 和最终 Con 仍为 False。
