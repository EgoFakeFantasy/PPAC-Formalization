# 实际恒等码、提升恒等与全内部公式恒等验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 e45b6194169a982d78ad6c5b85048313199dcb3a。
F2.1–F2.2 已完成：实际恒等图及原自然映射码存在，真实 binder 提升保持恒等，所有合法内部公式自重命名。
任意内部目标候选下，恒等码的 RenameFormula 精确等价于源 FormulaCode 与目标等于原码。
复合、捕获规避替换、专用 ProofZF/U、内部编译/解释及最终内部 Con 仍未完成。

## 对象语言、背景与最终目标

对象语言为原 YesMetaZFC 的纯等词/成员语言；正式接口为原 FirstOrder.Derives。
背景保持 nativeZF 的完整 Collection 呈现，源 ZF 使用完整 Replacement；既有原核传输与呈现重放逐句适用。
最终目标仍为 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，目标理论为 ZF+PP+ACwo+¬AC。
Con 遍历全部内部 ω 证明码，保留原六规则、27 模式及完整 Separation/Collection；本批不改动这些定义或理论锁。
没有新增对象 AC、标准 ω、外部良基、模型存在或 Con(nativeZF) 前提。

## 实际图、自然码与提升

SyntaxIdentityMapSyntax.graph(a,r) 用原 functionGraph 和纯矩阵 x=y 表示完整恒等图。
SyntaxIdentityGraph 用原 Replacement 实际构造 r；对所有内部 i,j 证明：

```
Edge(r,i,j) ↔ (i∈a ∧ i=j).
```

图对任意集合域 a 存在且唯一；a∈w 时另有完整 IndexMap(w,r,a,a) 及对角性。
不是把 Lean 的 identity 函数作为图见证，也没有假定非空域。

IdCode(w,a,R) 定义为 ∃r(Encoded(w,r,a,a,R) ∧ Diagonal(r))。
给定 Ω(w) 与 a∈w，实际存在该原自然列表码 R。
任意同码实际完整解码图均有对角性；给定 Encoded 时 IdCode ↔ Diagonal。
源与目标域在 IdCode 定义中都明确为 a；没有从列表码单独推断独立的目标范围。

提升的零边由原 Empty 唯一性处理，旧边由实际 k=l 和原后继相等替换处理。
实际 Lifted 图的每条边仍满足 i=j。
对任意 CodedLift(w,a,a,R,u,v,L)，Ω 与 IdCode 推出 u=v 及 IdCode(w,u,L)。
u,v,L 都是内部对象，未固定为宿主后继或标准有限深度。

关键原核闭句：native_graphExists/graphEdges/graphUnique、native_codeExists/codeAtGraph/codeEncodedIff、
native_liftValueDiagonal/liftGraphDiagonal/liftCode。

## 公式恒等的内部归纳

Property(w,n) 在对象语言内部全称量化 R,S,a,b，内容为：
FormulaCode(w,n,a,b) ∧ IdCode(w,a,R) ∧ IdCode(w,b,S) → RenameFormula(w,R,S,a,b,a,b,n,n)。
Earlier 只量化内部 ω 中严格属于 n 的子码，是证明过程中的内部归纳假设。

- 假、真使用原空构造精确律；成员式与等式消去原字段存在量词，使用实际对角图的项恒等律。
- 否定和四个二元构造直接使用严格子码归纳；成员式保留同一个原 ZeroScalar 符号码。
- 两种量词实际取得后继作用域 u 及提升码 L；先证明 IdCode(w,u,L)，再在同一四参数性质中实例化量词体。原 free 码 S 与范围 b 保持。

原 Foundation 及 Property 否定矩阵的完整 Separation 关闭内部成员归纳。
Below 的蕴含守卫显式转为 Earlier 的合取守卫；最终结论没有 Earlier、图解码、载体或历史存在前提。
对所有内部自然源代码与所有内部作用域、恒等码有效，不局限于外部标准 AST。

最终三个闭句分别给出自重命名、任意输出恒等及精确双条件。在 Ω 与两个 IdCode 下：

```
RenameFormula(w,R,S,a,b,a,b,n,q)
  ↔ (FormulaCode(w,n,a,b) ∧ n=q).
```

q 可为任意内部候选；不额外假定其自然性或目标类型。
关键证书为 ObjectSyntaxRenameIdentity.native_formulaReflexive、native_formulaIdentity、native_formulaIdentityIff。
三者均为 YesMetaZFC 原核的空局部上下文 Derives；不是宿主层 AST 相等或语义模型定理。
每个模式都经 Source.Derives → TheoryTransport → sourceZF 原核 → ZFReplay → nativeZF 原核。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py` 退出 0。
首次完整验收在新增 CheckStep4 实例的 namespace 外名称解析处失败；修正检查文件作用域后，重新执行整套九命令，以下仅记录重跑结果。

| 检查项 | 实际结果 |
|---|---|
| 全仓 --no-cache --wfail 构建 | 783 jobs，退出 0 |
| 声明审计 | 8693 项；288 项无公理依赖，8405 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 10 模块、131 项，全覆盖 |
| Internal 累计显式声明 | 6378 项，无漏审 |
| 新增 Source/sourceZF核/nativeZF核模式 | 16 对核心/native 精确足迹 |
| 累计模式 | 815 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 752 份，差异 0 |
| 九命令/五 trust=0 | 全部退出 0 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书的依赖精确为 propext、Classical.choice、Quot.sound；native 证书另含既定七项原证书。
这些是记录中的 Lean 可信基依赖；未新增对象语言公理，原 choice 额外证书仍单独限域。
独立回读记录位于忽略目录 verification/identity-readback.json；完整日志与生成辅助保留本地。
原 OpenAI 完整构建及 Comparator 本批未运行；没有据此报告其通过。

## 下一工程单元

| 单元 | 输入/职责 | 原核验收条件 | 当前状态 |
|---|---|---|---|
| F2.1 | 实际恒等图、原自然码、真实后继与提升 | 实际存在、全边式、任意同码解码对角及提升恒等 | 完成 |
| F2.2 | 全 11 构造、内部四参数成员归纳 | 所有内部公式自重命名；任意候选精确双条件 | 完成 |
| F2.3a | 两个可复合实际完整图与三个明确作用域 | 实际唯一复合图及原自然码；所有内部边的复合双条件 | 待完成 |
| F2.3b | 原项关系、实际复合图与实际 binder 提升 | 项复合及提升与复合相容，保留独立范围及非单射输入 | 待完成 |
| F2.3c | 完整构造精确律和内部参数归纳 | 全内部 FormulaRename 复合；无 Earlier 前提，接原核规则 | 待完成 |
| S | 全内部替换序列和 bound/free 范围 | 捕获规避替换存在唯一、类型与代数，覆盖原替换/加强规则 | 待完成 |
| 5–6 | 原六规则/27 模式及完整理论公理码 | ProofZF/U、全内部编译/解释及最终 Con 原核推导 | 待完成 |

恒等专门门禁为 True；恒等与复合联合门禁、完整 FormulaRename、替换、ProofZF/U 和最终 Con 仍为 False。
不把本批恒等定理称为相对一致性形式化完成；未推送。
