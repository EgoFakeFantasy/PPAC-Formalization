# 原项列表参数的全公式free替换验收

2026-10-22；分支migration/yesmeta-step3；本批基点7f08049b2d399685cc8a4d1ae1074e73b657b290。
S2.1–S2.3已验收：纯对象公式free替换在全部内部合法公式码上实际存在唯一，并具有准确输入/输出类型、输入双条件和11构造端点律。
原语法数值编码对应、原规则检查兼容、混合bound/free捕获规避操作及最终内部Con仍未完成。

## 固定对象合同

对象语言是原纯等词/成员语言；背景是原nativeZF完整Collection呈现。
源完整Replacement通过既有对象互导和原核replay接入，未增加对象公理。
最终主句仍要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target为ZF+PP+ACwo+¬AC。
内部Con规格遍历全部内部ω证明码，保留原六规则、27逻辑模式和完整Separation/Collection。
专用ProofZF/U完整纯AST、全内部证明码正确性和最终Con主句尚未交付。

新增有限纯AST为：

```
FormulaFreeSubst(w,b,a,c,L,n,q) :=
  ∃R ∃S (IdCode(w,b,R) ∧ CodeConversion(w,a,c,L,S) ∧
         RenameFormula(w,R,S,b,a,b,c,n,q)).
```

b为bound长度，a/c分别为原/目标free长度，L保留原替换项码列表。
R/S和内部列表字段图都在对象量词中；没有把内部存在见证抽成宿主函数或数据。
范围c不从原列表或索引码默认恢复，始终显式保留。
纯OpenTerm只含free变量的对象分类及原列表/索引码转换由S1提供；不套用扩展BasicSetTheory的函数项。

## 实际总性、唯一性与准确输入

在Ω(w)下，对全部内部候选证明：

```
(∃q FormulaFreeSubst(w,b,a,c,L,n,q))
  ↔ (FormulaCode(w,n,b,a) ∧ TermList(w,a,c,L)).
FormulaFreeSubst(w,b,a,c,L,n,q) ∧
FormulaFreeSubst(w,b,a,c,L,n,v) → q=v.
```

实际唯一输出纤维同样与上述准确输入互为双条件。
输出满足FormulaCode(w,q,b,c)和q∈w；源类型也从替换关系恢复。
任意实际IdCode R和实际CodeConversion L→S，都给出FormulaFreeSubst与该RenameFormula的精确双条件。
不同见证先由恒等码唯一性和S1转换码唯一性在对象核中对齐，再调用全内部公式重命名唯一性。
总性先在对象存在量词中构造R/S，再由全内部Rename总性取得q，不留码存在或Earlier前提。
合法输入允许空域、重复目标索引和内部非标准码；未限制标准ω或宿主有限语法深度。

## 原列表字段与11构造规律

两个常量、等式、成员式、否定、四二元、两量词共11构造都有已知端点精确双条件。
端点构造码前提显式保留；不据此把局部端点律当作专用原证明检查器正确性。
成员式保留原零关系符号及符号相等条件。

对已知同类变量端点，bound项关系精确为i∈b且i=j。
free项的目标码q精确取自原替换列表：

```
TermRename(w,r,s,b,a,b,c,n,q)
  ↔ (i∈a ∧ Field(w,L,i,q)).
```

此处保留源/目标变量码、实际列表转换与任意实际图解码前提。
目标不是宿主选定的j或值，而是原列表的实际字段；重复替换像允许出现。

量词分支实际使用Succ(u,b)及恒等码的真实CodedLift，子判断的bound域为u。
同一份原free列表L和其转换S在量词下保持，这对应纯free项像不含bound变量的当前操作范围。
否定、四二元、两量词另有不需要调用方提供R/S/K的接口：
从Ω、b∈w、TermList和端点码出发，在对象存在量词内构造并消去所有码见证。
量词额外保留实际Succ(u,b)，并在对象核中证明u∈w后构造其恒等码。

## 原核传输与实际验收

ObjectFormulaFreeSubst给25组Sentence/source/sourceZF核/nativeZF核闭句证书。
每个source包装实际调用本批对象推导，再经TheoryTransport.sentence和ZFReplay.replay进入原FirstOrder.Derives nativeZF []。
这些对象句子已取得实际原核证明；它们不替代最终Con主句。

`C:/Python314/python.exe -X utf8 scripts/verify.py`退出0。
原规则/理论锁、版本、全仓严格构建及五trust=0入口共九命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 全仓严格构建 | 848 jobs，退出0 |
| 声明审计 | 9880项；294无公理依赖、9586允许依赖 |
| 警告 | 0 |
| 本批新增 | 8模块、150项显式声明、25个闭句模式 |
| Internal显式声明全覆盖 | 7565项 |
| 核心/native精确足迹 | 新增25对；累计1006对 |
| SHA256独立回读 | 817份，差异0 |
| 九命令及五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| YesMetaZFC固定提交 | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书恰依赖propext、Classical.choice、Quot.sound；native证书另恰含既定七项原证书。
原choice额外证书范围没有扩大；对象背景未加AC、标准ω、外部良基、模型或一致性假设。
原库未改，未恢复退役反射实现。独立回读在忽略目录verification/formula-free-subst-readback.json。
生成规格、辅助脚本与详细日志留在本地；原OpenAI完整构建/Comparator未运行；未推送。

## 接续工程表

| 单元 | 实现职责及输入 | 对象交付和原核验收门 | 状态 |
|---|---|---|---|
| S1 | 原项码列表、完整字段图和索引MapCode | 双向实际唯一码、准确输入和任意实际字段对应 | 已完成 |
| S2.1 | FormulaCode、TermList、实际恒等/转换码 | 纯全公式free替换，实际唯一输出、准确类型和输入双条件 | 本批完成 |
| S2.2 | 原11构造和实际原列表字段 | 精确端点律；bound保持，free目标码就是原列表字段 | 本批完成 |
| S2.3 | 实际后继bound域及恒等提升 | 量词保持原free列表；逻辑律的R/S/K见证在对象量词内取得和消去 | 本批完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree语法及数值编码 | 准确原编码对应，并连接原规则5/4的全内部检查；标准宿主实例仅是中间证据 | 待完成 |
| S3 | 混合bound/free项像与真实binder提升 | InstantiateTop/AbstractFreeTop及一般捕获规避替换的全内部存在唯一、类型和代数 | 待完成 |
| 5a | 原六规则/27模式、完整Separation/Collection及目标公理 | 专用ProofZF/U纯AST和准确字段检查，覆盖全部内部证明码 | 待完成 |
| 5b | 内部证书转换器和检查关系 | 任意内部证明码的编译及检查正确性 | 待完成 |
| 6 | 内部解释与固定内部Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

本批五个细分门禁为True；原free_strengthening兼容、完整FormulaRename总门禁、完整混合捕获规避替换、
专用检查器、任意内部证明码正确性、最终Con及相对一致性继续False。
当前操作只把free变量换成纯OpenTerm，不实现bound→free或free→bound的跨类别变换。
S3必须处理两类项像中的bound部分随新binder提升，不能把当前同类Rename提升直接改名为一般替换。
原模式20/23/25需要InstantiateTop，21/22/24需要AbstractFreeTop；规则3也需要后者。
原参数格式与NatPacket/带头部数值树包装须分别核对；继续串行Lean/Lake和逐声明精确足迹验收。
