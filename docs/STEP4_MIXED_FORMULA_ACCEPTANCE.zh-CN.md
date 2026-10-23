# 一般混合公式替换实际总唯一与原核证书验收

2026-10-23；分支migration/yesmeta-step3；本批基点31f897019a3de70d6b1ca35267c51ae4b8ecae11。
S3.3b.1–S3.3b.2已验收。原操作数值编码对应、InstantiateTop/AbstractFreeTop、规则4/5内部检查兼容与最终内部Con尚未完成。

## 固定对象合同

语言为原纯等词/成员语言，背景B保持原nativeZF完整Collection呈现。
源完整Replacement通过既有对象互导及原核replay接入；未改依赖或增加对象公理。
最终要求原FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target为ZF+PP+ACwo+¬AC。
Con_T := ¬∃p(p∈ω ∧ Proof_T(p,code(⊥)))，遍历全部内部ω证明码。
Proof_T须核验原六条Hilbert规则、27逻辑模式、完整Separation/Collection及精确原元数据。
Con目前仍是已锁定的数学规格；专用ProofZF/U纯AST及最终Con对象主句尚未实现。
Lean宿主Consistent、语义模型或编译通过均不能代替最终主句。

## 实际混合状态与量词

裸cell仍编码七个自然字段[R,S,a,b,c,d,q]。
新legal := TermLists(w,a,b,c,d,R,S) ∧ FormulaCode(w,q,c,d)，未复用旧IndexMap的legal/state。
TermLists允许两种目标变量类别、重复像与空源域；项码不受目标变量数的数值上界限制。
合法状态实际存在；状态码单射与实际唯一七字段解码均有对象证明。

量词在对象内部同时绑定四见证A,C,K,H：

```
∃A ∃C ∃K ∃H
  (CodedBinder(w,R,S,a,b,c,d,A,C,K,H) ∧
   ChildSubst(w,K,H,A,b,C,d,x,X)).
```

A/C为源/目标bound范围后继，K/H为两份实际提升环境码。
bound源与free源的像都移动其中的目标bound分量；free源索引本身不变。
任意两组实际提升见证按两个后继和两个环境码对齐，不能固定旧free环境S不变。

## 实际公式输出与精确端点

四类原子分支使用已证CodedMixedTerm，成员关系保留同一原零符号；七类逻辑分支保持原构造和内部子源码严格递减守卫。
明确的原Separation实例构造自然状态集合，Extensionality证明实际单值性。
具体算子的总性和单值性已消去，原序数递归实际取得图、历史与求值集合。

```
MixedFormulaSubst(w,R,S,a,b,c,d,n,q) :=
  n∈w ∧ ∃v(Evaluation(w,n,v) ∧ ContainsState(w,v,R,S,a,b,c,d,q)).
Input := FormulaCode(w,n,a,b) ∧ TermLists(w,a,b,c,d,R,S).
```

所有内部候选上的完整递归双条件与历史read对应均已证明。
原Foundation与相应Separation关闭整个内部ω上的六参数输出纤维归纳；不保留Earlier前提或外部标准深度界。
每个合法Input实际取得唯一q，并有准确源/目标类型和q∈ω。
存在输出、实际唯一输出纤维分别恰与Input等价；非法Input被正式拒绝。
求值集合唯一与公式输出q唯一由不同定理证明，不能互相替代。

已知合法Input及原源/目标构造时，全部十一类精确端点律成立：
空原子保持自身，等词式逐项替换，成员式逐项替换且保持零符号，否定与四二元联结词逐子式替换，两种量词实际提升两张环境表。
给定CodedBinder，两量词端点均精确等价于使用K/H的实际子公式判断。

## 原核传输与实际验收

ObjectMixedFormula提供50组Source闭句、sourceZF映像原核证书、nativeZF原核证书。
实际返回原FirstOrder.Derives nativeZF [] (Translation.sentence sentence)，未替换推导核。

968构建任务、11222项审计、0警告；九命令和五个trust=0入口均退出0。
本批67模块607显式声明、50组闭句；累计8907项Internal显式声明全覆盖，937份源哈希独立一致，1152对核心/native精确足迹。
306项无公理依赖，10916项依赖在原允许范围内。
每组核心足迹精确为propext/Classical.choice/Quot.sound；native精确再加原七项证书。
七份锁未变；YesMetaZFC固定于039c8e132cc19671d73a3933c66b4799d2599dd6且工作区干净。
独立回读逐一核对全部源哈希、全部证书对、声明覆盖及未完成门。

执行命令：C:/Python314/python.exe -X utf8 scripts/verify.py。
原OpenAI完整构建和Comparator未运行；未推送或建PR；生成器、日志、回读仅在本地忽略目录。

## 后续agent工程合同

| 单元 | 输入 | 必须取得的对象推导 | 状态 |
|---|---|---|---|
| S3.3b | 原自然混合环境码与完整原FormulaCode | 全内部ω实际唯一混合公式输出、输入/纤维双条件、11端点 | 已验收 |
| S3.4a | 合法目标项码、内部后继与首槽表 | InstantiateTop：源bound0映为给定项，旧bound后继映回前驱，free保留；实际表/原码存在唯一 | 待完成 |
| S3.4b | 内部bound/free范围与首槽表 | AbstractFreeTop：free0映为新bound0，其余free前驱重编号，旧bound移位；实际表/原码存在唯一 | 待完成 |
| S3.4c | 两类特定环境与本批混合公式替换 | 原instantiate/abstract操作数值编码对应、嵌套binder保护及实际唯一输出 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree数值语法 | 原规则5/4任意内部码检查兼容，保留原参数域与0元数据 | 待完成 |
| 5a | 六原规则、27模式及完整ZF/U公理 | 专用ProofZF/U有限纯AST；精确原元数据和全部内部证明码量化 | 待完成 |
| 5b | 内部语法操作与源证书转换器 | 全内部编译/检查正确性，覆盖完整Separation/Collection | 待完成 |
| 6 | 内部解释与固定内部Con | 原Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

不得把本批的一般混合替换记为原操作数值编码对应或最终任意内部证明迁移已完成。
