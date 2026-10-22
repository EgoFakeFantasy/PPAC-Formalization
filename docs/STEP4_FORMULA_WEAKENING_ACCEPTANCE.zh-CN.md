# 全内部 free 头槽公式弱化验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 ee298e2ebefca9c25f3f703a1ad19e555e15af0a。
F2.4b.1 与 F2.4b.2 已验收：纯弱化关系、全部内部合法输入的实际唯一输出和全11构造的已知端点规律。
原语法编码对应、完整内部六规则检查器中的 free_strengthening 兼容、捕获规避替换和最终 Con 仍未完成。

## 对象合同与实际定理

对象语言是原单排序纯等词/成员语言，背景是原 nativeZF 的完整 Collection 呈现。
Source 的完整 Replacement 通过已经证明的对象公理互导和原核 replay 接入。
目标保持 ZF+PP+ACwo+¬AC，最终要求原核中的对象蕴含 Con_ZF→Con_target。
内部 Con 的固定规格是不存在内部 ω 中被原六规则/27模式检查接受的矛盾证明码；完整 ProofZF/U AST 尚未交付。
没有新增对象公理、AC、标准 ω、外部良基、模型存在或一致性假设。

新增纯对象公式为：

```
WeakenFree(w,a,b,B,n,q) :=
  ∃R ∃S (IdCode(w,a,R) ∧ ShiftCode(w,b,B,S) ∧
         RenameFormula(w,R,S,a,b,a,B,n,q)).
```

a 是 bound 长度，b 是原 free 长度，B 为其实际后继。
原规则从 formula.weakenFree 的推导得到原 formula 的推导；上式编码的语法方向是原结论 n 到弱化前提 q。
不构造整个后继域到原域的总逆映射，因而不排除合法空 free 上下文。

在 Ω(w) 下，原对象核证明：

```
(∃q WeakenFree(w,a,b,B,n,q))
  ↔ (FormulaCode(w,n,a,b) ∧ Succ(B,b)).
WeakenFree(w,a,b,B,n,q) ∧ WeakenFree(w,a,b,B,n,v) → q=v.
```

存在唯一纤维同样与精确输入互为双条件。由 FormulaCode 还实际取得 B 和唯一 q，结论不留下后继存在前提。
输出满足 FormulaCode(w,q,a,B) 且 q∈w。任意实际恒等码 R、位移码 S 都给出 Weak 与该 RenameFormula 的精确双条件。
不同恒等码见证通过完整图唯一性及原编码唯一性对齐，继而与既有位移码唯一性一同消去见证依赖。
所有码、图、后继和结果的存在/唯一性使用对象 exI/exE/allI；Fin m 只是纯公式的变量位置。
覆盖全部内部 ω 中的合法码，不局限宿主标准码或外部有限深度。

## 构造子与项规律

两个常量、等式、成员式、否定、四个二元逻辑构造及两个量词，共11构造均有已知端点精确双条件。
常量律允许任意候选 q；其余端点律保留原源/目标构造码前提，不把这些条件隐藏成无前提的任意码判断。
已知同类变量码时，bound 项关系精确为 i∈a∧i=j，free 项关系精确为 i∈b∧Succ(j,i)。
成员式保留原关系符号零码与符号相等条件。

给定实际 Succ(u,a) 与任意 IdCode(w,u,L)，原核证明它确实是 R 的实际 CodedLift。
量词内部使用该真实 bound 提升，free 的 b/B/S 保持。
否定、四二元、两量词另有不含 R/S/L 参数的接口：从 Ω、a∈w、b∈w、Succ(B,b) 和端点码出发，
在对象存在量词内取得并消去所有码见证；量词额外保留实际 Succ(u,a)。

freshFreeAbsent 和 emptyFreeAbsent 是项层排除定理：目标 free 索引为零或原 free 域为空时，相应 free 项关系为假。
本批不据此宣称独立的整棵公式自由出现谓词定理已完成。

## 原核证书与实际验收

ObjectSyntaxWeakenFree 提供30组 Sentence、source、sourceZF核证书与 nativeZF核证书。
source 证明返回原 Source.Derives，经 TheoryTransport.sentence 和 ZFReplay.replay 返回原 FirstOrder.Derives nativeZF []。
这30个对象句子的推导传输已经完成；它们不替代尚未完成的最终内部 Con 主句。

`C:/Python314/python.exe -X utf8 scripts/verify.py` 最终退出0。
源码锁检查、版本、全仓严格构建及五个 trust=0 入口共九命令全部退出0。
审阅修正了 verify.py 中累计历史 scope 文案的状态矛盾，随后重新执行完整验收，以下采用最终结果。

| 检查项 | 实际结果 |
|---|---|
| 全仓严格构建 | 828 jobs，退出0 |
| 全部声明审计 | 9500 项：294 无公理依赖，9206 允许依赖 |
| 警告 | 0 |
| 本批 | 10模块、184项显式声明、30个闭句模式 |
| Internal 显式声明覆盖 | 7185项，无遗漏 |
| 精确核心/native足迹 | 本批30对；累计948对 |
| SHA256独立回读 | 797份，差异0 |
| 九命令与五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| YesMetaZFC固定提交 | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书恰依赖 propext、Classical.choice、Quot.sound；native证书另恰含既定七项原证书。
原 choice 额外闭性证书范围未扩大；原库未修改；未恢复退役反射实现。
独立回读在忽略目录 verification/weaken-free-readback.json；生成规格、辅助脚本、详细日志留在本地。
原 OpenAI 完整构建与 Comparator 未运行；未推送。

## 接续工程表

| 单元 | 实现输入与职责 | 交付与原核验收门 | 状态 |
|---|---|---|---|
| F2.4a | 原 free 头槽的实际完整图和原自然列表码 | 全内部边、唯一图码、精确输入、空源域与零槽排除 | 已完成 |
| F2.4b.1 | 恒等码、位移码、全内部 RenameFormula | 纯 WeakenFree；实际唯一输出、精确输入双条件和无后继存在前提的实际状态 | 本批完成 |
| F2.4b.2 | 原11构造端点、真实 bound 提升、free位移 | 全11已知端点律；逻辑律的所有码见证在对象量词内消去 | 本批完成 |
| F2.4b.3 | 原 Formula.weakenFree 与原数值语法编码 | 原操作的准确编码对应；外部标准实例对应只是中间证据 | 待完成 |
| S1 | 纯集合语言的原 free_substitution 项码列表字段 | 全内部 open-term/fvar 索引对应、原列表与实际索引图转换，不擅改原规则格式 | 待完成 |
| S2 | 跨 bound/free 的实例化、抽象及真实 binder | 全内部捕获规避操作的存在唯一、类型、精确构造律与代数 | 待完成 |
| 5a | 原六规则/27模式、完整 Separation/Collection 和目标附加公理 | 专用 ProofZF/U 纯 AST；加强规则从弱化前提回到原结论，覆盖所有内部证明码 | 待完成 |
| 5b | 原源/目标证书转换和内部编码关系 | 全内部编译器及检查正确性；不能仅对标准宿主树归纳 | 待完成 |
| 6 | 固定内部 Con 与内部解释 | 原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target) | 待完成 |

四个本批细分门禁为True；原 free_strengthening 兼容、完整 FormulaRename 总门禁、
捕获规避替换、专用检查器、任意内部证明码正确性、最终 Con 和相对一致性门禁继续False。
每个实施 agent 只改约定模块；由主 agent 串行 Lean/Lake，审阅 agent 只读检查对象层范围、固定理论和原核接口。
复核原纯集合签名后可以研究把 open-term 替换复用成非单射 free 重命名，
但原规则使用的项码列表必须保留，扩展签名模块不能直接视为纯索引表；该路线仍须全内部对象证明。


## 下一替换单元的源码核对

本节是已核查的实现路线，不计为内部替换证明完成。
固定原库 SetTheory/Language.lean:14 的 FunctionSymbol 为 Empty；Logic/Syntax.lean:290 的 OpenTerm 具有空bound上下文。
原核 Derivation/Core.lean:179–185 的 free_substitution 因而在本项目纯语言中只允许 fvar 项像，允许重复目标索引。
Derivation/Substitution/Basic.lean:1495 的 substituteFree_of_renaming 是宿主语法等式，后续必须再证明全内部编码版本。

上游 ProofT/ProofTreeCode.lean:26–30 的带头部完整证明树把 rule-5 替换参数保存为 termCode 的原列表，
localRun:99–104 对它进行 argumentsList 解码，不能直接用裸索引 MapCode 替换该字段。
该模块打开 Nonlogical.BasicSetTheory；此扩展签名含函数符号，和本工程纯 SetTheory.signature 不同。
必须仅对专用纯语言检查器内的合法 OpenTerm 证明唯一 fvar 索引恢复及完整图/码转换。
NatDecode.tree:54–64 则是另一种不带相同头部的树格式，NatDecode.decode:72 使用 NatPacket；
本批只以它核对原推导规则方向，不将它的字节编码等同现有数值结构树或带头部 ProofTreeCode。
完整专用 ProofZF/U 的编码与对应仍须在其实施单元中证明。

现有 RenameFormula 分别保持bound/free类别，因此不能覆盖跨类别的两项操作：
InstantiateTop 把顶层 bound0 换成 free项；AbstractFreeTop 把 free0 变成 bound0 并调整其余位置。
原 LogicalAxiomEncode.lean:31–37 的 tag20/23/25 需要前者，tag21/22/24 需要后者；
原 forall_generalization（Core.lean:171–174）也需要 AbstractFreeTop。
在混合替换像深入量词时，两类像中出现的bound索引都必须正确位移，不能只复用当前同类重命名提升而省掉新证明。
