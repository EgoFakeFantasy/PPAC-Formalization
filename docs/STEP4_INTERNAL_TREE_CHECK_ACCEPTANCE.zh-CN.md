# 全内部树递归检查与实际唯一解码验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点17b442304f246d540f34760d519adf6fa16513f6。
本批完成4b.c.4c.v.b.iii：实际唯一求值、任意前段图对应、递归接受/拒绝和唯一节点解码。
通用结构树已经完成；全部11种原生公式的类型/作用域、ProofZF/U及最终内部Con尚未完成。

## 对象合同

语言仅含等词与成员，背景原ZF；推导由Source.Derives经TheoryTransport及ZFReplay返回
原FirstOrder.Derives nativeZF []闭句证书。没有新核、对象AC、Con或外部标准ω假设。
原raw树数值、Nil/Cons、实际长度、完整Kuratowski字段图及其所有内部边均保持。

令R(w,z,e,f,d)为上批具体Step的原完整Recursor图。
Eval(w,z,e,n,y):=∃s∃f(Succ(s,n)∧(R(w,z,e,f,s)∧edge(f,n,y)))。
每个原内部序数n实际存在唯一y；s和f均为对象存在见证，不由Lean选择函数抽取。
任意内部序数d、n∈d及实际图R(w,z,e,f,d)下，
edge(f,n,y)↔Eval(w,z,e,n,y)。该式对任意输出对象y成立。

存在性由真实后继序数和上批实际递归图取得。唯一性先证明不同序数域上的图相容，
再以实际共同输入上的函数单值性对齐。反向边构造使用真实后继域包含与原图相容，
不是把外部标准n的测试外推为全部内部n。
原Recursor限制见证实际给出n上的前段图h及Step(w,z,e,n,h,y)，完整保留递推方程。

## 完整递归判定及标志独立性

Empty(z)、Succ(e,z)、Ω(w)下，每个实际Eval值在ω中，且恰为z或e；并证明e≠z。
Accept(w,z,e,n):=Eval(w,z,e,n,e)，Reject同式末值为z。
Branch(w,z,e,n)实际存在tag,p,l,f，要求原Shape及
∀i∀y(edge(f,i,y)→Accept(w,z,e,y))。
前段图边双条件和严格子码界消去全部历史覆盖前件，证明Good↔Branch。
对于所有内部自然码，Accept↔Branch、Reject↔¬Branch，并且二者完整互斥。

Valid(w,n):=n∈w∧∃z∃e((Empty(z)∧Succ(e,z))∧Accept(w,z,e,n))。
Invalid同式改为Reject。真实标志通过原Extensionality和后继唯一性对齐；
对象等词替换还同时传输算子参数及接受/拒绝输出。
故两公式不依赖实际零/单位见证的选取；所有内部自然码满足Valid∨Invalid、¬(Valid∧Invalid)、Invalid↔¬Valid。
不把两个任意集合当作真假标志。Valid定义不自引用；仅经无Valid测试的Step递归及实际图求值定义。

Recursive(w,n)实际存在tag,p,l,f，要求
Shape(w,n,tag,p,l,f)∧∀i∀y(edge(f,i,y)→Valid(w,y))。
原ZF证明Recursive↔Valid；此闭句量化任意内部候选n，无外加n∈ω前件。
反向证明从原Shape的raw值域实际推出根自然性，再调用已证全部内部自然码判定。
正向对子字段自然性的需求由严格子码界及根自然数传递性实际消去。

## 实际唯一节点解码

NodeData为上述Shape与全部子字段Valid的合取；DecodedFiber实际存在tag,p,l,f和
∀tag'∀p'∀l'∀f'(NodeData(w,n,tag',p',l',f')→
  ((tag'=tag∧p'=p)∧(l'=l∧f'=f)))。

原raw输入单射性先给tag和payload相等；用对象等词替换对齐payload，
再用原列表长度及完整Fields图的联合唯一性取得实际长度和完整图相等。
这保留原图的完整functionOn与精确边条件，不能用字段值自然性替代图的唯一性。
Valid实际产生该四重唯一解码纤维；原核证明DecodedFiber↔Valid，覆盖任意候选对象n。
本结论是结构树节点的精确解码，不是已完成11种公式构造的类型解码。

| 新模块 | 职责 |
|---|---|
| StructuralTreeEvaluationSyntax/Existence/Unique | 实际后继域/完整图/边的求值关系、所有内部序数实际存在唯一 |
| StructuralTreeGraphValues | 任意实际序数前段边与统一求值精确双条件 |
| StructuralTreeHistory | 真实限制历史和当前Step、二值值域及真实单位非零 |
| StructuralTreeRecursiveSyntax/Correspondence | 全内部字段接受条件、Good与实际递归分支对应 |
| StructuralTreeCheck | 实际标志下接受/拒绝双条件和互斥完整分类 |
| StructuralTreeValiditySyntax/MarkerTransport/Canonical | 无标志参数Valid/Invalid、原对象等词传输及全部自然码分类 |
| StructuralTreeRecursion | 无标志参数的递归正确性 |
| StructuralTreeDecode | tag/payload/长度/完整图联合唯一、实际唯一纤维和完整双条件 |
| ObjectStructuralTreeCheck | 20个完整源ZF及原nativeZF闭句证书 |

20个端点为fiber、naturalValue、valueUnique、edgeIff、history、range、goodIff、acceptsIff、rejectsIff、
fixedClassification、validAccepts、invalidRejects、markerTransport、classification、exclusive、invalidIffNot、
recursiveIff、decodedFiber、decodedIff、decodeUnique。
每个均有source_*、*_kernel_certificate、native_*。
CheckStep4核对真实求值见证、自然码守卫、全部字段量词、实际四重节点见证和全部原核端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成529个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit五个入口均以--trust=0通过。
4707项审计：203项无公理依赖，4504项允许依赖；0警告。
本批14个新模块196项显式声明全部审计；Internal具名覆盖累计2392项。
498份源码SHA256独立复核，差异0；累计219对核心/native证书或模式精确依赖通过。
新增20个核心依赖恰为propext/Classical.choice/Quot.sound；native端点恰额外继承原七项ZF闭性证书。
这些是宿主证明证书依赖，没有向对象ZF加入选择公理。
两份可信基JSON、原19规则/九类源ZF锁、固定依赖和原核不改；原choice额外证书仍限域。
锁文件同时用git diff及Git内容核对；内容比较仅规范化Windows检出的CRLF，不忽略其他差异。
树接受/拒绝递归正确性及结构树有效性/解码门禁现为True。
ProofZF/U、任意内部证明码正确性、内部编译器、最终对象Con门禁仍False。
独立回读verification/tree-check-readback.json；日志/哈希/依赖细节仅本地，不自动发布。
未推送；原OpenAI完整构建和Comparator未运行。

## 下一最小工程

按4c.a–c接入纯签名的全部11原生公式构造：falsum/truth/rel/equal/neg/conj/disj/imp/iff/forall/exists。
保留bvar/fvar及索引界、无函数符号、membership编号0、精确字段数和scalar叶。
量词体必须在真实后继bound上下文检查；bound/free长度及替换图量化全部内部自然数。
之后建立全部非单射统一替换、提升和捕获规避的实际内部关系与正确性，再装配完整ProofZF/U。
一般结构树Valid不替代上述类型正确性；最终交付仍是原核Derives nativeZF [] (Con_ZF→Con_target)。
