# 内部纯项重命名验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点54907d28445980a984019ed1fa0cdb2ee4d85fee。
落实4c.c.1/4c.c.2的纯项分支：实际完整索引映射下的内部重命名，源/目标类型、实际输出存在唯一和精确图边合同。
新增9模块179项显式声明、31个完整Source/sourceZF核/nativeZF核闭句模式。
完整公式重命名、量词提升、捕获规避替换和Proof/Con仍未完成。

## 对象语言与背景

仍使用原纯等词/成员语言、原ZF和原FirstOrder.Derives，不增加新公理或推导核。
所有长度、映射图、变量码和索引均是内部对象；不限制外部标准ω或标准码。
外部Bool只索引bound/free两个固定公式模式；实际索引及码的见证全部经原exE消去。
没有从Lean的Prop中抽取Type层的索引函数或输出码。

## 完整映射与重命名定义

IndexMap(w,r,a,c):=Ctx(w,a,c)∧Sequence(r,a,c)。
原Sequence保留完整functionOn，排除图中杂项，并保证每条实际边的目标属于c。
源长度a和目标长度c都属于内部ω。没有单射、满射或两长度相等前提。
Maps(w,r,s,a,b,c,d)分别给出r:a→c及s:b→d，bound/free分工固定。

RenameBranch(bound,w,r,a,n,q)实际存在内部i,j，使：
i∈a、Edge(r,i,j)、原Code(bound,w,i,n)、原Code(bound,w,j,q)同时成立。
RenameTerm由Maps与bound/free两个RenameBranch的对象析取组成。
其定义不直接塞入输入或输出Term测试，而由真实索引、原码和图边推出这些类型性质。

## 已证明的对象结论

| 结论 | 实际推导 |
|---|---|
| 源/目标作用域 | 原变量分支及图范围推出Term(w,a,b,n)与Term(w,c,d,q) |
| 输出自然性 | 目标Term的原值域定理推出q∈ω |
| 非单射映射下唯一性 | 同源原码恢复唯一源索引，原图单值性恢复唯一目标索引，原变量码唯一性恢复唯一输出 |
| bound/free排他 | 原变量码类互斥，禁止跨类重命名 |
| 实际输出存在 | 原完整函数图在内部索引上取得实际值，再用原变量码存在性构造实际输出 |
| 实际唯一类型纤维 | 每个合法输入实际存在自然输出、RenameTerm及目标Term，且对全部候选输出唯一 |
| 输入合法性双条件 | 给定Ω及Maps，源Term等价于实际输出存在，也等价于实际唯一类型纤维 |
| 已知原变量码精确式 | RenameTerm精确等价于输入索引属于源作用域且对应实际图边成立 |
| 错误图边拒绝 | 在给定同类源/目标变量码时，缺失对应边正式推出¬RenameTerm |
| 实际对角图恒等律 | 给定两个完整对角映射图，RenameTerm推出原码相等；每个合法输入实际自重命名 |

唯一性不依赖索引图单射。多个源索引可以映到同一目标索引，所得输出仍由给定输入唯一确定。
实际对角图是对象∀i∀j(Edge(r,i,j)→i=j)前提，不是宿主identity函数。
本批消费给定完整图；没有宣称已经构造任意复合图或量词提升图。

## 关键原核闭句

ObjectSyntaxRenameTerm.native_existsTerm、native_fiber、native_fiberIff
给出全部内部合法输入的实际存在唯一类型纤维。
native_sourceTerm/native_targetTerm证明源/目标类型保持；
native_knownTerm对两个实际原变量码给出精确图边双条件，含bound/free两个实例。
native_unique、native_identity及native_reflexive分别给出非单射条件下唯一性和对角图恒等律。

所有31个闭句模式均先由原19条Source规则构造证明，
经TheoryTransport给出sourceZF核证书，再经ZFReplay返回原nativeZF的FirstOrder.Derives []。
泛型闭句与关键AST均接入CheckStep4，全部显式声明接入Audit。

## 实际机器验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0。
两份源规则/理论锁、版本、全仓wfail构建以及五份trust=0检查/审计入口共九命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 674 jobs，退出0 |
| 声明审计 | 6998项；266项无公理，6732项允许依赖 |
| 警告 | 0 |
| Internal显式声明 | 4683项，无漏审 |
| 新增闭句模式 | 31对核心/native精确足迹 |
| 累计闭句模式 | 558对核心/native精确足迹 |
| 源码SHA256独立回读 | 643份，差异0 |
| 九命令及五trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与本批基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

31对核心证书精确依赖propext、Classical.choice、Quot.sound；
native证书另含原七个固定ZF定义证书的既有依赖，无额外原choice证书。
没有新增自定义公理；原19规则、九类ZF公理和推导核不变。
独立回读记录在忽略目录verification/internal-term-rename-readback.json，
源日志及探针保持本地；原OpenAI完整构建与Comparator本批未运行；未推送。

## 后续仍需完成

量词提升必须遵守固定依赖原Logic/Syntax.lean的VariableRenaming.lift：
新槽here→here，旧there(i)→there(r(i))；自由映射保持不变。
下一步实际构造提升图，证明全内部零/后继边精确式、完整定义域、范围和唯一性，
再用严格子码对象递归实现完整11类FormulaRename。
捕获规避替换、专用ProofZF/U完整AST、任意内部证明码正确性、
内部编译器和最终Derives nativeZF [] (Con_ZF→Con_target)仍未完成，相关门禁保持False。
