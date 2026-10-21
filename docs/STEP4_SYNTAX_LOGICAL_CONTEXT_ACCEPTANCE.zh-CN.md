# 七种逻辑局部分支与实际上下文载体验收

日期：2026-10-22；分支migration/yesmeta-step3。
本批基点5649309014f474ffab79a149ead41f6a8bdd3297。
完成4c.a.iii.b的七种逻辑/量词局部分支，并完成4c.b.1a实际集合载体。
新增33个完整闭句模式实际取得原FirstOrder.Derives nativeZF []证书。
局部状态Separation、组合算子和完整公式类型递归仍未实现，不能据此声称ProofZF/U或Con完成。

## 固定对象合同

背景仍为原ZF，语言只有原等词/成员，推导先在Source.Derives中完成，再经既有传输回放到原nativeZF核。
未增加对象AC、不可达、Con前提或新公理核；原19规则、九类源ZF、两份可信基和固定依赖不改。
所有历史、子码、内部bound/free长度、后继集合、状态集合及候选字段都是对象变量。
外部Fin 4只索引四种二元联结词，Bool只索引两个量词/有限模板；每个模式返回实际原核闭句证书。
Fin m仅是公式变量槽位，不限制内部上下文、内部自然数和候选码取值。

## 实际上下文集合值读取

一个类型状态S是内部上下文Kuratowski对的集合；它不要求是函数图。
用原Edge(S,b,f)表示上下文对(b,f)属于该状态。
历史h则保留原完整functionOn，输入是子码，输出是其状态集合。

Read(h,x,b,f):=∃S(Edge(h,x,S)∧Edge(S,b,f))。
给定完整FunctionOn(h,d)和实际Edge(h,x,V)，原核证明Read(h,x,b,f)↔Edge(V,b,f)。
这不是宿主函数求值，不把每个子码固定成一个布尔值。

Advanced(h,x,b,f):=∃k(Succ(k,b)∧Read(h,x,k,f))。
给定任意实际Succ(k,b)，原Extensionality和原后继唯一性证明Advanced↔Read(h,x,k,f)。
Ω(w)、Ctx(w,b,f)和Succ(k,b)另推出Ctx(w,k,f)及b∈k，确保实际bound后继和free不变。
Read/Advanced及所有局部AST均证明任意非单射变量重命名等式。

## 七种局部分支及精确类型

| 原构造 | 标签/字段 | 实际子式状态查询 |
|---|---|---|
| neg | 4 / 单字段x | Read(h,x,b,f) |
| conj | 5 / x,y | Read(h,x,b,f)∧Read(h,y,b,f) |
| disj | 6 / x,y | Read(h,x,b,f)∧Read(h,y,b,f) |
| imp | 7 / x,y | Read(h,x,b,f)∧Read(h,y,b,f) |
| iff | 8 / x,y | Read(h,x,b,f)∧Read(h,y,b,f) |
| forall | 9 / 单字段x | Advanced(h,x,b,f) |
| exists | 10 / 单字段x | Advanced(h,x,b,f) |

这里检查语法类型，不计算公式真值。neg不否定子式类型状态；disj/imp也要求两个子式都类型正确。
每个局部分支保留完整Ctx(w,b,f)、精确原字段构造、每个子码严格属于父码及对应状态读取。
已知原单字段/二字段构造码时，分支恰好对应Ctx与表中查询条件。
给定实际Succ(k,b)，两个量词有专门双条件：Quantified↔(Ctx(w,b,f)∧Read(h,x,k,f))。
它明确查询k而不是原b；即使当前上下文b上有状态，也不能替代后继上下文的状态。

合法Ctx、内部自然子码和所需真实读取条件实际构造自然父码，并保留给定子字段。
量词构造使用实际后继见证k和Read(h,x,k,f)，不假定父码已经存在。
全部局部父码属于内部ω；原字段有严格子码界，同输入码唯一，同码恢复所有字段。

## 实际唯一解码与拒绝

SingleUnique(tag,w,n,x):=∀u(SingleCode(tag,w,u,n)→u=x)。
BinaryUnique以∀u∀v要求两个字段分别相等。
候选字段量词覆盖全部内部集合，不预先限制为当前scope或外部标准码。
DecodedSingle/DecodedBinary实际存在原字段，保留原构造、严格子码界、正确读取和完整唯一性公式。
原核证明各局部分支↔实际唯一解码纤维；覆盖否定、四种二元联结词和两个量词实例。

异原标签与当前分支矛盾。未知标签拒绝直接量化内部自然t、payload p及Raw(w,t,p,n)，
只要t不满足当前分支的对象数码标签，就不能同时通过该分支。
给定已知原构造码，缺少所需Read/Advanced会被拒绝。
两个量词另证明：给定实际Succ(k,b)而¬Read(h,x,k,f)，该量词局部分支被拒绝。

## 实际上下文与状态载体

Tower(w,A,C,U):=PowerOf(A,w)∧PowerOf(C,A)∧PowerOf(U,C)。
三个原PowerSet实例在对象层实际取得A,C,U；原Extensionality证明整个三元组逐分量唯一。
此定理对任意内部集合w成立，特别适用于内部ω。
没有借用Lean幂集或Type层选择函数来构造这些集合。

若b,f∈w，原Kuratowski对p=(b,f)确实属于C=P(P(w))。
证明真实解出{b}和{b,f}，先证明二者是w的子集、属于A，再证明p⊆A，因而p∈C。
还实际构造某个这样的p∈C，不只证明已有p的条件界。
任何状态集合V只要V⊆C，就属于U=P(C)。这给后续集合值递归提供实际统一输出界。
本批尚未用Separation构造特定的局部类型状态V；未声称递归算子或完整状态图已经存在。

## 模块与验收结果

12个新模块共231项显式声明，全部加入Audit：
SyntaxContextReadSyntax/Read，SyntaxLogicalSyntax/Typing/Existence/Fields/Decode/Reject，
ObjectSyntaxLogical，SyntaxContextCarrierSyntax/Carrier，ObjectSyntaxContextCarrier。

ObjectSyntaxLogical提供27个闭句模式；ObjectSyntaxContextCarrier提供6个。
CheckStep4核对原标签、读取AST、实际后继槽位和幂集层次，
并具体检查四个二元模式、两个量词及否定的类型/构造/解码或拒绝证书。

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：两项固定源检查、Lean版本、全仓wfail构建，以及
Check/CheckStep2/CheckStep3/CheckStep4/Audit五份lake env lean --trust=0入口。
结果：578个构建任务；5535项声明审计；235项无公理依赖、5300项允许依赖；0警告。
Internal累计3220项具名声明全部覆盖；累计330对核心/native证书或模式精确足迹通过。
新增33对核心恰为propext、Classical.choice、Quot.sound，native端点另继承原七个ZF证书。
这里的Classical.choice是Lean证明基础依赖，没有引入对象AC；原choice额外证书仍保持限域。
547份源码SHA256独立重算差异0；固定YesMetaZFC为039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
本地独立回读verification/syntax-logical-context-readback.json；日志/探针/哈希不入库。
未推送；原OpenAI完整构建和Comparator未运行。

## 未完成关卡

下一步组合全部11个原构造的局部判据，并用实际C上的Separation构造唯一上下文状态集合，
排除非上下文对杂项，证明逐对成员双条件和输出属于U。
随后证明集合值算子总单值性并实例化原对象超限递归，证明真实前段状态读取和完整类型正确性。
内部非单射捕获规避替换、原ZF/U全部规则与模式检查、任意内部证明码正确性、
内部编译器和最终Derives nativeZF [] (Con_ZF→Con_target)均仍未完成。
所有相应完整类型/递归/替换/Proof/Con门禁继续为False。
