# 真实历史前置与原reader递归方程对象验收（2026-10-25）

真实历史前置与reader完整运行递归方程已验收：原Replacement构造零头／全内部后继平移的精确序列图，所有真实旧行与新增首步组成真实新历史。真实一步前后完整Run在任意输出候选上满足双条件，四字段Eval构造并消去两端状态码，得到原Advance及Terminal方程。11模块136声明、21组原nativeZF闭句；2523构建、27606审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。全内部varint分段／输出顺序、完整程序规格桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 对象背景与最终目标

纯EqMem、完整ZF及原Separation／Collection保持。21组模式返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`，经既有 `TheoryTransport.sentence` 和 `ZFReplay.replay` 传输；没有新核、对象Choice、不可达、外部标准ω或模型外部良基假设。静态Formula5和有限绑定槽位只构造公式，不生成内部运行数据。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

最终内部主句仍未证明。全内部Proof须覆盖原六规则／27模式及完整公理模式；当前程序递归辅助结果不能替代Proof、完整解释或最终Con。YesMetaZFC仍固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作树和七个既有锁文件均保持。

## 原Replacement构造精确前置序列

给定真实原序列f，域为内部d；新域e满足Succ(e,d)。定义实际值关系：

```text
Shift(f,d,i,y) = ∃j (j∈d ∧ Succ(i,j) ∧ Edge(f,j,y))
Value(f,d,n,i,y) = (Empty(i) ∧ y=n) ∨ Shift(f,d,i,y)
Graph(f,d,n,e,g) = FunctionOn(g,e)
  ∧ ∀i∀y (Edge(g,i,y) ↔ (i∈e ∧ Value(f,d,n,i,y)))
```

零分支精确等价于y=n。原后继注入性和旧序列函数性证明后继分支精确等价于旧位置j∈d且Edge(f,j,y)，并给任意两个候选值相等。对所有内部i∈e，原ω的零／前驱分解取得实际分支；原序数成员界证明前驱属于d；原序列求值给真实值。该分解使用原完整Separation及内部归纳所得定理，不使用外部长度归纳。

固定Formula5的对象单值纤维满足原Replacement接口，实际构造整个Kuratowski函数图g和全部边双条件。旧序列有ω值、n∈ω时，g是真实ω值序列；图集合由原外延原理唯一。图存在不要求n∈ω，ω有界性单独要求实际头n∈ω，二者假设没有混淆。

对实际零z，证明Edge(g,z,n)。对每个实际j∈d及Succ(i,j)，在任意y上有Edge(g,i,y)↔Edge(f,j,y)，包括非标准内部位置；域外候选则由完整Graph边律准确排除。

## 真实reader历史的前置构造

既有History保留真实序列、实际首末值及全部内部位置上的原带码Step。给定History(r,t,l,d,f)、Step(n,r)和Succ(e,d)，本批构造：

```text
∃g (Graph(f,d,n,e,g) ∧ History(n,t,d,e,g))
```

零位置新增的真实row包含Step(n,r)；每个后继位置i由内部前驱分解取得旧j，原旧row的两个实际值及真实Step平移到g。全内部links由原∀i∈d的量词证明，未只抽样标准行。新历史末索引为旧域d，新域e是真实后继，原末状态t保持，实际图由Replacement取得。

用于新增行的后继索引和新域e由原Pairing／Union构造、在对象存在量词中消去。证明中没有选择一条宿主历史、宿主Nat循环、List操作或任意生成的最终答案图。

## 完整Run的一步精确方程

Step(n,r)加一条实际从r返回q的历史，经以上前置构造取得从n返回q的真实Run；所有域／图见证都已消去。反向传播仅需Ω、实际Step和后续Run，不留下新历史存在性前提。

正向先从Step取得实际后继carrier，再应用已验收的原全内部停止／返回存在性取得某个p。前置构造给Run(n,p)，原Run唯一性与已给Run(n,q)对齐p=q，再作原对象相等代换取得Run(r,q)。两方向组合为：

```text
Ω(w) ∧ B∈w ∧ Empty(z) ∧ o∈w ∧ Step(w,B,z,o,n,r)
  → (Run(w,B,z,o,n,q) ↔ Run(w,B,z,o,r,q))
```

q为任意对象输出候选；没有预设其为Option码，也没有保留终止、完整历史、执行长度或归纳假设。正向使用真实返回总性与唯一性，不依赖未证明的历史尾切片。

## 四字段Eval的原推进与终止方程

```text
Eval(w,B,z,o,L,v,s,a,q)
  = ∃n (StateCode(w,L,v,s,a,n) ∧ Run(w,B,z,o,n,q))
```

在任意实际StateCode上，Eval精确归一为Run。原Advance已含真实源State；原类型保持给真实目标State，原四格forest存在性实际构造两个状态码，原Step构造器连接到带码Step，再用上一步Run双条件并消去两个码，得到：

```text
Ω(w) ∧ B∈w ∧ Empty(z) ∧ o∈w ∧ Advance(L,v,s,a,X,y,S,c)
  → (Eval(L,v,s,a,q) ↔ Eval(X,y,S,c,q))
```

该方程没有源／目标状态码参数前提，包含原发射和继续两类实际分支。对原三类Terminal观察，从其真实State构造码并应用上一批真实零步历史方程，同样取得Eval↔原局部Return。对象初始化Parse和Eval均以同一原StateCode与Run为基础，但本批尚未完成规范varint分段或完整Bytes／Canonical／Tok桥。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句模式 | 11／136／21 |
| 定向native构建 | 2258 jobs通过 |
| 全仓构建 | 2523 jobs通过 |
| 声明审计 | 27606；无公理502；允许足迹27104 |
| 警告／SHA256不一致 | 0／0 |
| 验收命令／trust=0 | 9条全部退出0／其中5条 |
| 全部核心／native精确证书对 | 3140 |
| Internal显式声明覆盖 | 25262 |
| 全部哈希独立回读 | 2303项一致 |
| 原数学源码、AST及既有锁文件 | 保持 |
| 全部旧布尔叶 | 保持，无变化 |

21组核心证书的准确足迹为propext、Classical.choice、Quot.sound；native准确为这三项加原锁定七项。136个声明在扩展允许清单前已独立预审计，没有放宽其他声明；宿主Classical.choice不作为对象AC前提。仅新增object_actual_reader_prepend_history_and_full_run_step_terminal_equations_proved=true；完整分段／程序规格、Basic AST、内部Proof及Con保持未完成。

## 清理、证据与后续流程

编译前Lean／Lake为0，终止0；精确工程.local白名单删除11个被替代的生成脚本、临时驱动、检查片段及冗余／失败日志，共39142逻辑字节。C盘可用空间实测由100986286080至100985958400字节；系统即时变化单独记录，不能将逻辑删除量当成实际净空间收益。正式源代码、证据、工具链、依赖及其他项目均未动。

本地材料不发布：verification/reader-recursion-readback.json、summary.json、commands.json、build.log、audit.log；.local/reader-recursion-preaudit.json、preaudit.log和reader-recursion-precompile-cleanup.json。提交后复核全部工作文件哈希、Git原始字节及干净状态。

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原状态、Cons及带码一步 | 实际字段、准确域及联合唯一 | 已验收 |
| R3／R4a | 真实历史、停止及原观察 | 全内部长度界、停止历史联合唯一与原因分类 | 已验收 |
| R4b.1／.2／.3a | 实际逆序、返回、初始化 | 实际Option载荷、Run与Parse对象唯一纤维、全部常数消去与空输入方程 | 已验收 |
| R4b.3b.1 | 真实历史前置与完整运行递归 | Replacement精确序列、全部内部行、Step前后Run双条件、无码参数Eval的Advance／Terminal方程 | 本批已验收 |
| R4b.3b.2 | 全内部varint分段与输出顺序 | 实际value／scale／acc不变量、完整段消费与规范分段唯一 | 下一单元 |
| R5 | readTokens与Bytes／Canonical／Tok | 全内部程序／规格双条件、所有无效码及完整字节包覆盖 | 待完成 |
| A／P | 原Basic AST及内部Proof | 六规则／27模式、完整Separation／Collection与全部内部码 | 待完成 |
| I／C | 原数学解释及内部Con | 语言／理论／背景核对、对象证明变换及nativeZF中的Con蕴含 | 待完成 |


下一单元用本批Eval一步方程连接独立Canonical／Prefix的内部递归：全内部段消费须维护value+n×scale、scale×128与实际acc的Cons／逆序顺序；完成整个varint段的方程，再处理多token分段与全部无效候选的逆向证明。最终仍须完整字节包、原Basic AST、内部Proof、数学解释及对象Con。
