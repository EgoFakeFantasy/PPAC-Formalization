# reader全内部长度守恒及历史长度界对象验收（2026-10-25）

reader全内部长度守恒与历史长度界已验收：每个实际历史域索引都有唯一的实际剩余长度；真实Cons消费使剩余长度减少一，原完整Separation与固定Formula4的内部ω归纳消去全部守恒IH，得到索引加剩余长度等于初始长度。任意实际历史索引及末索引均不超过真实初始输入长度，过长接受历史不可能。8模块85声明、13组原nativeZF闭句；2460构建、26717审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。完整停止历史存在唯一、EOF实际逆序、原reader程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 背景理论、正式接口与最终目标

纯EqMem语言与完整ZF（完整Separation／Collection）保持原状。每个本批闭句均返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`，由 `TheoryTransport.sentence` 和 `ZFReplay.replay` 传输。未引入对象Choice、不可达、外部标准ω、模型外部良基或新推导核。YesMetaZFC固定于 `039c8e132cc19671d73a3933c66b4799d2599dd6`，依赖工作树干净。

最终任务仍为：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

这里内部Proof须覆盖全部内部ω，包括非标准与无效码，并核验原六规则／27模式及全部公理模式。本批不声称上述最终主句已证明。

## 实际剩余长度与相邻步

保持此前State、StateCode、CodedStep和History的原定义。新投影完全使用原实际输入和原内部列表长度：

```text
LengthAt(w,f,i,a) = ∃L (InputAt(w,f,i,L) ∧ HasLength(w,L,a))
Balance(w,f,N,i) = ∀a (LengthAt(w,f,i,a) → Sum(w,i,a,N))
AllBalance(w,f,N) = ∀i∈w Balance(w,f,N,i)
```

LengthAt中的L是对象存在量词，不抽取宿主列表或Type层选择函数。原历史每个实际域索引取得有效L，原列表长度存在性取得实际a∈ω；输入唯一性与原HasLength唯一性给LengthAt的a唯一。LengthAt本身还能推出i属于原历史图定义域。

每个实际相邻历史步给原Tail(L,K)，即存在原HeadRest与实际Cons。原列表长度Cons前驱定理取得k及Succ(a,k)、HasLength(K,k)，与实际K长度b的唯一性对齐k=b，得到Succ(a,b)。此处Succ(a,b)表示a=b+1。

## 原内部ω归纳消去全部守恒IH

基点从原Empty唯一性把实际种子边搬到任意空索引；原输入投影和原HasLength唯一性使该处长度a=N，再用原零加法与交换律证明Sum(i,a,N)。

后继点由实际LengthAt(j,b)取得j∈d，原Succ(j,i)及History长度关系推出i∈l。原历史输入及原列表长度存在性在对象量词内取得实际旧长度a，逐步消费给Succ(a,b)。用IH的Sum(i,a,N)、原无界加法存在性和后继加法，得到Sum(j,b,N)。

固定 `Formula 4` 正好编码 `Balance(w,f,N,i)`；参数映射仅携带w、f、N。`ZFArithmetic.induction` 使用原内部ω归纳与完整Separation，证明AllBalance；最终定理只有Ω、真实History、初始Input及实际HasLength四个对象前提，无剩余归纳假设，不要求外部标准索引。

## 全局历史界与准确边界

对任意i∈d，从实际LengthAt取得a∈ω，AllBalance给Sum(i,a,N)，原自然差分定理给i≤N。由于原History的d=Succ(l)，l∈d，因此末索引l≤N；原自然序的无反向成员性质证明¬(N∈l)，排除过长已接受历史。

这证明每段已经存在的真实历史都满足长度界。完整停止历史的无条件存在仍需下一单元构造，不能仅由有界性或一步追加闭包宣称已完成。

## 实际验收

| 项目 | 实测结果 |
|---|---|
| 新模块／显式声明／闭句模式 | 8／85／13 |
| 定向native构建 | 2198 jobs，通过 |
| 整仓构建 | 2460 jobs，通过 |
| 声明审计 | 26717；无公理 484；允许足迹 26233 |
| 警告／哈希不一致 | 0／0 |
| 验收命令／trust=0 | 9条全部退出0／5条 |
| 全部核心／native模式精确足迹 | 3014组，全部符合 |
| Internal显式声明覆盖 | 24373 |
| 源码SHA256复核 | 2240项全部一致 |
| 既有数学源码及AST | 全部未修改 |
| 既有布尔门 | 全部保持，无false→true迁移 |

13组核心证书足迹恰为propext、Classical.choice、Quot.sound；对应native证书恰为这三项加锁定的原七项native公理证书，不扩展到其他声明。宿主证明证书中的Classical.choice不作为对象AC假设。完整审计前已独立检查全部85个新声明足迹。

原七项锁文件、工具链和依赖固定提交不变。仅新增 `object_Packet_readTokens_all_internal_length_conservation_and_history_bound_proved=true`。旧的“长度界且完整停止历史存在唯一”合取门仍为false，因为后半项尚未证明；完整reader／AST／Proof／Con各旧false门保持。

## 清理与证据

编译前确认Lean／Lake进程为0，无进程需要停止。按工作区.local精确文件白名单删除6个无用临时检查文件及冗余日志，逐项保存SHA256和逻辑字节量，共17644字节。C盘可用空间实测由96982179840变为96982204416字节，不能把既有约90 GiB空间归因于本次小规模清理。依赖、工具链、缓存、其他应用与正式证据保留。

本地验收证据（verification与.local按仓库规则不发布）：

- `verification/packet-reader-length-readback.json`：全部哈希、精确足迹、命令、原文件与布尔门逐项回读，提交后补充Git对象字节证据。
- `verification/summary.json`、`verification/commands.json`、`verification/build.log`、`verification/audit.log`。
- `.local/packet-reader-length-preaudit.json`：新声明在放入native精确允许清单之前的独立足迹。
- `.local/packet-reader-length-precompile-cleanup.json`：逐文件安全清理清单、SHA256及空间实测。

## 后续agent工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、实际输入Cons及完整单步 | 原准确域／类型／联合唯一及四类观察 | 已验收 |
| R3a | 状态码、带码步、独立历史及追加／比较 | 真实零步与追加；全内部共同索引一致及同长度端点唯一 | 已验收 |
| R3b.1 | 实际状态输入投影及逐内部步消费 | 域索引实际唯一有效输入；原Cons消费、严格下降及Nil／拒绝边界 | 已验收 |
| R3b.2a | 原列表长度、无界加法与固定Formula4归纳 | 全内部索引加剩余长度等于初始长度；实际历史全索引及末索引有界；过长接受历史不可能 | 本批已验收 |
| R3b.2b | 内部有界前缀构造及原序列追加 | 停止历史存在唯一；先取得已停止历史或指定内部长度前缀，再以初始长度后继排除过长运行 | 下一单元 |
| R4 | EOF实际逆序、初始化及规范varint分段 | 原acc.reverse与准确返回／拒绝，value／scale／acc顺序对应 | 待完成 |
| R5 | reader、Bytes／Canonical／Tok及原Basic AST | 全内部程序／规格双条件、完整字节包和AST桥，覆盖无效码 | 待完成 |
| P／I／C | 原六规则／27模式、完整ZF／U公理 | 内部Proof／检查／编译、完整解释及原nativeZF内部Con蕴含 | 待完成 |

下一单元用原内部ω归纳取得“已有真实停止历史，或存在指定内部长度的真实前缀”。零步用既有单点历史；后继时对真实末状态有无实际带码后继作对象分支，无后继则停止，有后继则用既有真实图追加。将索引推进到初始长度的后继时，本批长度界排除仍运行分支，从而取得实际停止历史。再以全内部共同索引一致性和原自然序比较证明停止长度／端点唯一。全过程须保留实际图、实际原转移与全部内部索引。

EOF实际acc.reverse、原reader与Bytes／Canonical／Tok的完整程序桥、Basic AST条件翻译、完整内部Proof／解释和最终Con仍单独待完成。总目标保持active。
