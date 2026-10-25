# 原内部列表实际逆序对象验收（2026-10-25）

原内部列表实际逆序图已验收：反向索引满足原无界i+j+1=l，全部内部位置都有唯一对称且在域内的反向索引；原Replacement构造精确反向字段图，原序列编码构造真实原列表码。所有内部有效列表均有唯一逆序码，保长度／有效性，字段准确反向，对称且逆序两次还原；原Nil与Cons／唯一尾追加的双条件均已证明。16模块187声明、23组原nativeZF闭句；2491构建、27146审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。EOF返回分支连接、完整reader程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 对象理论与完整目标

纯EqMem语言、完整ZF与完整Separation／Collection不变。23组闭句证书返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`，由既有 `TheoryTransport.sentence` 与 `ZFReplay.replay` 传输。没有新推导核、对象Choice、不可达、外部标准ω或模型外部良基假设；没有使用宿主List.reverse、运行时宿主Nat递归或宿主选择函数生成数据。静态Fin槽位等式只用于固定有限公式绑定器构造。

YesMetaZFC固定提交为 `039c8e132cc19671d73a3933c66b4799d2599dd6`，依赖工作树干净。最终对象主句保持：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

完整内部Proof须核验全部内部ω（含非标准与无效码）、原六规则／27模式及完整公理模式。EOF程序连接、完整内部Proof／解释与最终Con仍未证明。

## 全内部反向索引及字段

```text
Mirror(w,l,i,j) = i∈w ∧ j∈w ∧ ∃p (p∈w ∧ Sum(w,i,j,p) ∧ Succ(l,p))
ReverseValue(w,n,l,i,y) = ∃j (Mirror(w,l,i,j) ∧ Field(w,n,j,y))
```

Mirror准确表示i+j+1=l，使用原无界加法和后继。对全部内部i∈l，原ω后继分解取得l的实际前驱p，原差分存在性构造j；原加法交换、后继注入及差分唯一性给对称、唯一和双向域界。不存在外部最短索引或标准性假设。

ReverseValue中的j是对象存在量词，实际原Field给自然输出及全候选单值性；Mirror唯一性对齐所有可能反向索引。因此所有内部域索引有实际唯一反向字段。

固定Formula5将反向字段关系交给原Replacement／RelationGraph接口，构造完整Kuratowski函数图，证明其精确全边律、ω值域及图集合唯一性。源码n可以是任意候选；最终逆序关系另以真实HasLength要求实际原有效列表，不把任意默认字段图当有效列表。

## 原列表码上的实际逆序存在唯一

```text
Reading(w,n,l,r) = ∀i∈l ∀y (Field(w,r,i,y) ↔ ReverseValue(w,n,l,i,y))
AtLength(w,n,l,r) = HasLength(w,n,l) ∧ HasLength(w,r,l) ∧ Reading(w,n,l,r)
Reverses(w,n,r) = ∃l (l∈w ∧ AtLength(w,n,l,r))
```

原HasLength保留完整真实构造轨迹，原Field是实际tail迭代后的原head读取。原完整序列编码定理将精确反向字段图构造成实际原列表码r；完整解码图与精确图的全边双条件给Reading。长度、字段图、实际码均在对象存在量词内消去。

对任意两个候选逆序码，原列表长度唯一性先对齐长度；两套Reading给全部域内字段一致，原完整字段列表码注入性最终给r=s。对象EX／ALL纤维证明：Ω与Valid(w,n)即可取得唯一实际逆序码，所有可能输出候选均参与比较。Reverses本身推出源与输出实际有效及共同真实内部长度。

## 精确反向字段、还原及Nil／Cons递归

每个实际Mirror(w,l,i,j)都把整个ReverseValue存在块准确归一为原Field(w,n,j,y)。因此实际逆序的输出字段与原反向位置字段满足全输出候选双条件。Mirror对称和全内部存在性给逆序关系对称，再结合唯一性证明逆序两次还原，覆盖任意内部及非标准长度。

原Nil输入的逆序准确等价于原Nil输出。原Cons情形使用完整字段定义实际尾追加码：

```text
Snoc(w,u,l,L,h,r) = HasLength(w,u,l) ∧ HasLength(w,r,L) ∧ Succ(L,l)
  ∧ (∀i∈l ∀y (Field(w,r,i,y) ↔ Field(w,u,i,y)))
  ∧ Field(w,r,l,h)
```

Snoc要求真实原列表码、全部前缀字段及真实末头字段。原ω域分解与原完整字段注入性证明该输出码唯一。若Cons(w,h,t,n)、HasLength(w,t,l)、Succ(L,l)及Reverses(w,t,u)，则对象推导给：

```text
Reverses(w,n,r) ↔ Snoc(w,u,l,L,h,r)
```

正向通过实际反向索引增长、原Cons零／后继字段律取得所有前缀字段及末尾原头；反向先构造真实逆序码，再用Snoc的原码唯一性对齐任意候选输出。此为实际代码双条件，不把一份外部列表递归定义当作已证事实，也没有保留未消去的存在性归纳假设。

本批完成独立逆序原语。EOF通过时的实际返回值连接、EOF失败／字节拒绝的准确返回、原初始化／分段不变量及完整readTokens程序桥仍待下一阶段，不能把独立逆序原语等同于整个程序已证明。

## 实际验收

| 项目 | 实测结果 |
|---|---|
| 新模块／显式声明／原闭句模式 | 16／187／23 |
| 定向native构建 | 2226 jobs，通过 |
| 整仓构建 | 2491 jobs，通过 |
| 声明审计 | 27146；无公理 485；允许足迹 26661 |
| 警告／哈希不一致 | 0／0 |
| 验收命令／trust=0 | 9条全部退出0／5条 |
| 全部核心／native精确足迹 | 3071组符合 |
| Internal显式声明覆盖 | 24802 |
| SHA256独立回读 | 2271项全部一致 |
| 既有数学源码、AST、七个锁文件 | 全部未改 |
| 所有旧布尔叶 | 全部保持，无false→true变化 |

23个核心证书的足迹恰为propext、Classical.choice、Quot.sound；native证书恰为这三项加原锁定七项native证书。未放宽到其他声明，没有新公理。宿主证明证书中的Classical.choice不作为对象AC假设。全部187声明在加入native精确允许清单之前已独立核查足迹。

仅新增 `object_actual_internal_list_reversal_exists_unique_Nil_Cons_proved=true`。EOF返回连接、reader程序桥、Basic AST、内部Proof／解释与最终Con的旧false门保持。

## 清理和本地证据

编译前确认Lean／Lake进程为0，无需终止进程。按.local精确文件白名单删除10个失败／冗余日志及临时检查文件，保存逐文件SHA256，共50020逻辑字节。C盘可用量实测由102650507264变为102650572800字节，分别记录逻辑删除与系统即时空间变化；依赖、工具链、缓存、其他应用及正式证据保留。

本地验收材料按仓库规则不发布：

- `verification/structural-list-reverse-readback.json`：全部SHA256、精确足迹、原布尔门、命令及提交后Git对象字节复核。
- `verification/summary.json`、`verification/commands.json`、`verification/build.log`、`verification/audit.log`。
- `.local/structural-list-reverse-preaudit.json`：加入允许清单前的187声明独立足迹。
- `.local/structural-list-reverse-precompile-cleanup.json`：逐文件清理及空间实测。

## 后续agent工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、实际Cons与完整单步 | 原准确域／类型／联合唯一及四类观察 | 已验收 |
| R3 | 原状态码、真实历史及追加／比较、内部长度归纳 | 全内部消费与长度界；实际停止历史存在及末码／长度／域／图联合唯一 | 已验收 |
| R4a | 真实停止原因 | EOF通过／失败／实际字节拒绝互斥穷尽；带分类完整历史存在唯一 | 已验收 |
| R4b.1 | 原有效内部列表的实际逆序 | 原镜像索引／精确图／实际码存在唯一；保长度、反向字段、还原及Nil／Cons-snoc双条件 | 本批已验收 |
| R4b.2 | 真实EOF返回与拒绝 | EOF通过取得实际逆序输出及唯一返回；EOF失败／字节拒绝给准确拒绝 | 下一单元 |
| R4b.3 | 原初始化与规范varint分段 | 原value／scale／acc及输入、输出顺序不变量，全部内部码覆盖 | 待完成 |
| R5 | reader、Bytes／Canonical／Tok及原Basic AST | 全内部程序／规格双条件、完整字节包及AST桥，覆盖全部无效码 | 待完成 |
| P／I／C | 原六规则／27模式、完整ZF／U公理 | 内部Proof／检查／编译、完整数学解释及原nativeZF内部Con蕴含 | 待完成 |

下一单元从EOFSuccess中的真实State取得有效acc，直接应用本批实际逆序纤维取得对象返回码及唯一性，证明成功返回图准确域；EOF守卫失败与实际字节拒绝排除成功返回。随后连接真实停止历史与实际末字段、原初始化及规范varint分段不变量，再完成Bytes／Canonical／Tok／Basic AST和最终内部Proof／解释／Con。总目标保持active。
