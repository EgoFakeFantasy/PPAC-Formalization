# 原reader初始化与终止方程对象验收（2026-10-25）

原reader初始化与空输入精确方程已验收：真实初始字段为input／0／1／Nil，原Nil码恰为内部一；实际128、零、一和初始状态码均在对象量词内构造并消去。仅Ω与实际输入有效性即可取得初始化reader的对象EX／ALL唯一返回纤维，返回存在域准确等于有效输入；真实零步历史证明原终止方程及空输入准确返回Some实际Nil。9模块136声明、21组原nativeZF闭句；2512构建、27470审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。varint分段／输出顺序、完整程序桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 背景理论、原源码与最终目标

纯EqMem与完整ZF、原完整Separation／Collection不变。21组闭句模式的终点均为原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`，经既有 `TheoryTransport.sentence` 与 `ZFReplay.replay` 回放，没有新推导核、对象Choice、不可达或外部标准ω假设。

核对固定YesMetaZFC源码 `Logic/FirstOrder/FormalSystem/Metatheory/ProofT/NatPacket.lean`：decode调用readTokens bytes 0 1 []；readTokens的空输入分支检验scale=1且value=0，返回acc.reverse。该源码提供要迁移的实际程序行为；本批证明的是下面的对象初始化、真实历史终止方程及空输入方程，尚未建立完整宿主程序编译桥。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

最终主句仍未证明。完整内部Proof覆盖全部内部ω（含非标准和无效码）、原六规则／27模式及完整公理模式，不能由初始化正确性替代。固定依赖仍为039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作树及七个既有锁文件均保持。

## 实际初始状态与所有见证的对象消去

```text
Seed(w,z,o,L,n) = StateCode(w,L,z,o,o,n)
Seeded(w,B,z,o,L,q) = ∃n (Seed(w,z,o,L,n) ∧ Run(w,B,z,o,n,q))
Parse(w,L,q) = ∃B,z,o (Numeral128(B) ∧ Empty(z) ∧ Succ(o,z) ∧ Seeded(w,B,z,o,L,q))
```

原Nil实际码恰为内部一，因此四字段input／value／scale／acc的真实初值是L／z／o／o。Empty(z)和Succ(o,z)下，原零／后继自然性、原Nil有效轨迹和输入有效性构造真实State；既有原四格forest编码存在性构造实际状态码n，码自然且唯一。没有把宿主空列表或宿主数值当对象码。

每个实际初始码都使Seeded精确归一为原真实历史Run；任意两个初始码先由原编码唯一性对齐，再用Run唯一性比较任意返回候选。Seeded的返回存在域恰为实际有效输入，不要求预先给出n、历史、终止性或归纳假设。

原静态Numeral128见证和内部零／一通过对象存在性取得。不同见证的B、z、o分别由原Numeral唯一、空集外延唯一和后继唯一性对齐；原对象相等代换同时替换Run及初始字段。Parse没有保留外部B／z／o／初始码参数。

```text
Ω(w) → (Valid(w,L) ↔ ∃q (q∈w ∧ Parse(w,L,q)))
Ω(w) ∧ Valid(w,L)
  → ∃q ((q∈w ∧ Parse(w,L,q)) ∧ ∀s (Parse(w,L,s) → s=q))
```

全部内部输入列表和全部输出候选参与对象量词，包含非标准长度；无效候选输入不会被默认成返回None。本批是原readTokens的无界自然数列表输入关系，未额外施加字节上界；完整decode的实际字节包及Bytes／Canonical规格对应仍待证明。

## 真实零步历史与精确终止方程

固定实际EOF成功及实际逆序载荷u后，原局部Return(q)在所有q上准确等价于Some(w,u,q)，无需先假设q是Some。固定原拒绝后，Return(q)准确等价于None(w,q)。证明通过三类原原因互斥、实际逆序唯一与原forest载荷相等代换，而非只比较返回标签。

原单点序列真实构造零步History(n,n,z,o,f)，然后与末状态的实际返回组合。对于任意实际状态码及原三类终止观察，整段Run(n,q)精确等价于局部Return(q)。该方程的历史f在对象存在量词中构造并消去；正向由无后继和真实停止末码唯一性排除其他末点。

空输入的初始State满足原EOF成功守卫。原Nil逆序为原Nil，固定局部返回方程给Some实际Nil，并经真实零步历史传输为整个Seeded方程。进一步消去全部常数见证，并用原Nil／Some唯一性，得到不含B／z／o的闭句模式：

```text
Ω(w) ∧ Nil(w,L) ∧ Nil(w,u) → (Parse(w,L,q) ↔ Some(w,u,q))
```

q可以是任意候选，未预设其为Option码。此处只完成原终止递归基例，非空输入的完整递归／分段不变量与程序规格等价仍未完成。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句模式 | 9／136／21 |
| 定向native构建 | 2247 jobs通过 |
| 全仓构建 | 2512 jobs通过 |
| 声明审计 | 27470；无公理485；允许足迹26985 |
| 警告／哈希不一致 | 0／0 |
| 验收命令／trust=0 | 9条全部退出0／其中5条 |
| 全部核心／native精确证书对 | 3119 |
| Internal显式声明覆盖 | 25126 |
| SHA256独立回读 | 2292项一致 |
| 原数学源码、AST、理论／信任／构建锁文件 | 保持 |
| 全部旧布尔叶 | 保持，无变化 |

21组核心足迹准确为propext、Classical.choice、Quot.sound；native足迹准确为这三项加原锁定七项。136声明在加入native精确允许清单前已独立预审计，没有放宽其他声明；宿主证明证书中的Classical.choice不作为对象AC假设。只新增object_actual_reader_initialization_literals_input_domain_and_empty_equation_proved=true；组合初始化／分段旧门仍为false，因为分段尚未完成。完整程序桥、Basic AST、内部Proof及Con保持未完成。

## 清理、证据与后续流程

编译前确认Lean／Lake为0，无需终止进程。精确.local白名单删除11个被替代的生成脚本、驱动、检查片段及失败／冗余日志，共44367逻辑字节，保留逐文件路径／大小／SHA256。C盘空间实测由102455750656至102455808000字节，逻辑删除量与系统即时变化分别记录；工具链、依赖、正式证据及其他项目未动。

本地证据不发布：verification/packet-reader-init-readback.json、summary.json、commands.json、build.log、audit.log；.local/packet-reader-init-preaudit.json与preaudit.log、packet-reader-init-precompile-cleanup.json。提交后复核所有工作文件哈希、Git原始字节及干净状态。

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、真实Cons与带码单步 | 实际字段、准确域及联合唯一 | 已验收 |
| R3／R4a | 实际历史、停止与原终止观察 | 全内部长度界、完整停止历史联合唯一及三原因互斥穷尽 | 已验收 |
| R4b.1／.2 | 实际逆序与EOF／运行返回 | 真实逆序图、Some／None精确值、实际运行域及对象唯一纤维 | 已验收 |
| R4b.3a | 原初始化与终止递归基例 | 实际128／0／1／Nil与初始状态码消去、准确输入域、空输入方程 | 本批已验收 |
| R4b.3b | 全内部varint分段与输出顺序 | 实际value／scale／acc不变量、内部段消费、已发射token与输出顺序 | 下一单元 |
| R5 | readTokens与Bytes／Canonical／Tok | 全内部程序／规格双条件，所有无效候选和实际字节包覆盖 | 待完成 |
| A／P | 原Basic AST与内部Proof | 六规则／27模式、完整Separation／Collection及全部内部码 | 待完成 |
| I／C | 对象数学解释与最终内部Con | 原理论／语言／假设核对、证明变换、nativeZF中的Con蕴含 | 待完成 |


下一单元需连接真实历史的前后缀／分段与varint递归，证明value／scale／acc在全内部索引上的消费和输出顺序。只有实际Run与独立Canonical／Bytes／Tok形成完整双条件，才能关闭完整reader程序桥；其后仍需原Basic AST、内部Proof、完整解释及最终对象Con。
