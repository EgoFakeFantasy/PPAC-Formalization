# 全内部完整单varint段对象验收（2026-10-25）

全内部单个规范varint段消费已验收：独立实际Cons双轨迹给精确拼接，任意两个有效内部列表都有唯一实际拼接码。固定Formula5经原完整Separation和Foundation消去所有较小token归纳假设，任意自然数尾输入、value／scale／acc下得到完整段Eval双条件；保留原尺度等于单位或token非零守卫，允许零尺度，未添加尾输入字节界。实际拼接输入被构造且对所有返回候选成立。30模块239声明、17组原nativeZF闭句；2553构建、27845审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。多token分段／输出顺序、带字节界的逆向规范性、完整程序规格桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 原核、背景理论与未完成的最终主句

纯EqMem、完整ZF及完整Separation／Collection保持。17组闭句模式经TheoryTransport.sentence与ZFReplay.replay返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。没有新核、对象Choice、不可达、外部标准ω或模型外部良基假设；模式构造的静态有限Fin槽位不作为内部执行数据。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

该最终内部主句仍未证明。内部Proof还须核验全部内部ω（含非标准／无效码）、原六规则／27模式和完整公理模式；本批不能替代完整解释及内部Con。YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6、依赖工作树及七个既有锁文件保持。

固定源码NatPacketRoundtrip.readTokens_varint要求scale≠1时token≠0，允许任意自然数尾输入、value、scale和acc。本批保留等价对象守卫s=o∨¬Empty(n)，没有擅加正尺度、标准性或任意尾输入的字节上界。逆向readTokens_prefix／inverse确实要求所有字节<256，列为后续有前提的证明任务。

## 独立真实列表拼接及其对象总性

Splice(w,C,T,L)含Valid(T)、Valid(L)，并保存两张相同内部长度／定义域的实际序列图。第一图以原Nil开始并逐格Cons构造C，第二图以T开始，每行使用同一个自然数head逐格Cons构造L；所有内部行都检查两组真实Cons。其定义没有Eval、运行答案或宿主List.append，方向准确为L=C++T。

原序列append／prefix限制构造和反演给精确Nil／Cons式：

```text
Nil(C) → (Splice(C,T,L) ↔ (Valid(T) ∧ T=L))
Cons(h,X,C) → (Splice(C,T,L) ↔ ∃Y (Splice(X,T,Y) ∧ Cons(h,Y,L)))
```

Cons式保留实际h与X的自然性要求；所有候选T、L都参与量词。反演从Valid(L)与实际Cons取得Valid(Y)，保留Valid(T)，没有把自然码误当有效列表。

固定Formula2以实际前缀码作内部强归纳索引。原有效列表分解和Cons尾码严格属于前缀码取得真正下降，原Cons构造存在性和输出注入性给后继纤维，原完整Separation(matrix.neg)与Foundation消去全部IH：

```text
Ω(w) ∧ Valid(w,C) ∧ Valid(w,T)
  → ∃L ((L∈w ∧ Splice(w,C,T,L)) ∧ ∀M (Splice(w,C,T,M) → M=L))
```

因此拼接并非仅有关系AST或条件递归，所有有效内部列表实际都有唯一拼接码，包括非标准长度。候选唯一性不预设M自然或有效；Splice自身保证实际有效性。

## 原继续字节算术与真实单步

```text
n=d+B*k, v1=v+d*s, S=s*B
  ⇒ (u=v+n*s ↔ u=v1+k*S)
```

这些等式均用原无界Product／Sum／Equation对象关系表示，乘积与和见证在对象存在量词内取得并消去。原乘法交换、结合、分配和加法结合证明组合；原输出唯一性与实际算术总性证明反向。尺度可为零，digit无需额外小于尺度。

终止字节b<B满足原守卫时，实际Cons头、原发射Eq和实际累加器Cons连接到前批Eval递归方程，得到重置value／scale并把真实token加入反向acc的精确求值式。继续字节h=d+B时，原差值关系给实际更新v1和S；实际Cons消费连接到更新后的Eval，保留任意自然尾输入。

## 全内部完整规范段消费

Canonical(w,n,C)是既有独立零种子规范LEB128实际列表轨迹。定义固定Formula5 property(w,B,z,o,n)，在对象内全称量化C、T、L、v、s、a、u、c、p九个变量：

```text
Canonical(w,n,C) ∧ Splice(w,C,T,L) ∧ State(w,T,v,s,a)
∧ (s=o ∨ ¬Empty(n)) ∧ Eq(w,n,v,s,u) ∧ Cons(w,u,a,c)
  → (Eval(w,B,z,o,L,v,s,a,p) ↔ Eval(w,B,z,o,T,z,o,c,p))
```

小情形Canonical给实际单字节前缀，精确拼接Nil／Cons式将输入归一为Cons(n,T,L)，应用原终止字节式。大情形取得实际商k≠0、digit d和头d+B；原quotient_bounds证明k∈n，原全称较小性质仅在这个真实内部下降处实例化。实际中间value和scale在对象EX中构造，算术分解得到较小段最终u；k≠0直接给递归守卫，即使新尺度为零也成立。

固定Formula5的progressive经原完整Separation与Foundation闭合，全部较小token IH已消去。最终单段模式只保留Ω、实际Numeral128(B)、Empty(z)、o∈ω及上式的原输入／守卫／算术条件。原具体单位一可按前批初始化规格实例化，参数o的自然性允许更一般的形式程序。

进一步由拼接总性实际构造唯一L，并在对象内全称量化全部返回候选p；`PacketReaderVarintConsumption.exists_unique`的结论同时保存L自然、真实Splice、全输出消费式和对所有拼接候选的唯一性。没有外部提供拼接码、分段长度、执行历史或未消去IH的要求。

本批完成正向单个完整varint段。多token顺序、带字节界的成功运行逆向规范分解、完整Bytes／Canonical／Tok程序规格桥及原Basic AST仍未完成，不能把单段方程当完整数据包或最终内部Con。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句模式 | 30／239／17 |
| 定向native构建 | 2288 jobs通过 |
| 全仓构建 | 2553 jobs通过 |
| 声明审计 | 27845；无公理503；允许足迹27342 |
| 警告／SHA256不一致 | 0／0 |
| 验收命令／trust=0 | 9条全部退出0／其中5条 |
| 全部核心／native精确证书对 | 3157 |
| Internal显式声明覆盖 | 25501 |
| 全部哈希独立回读 | 2333项一致 |
| 原数学源码、AST及既有锁文件 | 保持 |
| 全部旧布尔叶 | 保持，无变化 |

17组核心足迹准确为propext、Classical.choice、Quot.sound；native准确为这三项加原锁定七项。239个声明在扩展允许清单前已独立预审计，没有放宽其他声明；宿主证明证书中的Classical.choice不作为对象AC。仅新增object_all_internal_single_varint_segment_consumption_with_unique_actual_splice_proved=true；旧多token／输出顺序组合门及完整程序桥、Basic AST、Proof、Con保持未完成。

## 清理、证据及后续流程

编译前Lean／Lake为0，终止0；精确.local白名单删除12个被替代的生成脚本、临时驱动、检查片段及失败／冗余日志，共66489逻辑字节，保存逐文件路径／大小／SHA256。C盘可用空间由100660781056至100660871168字节，逻辑删除与系统即时净变化分别记录。正式源代码、验收证据、工具链、依赖及其他工程保持。

本地证据不发布：verification/varint-segment-readback.json、summary.json、commands.json、build.log、audit.log；.local/varint-segment-preaudit.json与preaudit.log、varint-segment-precompile-cleanup.json。提交后再次核对全部哈希、Git原始字节及干净状态。

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1–R4b.3b.1 | 原状态、真实历史、停止、返回、初始化与递归 | 原核实际码、全内部运行唯一纤维、Advance／Terminal方程 | 已验收 |
| R4b.3b.2a | 任意实际尾表上的完整单varint段 | 精确拼接存在唯一；原算术组合；固定对象强归纳消去全部IH；所有输出候选消费方程 | 本批已验收 |
| R4b.3b.2b | 多token分段及输出顺序 | 内部token序列、真实反向acc与最终顺序、完整段组合 | 下一单元 |
| R4b.3b.2c | 逆向规范分段 | 原输入字节<256前提下，成功运行推出规范段分解及唯一性 | 待完成 |
| R5 | 原readTokens与Bytes／Canonical／Tok | 完整字节包、所有无效内部候选及程序／规格双条件 | 待完成 |
| A／P | 原Basic AST与内部Proof | 原六规则／27模式、完整Separation／Collection与全部内部码 | 待完成 |
| I／C | 对象数学解释与最终内部Con | 理论／语言／背景核对、对象证明变换及nativeZF中的Con蕴含 | 待完成 |


下一单元用单段式和实际拼接唯一性组合内部token序列，精确保持反向acc与最终输出顺序；随后在正确字节界下证明成功运行的规范段反演及唯一性，再完成原程序与Bytes／Canonical／Tok的完整对应。之后仍需内部Basic AST、Proof及完整数学解释，最终交付nativeZF内部Con蕴含。
