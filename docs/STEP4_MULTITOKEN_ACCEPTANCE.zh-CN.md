# 全内部多token编码与原reader输出顺序验收（2026-10-25）

全内部多token编码及原reader顺序消费已验收：独立原双轨迹构造每个有效内部token列表的唯一规范分段编码，精确Nil／Cons方程保留段和token顺序。实际Splice结合律与单元素Snoc合同将反向acc对接最终顺序；固定Formula5经原完整Separation／Foundation消去全部尾码IH。仅Ω与独立Encoded即可取得原Parse(bytes,p)↔Some(tokens,p)，实际128／0／1见证均在对象推导内消去，并联合构造唯一实际字节输入和所有返回候选方程。43模块375声明、25组原nativeZF闭句；2596构建、28220审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。全局字节<256界、带界逆向规范分段、完整程序规格桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 背景与最终目标

对象语言仍为纯EqMem，背景为完整ZF的原呈现（全Separation／Collection）。本批25组闭句均以TheoryTransport.sentence返回原核，再经ZFReplay.replay取得 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。无新公理核、对象Choice、不可达、外部标准ω或模型外部良基假设。静态Fin槽位仅构造对象公式，未充当内部运行数据。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

最终内部Con主句仍未证明。必须继续覆盖全部内部ω（含非标准／无效码）、原六规则／27模式及完整公理模式。编译与本批对象定理均不能替代内部Proof、数学解释及Con证明。

## 独立实际多token编码

PacketTokensBytes的原双轨迹共享内部定义域。原token轨迹从Nil逐格Cons构造token列表；第二轨迹以任意真实seed开始，每行用同一自然数head的独立Canonical varint和实际Splice追加到字节前方。公开Encoded选择实际Nil seed。定义不使用Eval或成功答案，所得方向是 `varint(head) ++ encode(tail)`。

```text
Nil(tokens) → (Encoded(tokens,bytes) ↔ Nil(bytes))
Cons(h,t,tokens) →
  (Encoded(tokens,bytes) ↔
    ∃V R (Canonical(h,V) ∧ Encoded(t,R) ∧ Splice(V,R,bytes)))
Valid(tokens) → ∃bytes ((bytes∈ω ∧ Encoded(tokens,bytes))
  ∧ ∀candidate (Encoded(tokens,candidate) → candidate=bytes))
```

Cons式保留实际head与tail码自然性前提。总性由固定Formula2、真实Cons尾码成员关系和原Separation／Foundation证明，外部较小码IH均已消去。所有候选字节码参与唯一量词；Valid输出是原列表有效性，尚不能称为所有字段<256的ByteList合同。

## 实际累加器与最终token顺序

原Splice的右Nil恒等、结合律、单元素拼接均在对象层证明。单元素追加的长度、全部前缀字段及最后字段满足既有Snoc合同，接入原ReverseConsContract：

```text
Output(A,tokens,O) := ∃R (Reverses(A,R) ∧ Splice(R,tokens,O))
Cons(h,A,A1) ∧ Cons(h,t,ht) ∧ Output(A,ht,O)
  → Output(A1,t,O)
```

因此消费头token实际将其Cons到反向acc，而原token顺序在最终输出中保留；没有用宿主List.reverse或仅语义相等代替实际列表码。

## 固定对象归纳及实际初始化

固定Formula5参数为ω／128／零／单位／token码，性质内部全称量化bytes、acc、最终输出和任意返回候选p。Nil使用准确空输入返回，Cons组合既有完整varint段消费、实际新acc与较小真实tail实例。严格下降来自实际Cons的tail码成员关系；原完整Separation和Foundation关闭全部IH。

```text
Ω ∧ Num128(B) ∧ Empty(z) ∧ Succ(o,z)
 ∧ Valid(tokens) ∧ Valid(A) ∧ Encoded(tokens,bytes) ∧ Output(A,tokens,O)
 → (Eval(bytes,z,o,A,p) ↔ Some(O,p))

Ω ∧ Encoded(tokens,bytes)
 → (Parse(bytes,p) ↔ Some(tokens,p))
```

最后一个定理仅含Ω及独立编码前提。真实Nil累加器满足逆序Nil和左Nil拼接；原InitLiterals接入实际初始状态，128、零和单位见证全部由原对象存在量词构造并消去。Roundtrip.complete联合给出唯一实际编码字节见证及该同一字节见证的所有Parse返回候选方程；p没有额外自然数限制。

## 实际验收

- 全仓构建：2596个任务通过，0警告。
- 公理审计：28220个声明；503无公理、27717仅允许依赖。
- 新增43模块／375个显式声明；25组原核及native闭句对均核对精确依赖。总计3182组精确闭句对，Internal显式覆盖25876。
- 9条验收命令全部exit 0，其中5条--trust=0；2376个工作文件哈希全部回读匹配。
- 全部既有布尔叶保持；最终Con、任意内部Proof正确性和全模式检查仍为false。7个锁文件与YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6及干净依赖树保持。
- 清理前无编译进程，停止0个进程；仅删除11个显式列明的本工程临时／冗余文件，共37500逻辑字节。清理前后磁盘实测分别100148281344／100148326400字节，磁盘差值受其他应用影响。未清除依赖、有效缓存或历史验收证据。清理之后才启动全仓编译。

本地证据：verification/multitoken-readback.json、summary.json、commands.json、build.log、audit.log；.local/multitoken-batch.json、multitoken-preaudit.json、multitoken-precompile-cleanup.json。它们不自动发布。提交后另行核对工作区、Git blob与全部哈希。

## 后续agent友好流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1–R4b.3b.2a | 原reader运行与单varint段 | 实际状态／历史／返回／初始化／完整段消费 | 已验收 |
| R4b.3b.2b | 多token编码与最终输出顺序 | 独立编码全内部存在唯一；Splice与Snoc；固定对象强归纳；初始化Parse精确返回原token | 本批已验收 |
| R4b.3b.2c.0 | 编码输出的全局字节界 | 每个实际编码字段<256，独立ByteList与拼接保持合同 | 下一单元 |
| R4b.3b.2c | 带字节界的成功运行逆向规范分段 | 保留原输入ByteList前提，从实际成功运行提取准确规范分段及唯一性 | 待完成 |
| R5 | readTokens与Bytes／Canonical／Tok | 全部内部码、完整字节包及程序／规格双条件 | 待完成 |
| A／P | 原Basic AST与内部Proof | 原六规则／27模式，完整Separation／Collection与无效内部码 | 待完成 |
| I／C | 对象数学解释与最终内部Con | 对象证明变换与nativeZF中的Con蕴含，核对理论／语言／背景 | 待完成 |


下一批可按下表并行读接口与写隔离新模块，编译及集成由主agent串行完成。表中模块名为计划名，尚无实现验收。

| agent单元 | 先读的实际接口 | 对象交付与工程边界 | 验收入口 |
|---|---|---|---|
| ByteBound拼接 | StructuralListSplice.cons_iff、PacketByteInputLaws.actual_iff、原列表字段 | 仅新SpliceByteBound模块；固定对象性质、真实tail码下降，任意字段界 | 新native闭句及全部内部字段候选 |
| ByteBound编码 | PacketTokensBytes.cons_iff、PacketVarintExecutionLiterals.byte_input、SpliceByteBound | 仅新PacketTokensByteBound模块；Encoded→ByteList，保留全部实际候选 | 原核闭句、公理精确清单 |
| 逆向单段 | 原Reader Advance／Eval、字节<256、Canonical递归 | 先固定原字节前提和成功返回合同；拒绝分支与EOF失败排除逐项入核 | 全内部单段分解与唯一性 |
| 逆向多段 | 本批编码精确Cons式与输出顺序、逆向单段 | 成功实际运行→独立Encoded，消去较短列表IH；不以成功定义编码 | 初始化双向程序／规格桥 |
| Bytes／Tok对接 | 原锁定源码与独立Bytes／Canonical／Tok | 证明实际拼接与原编码的对象等价，完整无效码量词保持 | 完整包与所有候选精确守卫 |
| Basic／Proof／Con | SOURCE_RULES_LOCK、SOURCE_THEORY_LOCK、OBJECT_TARGET | 原六规则／27模式、全模式、公理判断与证明变换；最终原Con蕴含 | Derives nativeZF [] 的最终主句 |

下一批固定归纳合同已核对：Splice字节界取 `P(w,C) := ByteList(C) → ∀T L (ByteList(T) → Splice(C,T,L) → ByteList(L))`；编码字节界取 `Q(w,n) := ∀bytes (Encoded(n,bytes) → ByteList(bytes))`，各为Formula2。Nil用拼接等号与 `PacketVarintExecutionHelpers.nil_input`；Cons用真实tail码成员关系，`PacketVarintExecutionHelpers.cons_input` 重建完整字节guard。两者都以各自matrix.neg的完整Separation及原Foundation消去IH，无新增256数码见证前提。

每批先定向 `lake build <新公开模块>`；再为全部新声明生成 `#print axioms` 并以 `lake env lean --trust=0 <审计文件>` 检查；确认原核／native精确依赖后才加入允许清单、PPAC、Audit和CheckStep4。清理显式临时文件并确认无工作区编译器后，运行 `python scripts/verify.py`，回读九命令／五trust=0、全部哈希、旧布尔变化及源码／依赖锁，最后精确提交并回读Git blob。所有Lean/Lake串行且LEAN_NUM_THREADS=1。

下一单元先建立实际Splice上的ByteList保持及Encoded的每字段<256界。逆向证明严格保留原ByteList前提，随后接入完整Bytes／Tok规格；本批不翻转复合的逆向／完整程序桥或Proof／Con门。
