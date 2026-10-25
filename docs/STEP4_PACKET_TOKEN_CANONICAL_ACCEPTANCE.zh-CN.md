# 原对象Tok与独立规范字节Prefix全内部对应验收（2026-10-25）

原对象Tok与独立规范字节Prefix的全内部双条件已验收：同一实际Cons的Bytes尾执行准确分解，经真实字段自然性及原注入性对齐；独立Prefix取得准确终止／延续递归。固定Formula2比较全部内部tail／output，原严格商下降、Foundation及完整Separation消去全部IH，128／256见证对象消去。最终仅Ω取得ALL3 Tok↔Prefix，并对任意实际规范列表取得Tok↔该列表Bytes。12模块115声明、13组原nativeZF闭句；2407构建、26032审计、零警告，九命令／五trust=0通过。Tok对应顶层及三个旧guard子门false→true，其余旧布尔叶保持。原readTokens累加器／scale程序桥、Basic AST、完整字节包、schema、Proof／解释及最终Con仍未完成。

## 对象合同与完整目标

对象语言保持原单排序等号／成员语言，背景是Contract.nativeZF及完整Separation／Collection，正式证书返回原YesMetaZFC.Logic.FirstOrder.Derives。没有新对象Choice、不可达假设、新推导核或内部ω标准性假设。原Packet十规则、Tok／Canonical／Bytes／Prefix定义和全部旧跟踪PPAC证明及AST保持原样。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

完整内部Proof仍须覆盖全部内部ω、非标准及无效码、原六规则／27模式和完整公理模式。内部checker、数学解释及上述最终Con对象定理仍未证明。本批对应的是原Packet规则表的对象Tok接受；没有把它等同于宿主NatPacket.readTokens程序已经形式化。

## 定义保持与精确对象结果

```text
Tok(w,n,t,a) := ∃r (OriginalTagRow(2,w,n,t,a,r) ∧ PacketCondition(w,r))
Prefix(w,n,t,a) := ∃s (Canonical(w,n,s) ∧ Bytes(w,s,t,a))
```

Tok沿用原tag2行和原Packet条件的独立定义。Canonical沿用原零seed双序列图和非空原列表，Bytes沿用原有序字节fold双图。Prefix的定义没有引用Tok；本批是在这四个既定独立公式之间证明对应。

```text
ZF ⊢ Ω(w) → ∀n,t,a (Tok(w,n,t,a) ↔ Prefix(w,n,t,a))
ZF ⊢ Ω(w) → Canonical(w,n,s) →
       (Tok(w,n,t,a) ↔ Bytes(w,s,t,a))
```

第一式有标量和实际ALL3版本；n、t、a量化全部内部集合候选，包括无效及非标准码。没有外加n、t、a自然性、较小IH、图、列表码、根行、字节末步或数词见证前提。第二式对每一份实际规范列表成立，依赖已经证明的规范列表唯一性；没有选择一个宿主列表代表内部规范列表。

## 同一Cons的真实Bytes分解

给定实际Cons(w,h,x,s)及h、x自然性，正式证明：

```text
Ω(w), h∈w, x∈w, Cons(w,h,x,s) ⊢
  (Bytes(w,s,t,a) ↔ ∃u (Bytes(w,x,t,u) ∧ ActualAffine256(w,h,u,a)))
```

从Bytes准确递归取得任意实际Cons(d,y,s)时，先从真实256末步推出Byte(d)进而d∈ω，从真实尾Bytes推出y∈ω。随后原Cons注入性给h=d、x=y，原对象等号替换对齐尾输入及实际末步digit。Nil分支由原Nil／Cons不相容排除。没有把任意未带守卫Cons的字段视为自然数。

当x为原Nil，真实尾Bytes值定理给t=u；实际末步tail经原等号替换对齐，取得单字节执行的准确末步。反向使用原Bytes Cons构造律。全部EX3／EXu见证对象消去。

## 独立Prefix的准确递归

实际B=128、C=256时：

```text
Small(w,B,C,n,t,a) := n∈B ∧ Affine(w,C,n,t,a)
Large(w,B,C,n,t,a) := ∃d,q,u,h (
  Affine(w,B,d,q,n) ∧ ¬Empty(q) ∧ Sum(w,d,B,h) ∧
  Prefix(w,q,t,u) ∧ Affine(w,C,h,u,a))

ZF ⊢ Ω(w) → Num128(B) → Num256(C) →
       (Prefix(w,n,t,a) ↔ (Small(w,B,C,n,t,a) ∨ Large(w,B,C,n,t,a)))
```

该准确递归有全内部ALL3版本，Num128／Num256在这个辅助版本中明确保留。正向先从Canonical的完整递归取得单元素／EX4延续分支，再把同一Cons上的Bytes准确分解对齐。终止分支给真实字节末步；延续分支的真实较小Canonical和尾Bytes在同一内部列表码上构成真实较小Prefix。实际末步与算术仿射式由原PacketAffineAccepted双条件对齐。反向直接使用前批实际Prefix终止／延续构造律。没有使用Tok来证明这组独立Prefix递归。

## 对象归纳取得原Tok对应

```text
Agreement(w,n,t,a) := Tok(w,n,t,a) ↔ Prefix(w,n,t,a)
P(w,n) := ∀t,a Agreement(w,n,t,a)
matrix : Formula 2 := P(0,1)
Earlier(w,n) := ∀q (q∈w → q∈n → P(w,q))
```

原Tok的完整算术递归和独立Prefix的递归保留相同Small、EX4、非零商、base128仿射、移位加法及base256末步。只有递归位置分别为Tok或Prefix。每份实际EX4分支先用原仿射守卫给q∈ω，再用实际非零商及原quotient_bounds给q∈n，然后实例化Earlier到任意内部tail及中间输出，双向传输较小接受关系。其余全部算术见证和守卫保持原样。

由原BoundedInduction.induction_on_set、Foundation和完整Separation(matrix.neg)消去全部内部IH。内部构造并消去128／256，得到仅Ω下全部自然输入的P。最后从实际Tok原行环境或实际Prefix数值域取得n∈ω，将结论扩展为全部候选上的标量及ALL3双条件；无效输入没有被外部预先过滤。

给定任意实际Canonical(w,n,s)，Tok正向先给Prefix，其内部另一份规范列表码由已证Canonical唯一性与s对齐，再用原Bytes输入等号替换；反向把给定Canonical和Bytes组合为Prefix，再转回Tok。

## 模块与实际验收

| 模块 | 原核对象工作 |
|---|---|
| PacketBytesConsSyntax／Cons | 同一原Cons的真实字段自然性、注入性对齐、准确尾执行和单元素末步 |
| PacketVarintPrefixRecursionSyntax／Small／Large／Equation | 独立Prefix完整算术递归及ALL3，全部列表／尾执行见证消去 |
| PacketTokenCanonicalSyntax／Step | 固定Formula2、所有内部tail／output比较、原商下降及完整EX4双向对齐 |
| PacketTokenCanonicalInduction／Literals | 原Foundation／Separation归纳与128／256内部见证消去 |
| PacketTokenCanonicalLaws | 仅Ω的全候选Tok↔Prefix、ALL3及给定规范列表上的Tok↔Bytes |
| ObjectPacketTokenCanonical | 13组Source闭句经TheoryTransport.sentence及ZFReplay.replay进入原nativeZF |

- 定向原native构建2151任务成功；全仓2407任务成功。九命令全部退出0，五个--trust=0入口通过，零警告。
- 新增12模块115声明先独立trust=0预审计，确认精确依赖后才接入正式Audit、CheckStep4及受限native名单。累计26032审计，475无公理、25557仅含允许的记录依赖。
- 13组core足迹恰为propext／Classical.choice／Quot.sound，native恰额外继承原ZF七项固定闭句证书；原choice专用桥范围不变。没有新native_decide、自定义axiom、对象公理、宿主eval、预算提高或linter豁免。
- 2187份文件SHA256回读一致，2922对精确core／native足迹，23688项Internal显式声明覆盖。七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净。全部旧跟踪PPAC证明和四个独立定义保持。
- 独立readback递归比较全部旧布尔叶：仅Tok↔独立Prefix顶层门及三个旧guard对应子门false→true，其余旧值保持。原readTokens／完整varint程序桥、Basic AST、完整byte-tree、schema、Proof及Con保持未完成。

验收基点0c4a65caedf199ef6159b1b318ea16bade43e4e3，本批12个Lean模块、4个接入文件及6份文档。证据见verification/summary.json、commands.json、build.log、audit.log、packet-token-canonical-readback.json及.local/packet-token-canonical-preaudit.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py；仅本地提交。

## 清理后继续编译

本批定向修复了三处工程错误：重命名仍引用旧accepted_rename，改用prefixCode_rename；ZFContext.add的未定占位改为明确Small公式；字面量模块的归纳引理改为完整命名空间。没有改变数学前提、提高预算或禁用linter。预审计及接入后确认Lean／Lake进程0、停止0；按绝对路径及非reparse普通文件逐一校验，清理已并入Audit的临时驱动、已并入CheckStep4的片段和三份被成功结果取代的失败日志，共5文件、逻辑22991字节；即时可用空间增加32768字节。清理后约90.57 GiB，再串行全仓验收。路径／大小／SHA256见.local/packet-token-canonical-precompile-cleanup.json。有效源码、工具链、依赖、缓存、成功日志与有复现作用的脚本保留，没有停止其他应用或服务。

## 后续agent工程流程表

| 顺序 | 具体实现与依赖 | 必须交付的原核对象结果 | 状态 |
|---|---|---|---|
| T1.2c.3e.1d.2b.1-4a | 独立Bytes／ByteList／Canonical双图及原联合归纳 | 全内部准确递归、总唯一及全部规范候选字节合法性 | 前批已验收 |
| T1.2c.3e.1d.2b.4b.1 | 同一原Cons的Bytes对齐、规范图准确递归 | 独立Prefix完整终止／延续双条件与准确tail | 本批已验收 |
| T1.2c.3e.1d.2b.4b.2／2c | 原Tok递归、Prefix递归、原商下降及固定Formula2 | 全部IH及数词消去，ALL3 Tok↔Prefix和任意规范列表Tok↔Bytes | 本批已验收 |
| T1.2c.3e.1d.2b.4b.3a | 原完整Fields、内部游标／余输入、原readTokens的value／scale／acc | 独立内部reader状态与逐步公式，终止规范守卫、延续值更新、EOF检查保留 | 下一单元 |
| T1.2c.3e.1d.2b.4b.3b | 上述reader状态、Canonical及真实加乘法 | 任意合法正scale的单规范前缀消费定理，value+n*scale、准确余输入／acc更新及多字节零终止拒绝 | 待完成 |
| T1.2c.3e.1d.2b.4b.3c | 单前缀消费、完整内部序列归纳、原readBytes商下降／marker1 | 从0／1／Nil开始的完整原reader对应、重置、完整消费、截断／尾随／非规范拒绝 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词／模板 | 原Basic条件AST到纯关系式Condition正式桥 | 待完成 |
| T1.2c.3e.2d | 原程序桥、原树／森林递归及内部归纳 | 完整字节包、版本1／marker1、树／森林顺序及完整消费／拒绝 | 待完成 |
| T1.2c.3f／1.2d | 原ProjectEncode／Quotation、primitive subset及全模式 | 原编译器准确桥、全内部Separation／Collection及目标3句公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输、内部Proof变换 | 待完成 |
| T4 | 内部Con及原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

下一单元必须直接保留原readTokens状态：低字节终止时检查scale=1或byte≠0，更新value+byte*scale后重置0／1并前插acc；延续时以真实d+128=byte更新value+d*scale及scale*128；EOF保留scale=1且value=0条件及acc逆序。不能从Tok↔Prefix跳过这些程序状态、内部序列消费或原Basic AST／最终checker。每批继续独立预审计、精确足迹、串行全仓验收和旧状态／锁／哈希／提交字节回读。
