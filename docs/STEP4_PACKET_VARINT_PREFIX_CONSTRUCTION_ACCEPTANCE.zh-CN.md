# 独立规范varint图与准确tail前缀构造验收（2026-10-25）

独立规范LEB128图及准确tail前缀的构造闭包已验收：原列表轨迹与数值序列共用全部内部索引，终止步要求原Nil及零初值，延续步要求非零已有值及base128仿射／移位字节。两类步互斥、实际128／256字节界已证；原序列追加构造双图，消去零、图及列表码见证。独立Prefix由规范图和实际Bytes定义，终止／延续构造保留准确剩余tail。17模块168声明、20组原nativeZF闭句；2370构建、25663审计、零警告，九命令／五trust=0通过。全部旧布尔叶保持。反向递归、全内部规范图总唯一及ByteList域、Tok双条件、原varint／readTokens程序桥、Basic AST、完整字节包、schema、Proof／解释及最终Con仍未完成。

## 对象合同与完整目标

对象语言为原单排序等号／成员语言，背景是Contract.nativeZF及完整Separation／Collection。正式证书返回原YesMetaZFC.Logic.FirstOrder.Derives；没有新推导核、对象Choice、不可达或内部ω标准性假设。原Packet十规则、Bytes／ByteList定义及所有旧跟踪PPAC证明和AST保持原样。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

完整内部Proof仍须覆盖全部内部ω、非标准及无效码、原六规则／27模式及完整公理模式。内部checker、数学解释与最终Con对象定理未证明。本批完成独立候选规范图的真实构造及局部定律，没有完成它与原宿主程序／Tok的全部正确性。

## 按原程序确定方向

锁定YesMetaZFC源码NatPacket.lean的varint采用低位优先：n<128时为[n]，否则前插n%128+128并递归n/128。readTokens按value／scale累积；终止字节小于128，多字节最后终止为零时拒绝，并在每次终止后把value／scale重置为0／1。原ObjectPacketData.bytes为byte+256*rest的foldr。

本批对象图沿原列表逐次前插的方向，从最高有效终止位向低位延续位构造。首次步必须在原Nil和零数值上放置终止位；后续步要求已有高位值非零。没有使用宿主varint计算或Tok接受作为规范图定义。源码条款校验只是方向锁定；它不是原宿主程序与内部图的形式化对应证明。

## 独立对象公式

以下变量均为对象集合变量。C／B是普通内部值；实际规范图另以Num128固定B。原Sequence包含完整functionOn及值域限制，原列表轨迹保留全部内部相邻行。

```text
Terminal(w,B,x,h,u,v) := Nil(w,x) ∧ Empty(u) ∧ h∈B ∧ v=h
Continue(w,B,h,u,v) := ∃d (¬Empty(u) ∧ Affine(w,B,d,u,v) ∧ Sum(w,d,B,h))
Cell(w,B,x,h,u,v) := h∈w ∧ u∈w ∧ v∈w ∧ (Terminal ∨ Continue)

Row(w,B,f,g,i) := ∃j,h,x,y,u,v (
  Succ(j,i) ∧ Edge(f,i,x) ∧ Edge(f,j,y) ∧ Cons(w,h,x,y) ∧
  Edge(g,i,u) ∧ Edge(g,j,v) ∧ Cell(w,B,x,h,u,v))

Trace(w,B,s,t,n,z,e,l,d,f,g) := OriginalListTrace(w,z,e,l,d,f,s) ∧
  Sequence(g,d,w) ∧ Edge(g,z,t) ∧ Edge(g,l,n) ∧ ∀i∈l Row(w,B,f,g,i)
FoldAt(w,B,s,t,n) := ∃z,e,l,d,f,g Trace(...)
CanonicalAt(w,B,n,s) := ∃z (Empty(z) ∧ FoldAt(w,B,s,z,n) ∧ ¬Nil(w,s))
Canonical(w,n,s) := ∃B (Num128(B) ∧ CanonicalAt(w,B,n,s))
Prefix(w,n,t,a) := ∃s (Canonical(w,n,s) ∧ Bytes(w,s,t,a))
```

Canonical的定义不引用Bytes或Tok。Prefix额外使用已独立验收的实际Bytes，以明确同一规范列表接在数值tail=t之前所得a；它不引用Tok，也不把成功reader、预期答案或执行输出用作规范性的定义。辅助FoldAt允许空轨迹，最终Canonical明确排除原Nil；二者范围不可混记。

## 已证明的原核对象结果

1. Cell自然域、实际终止／延续构造：终止步从原Nil、零、低于B的字节构造；延续步从真实内部仿射、加法及非零旧值构造。全部自然性由原ω、加法闭包及原仿射守卫证明。
2. Terminal与Continue不相容；已有数值为零时实际Cell只能是Terminal，已有列表非Nil时实际Cell只能是Continue。在实际Num128／Num256下，每份实际Cell都给h∈256，使用原128+128=256及加法严格单调。
3. 原双序列追加：全部旧行通过两张图的实际edgeIncluded保留，新末行使用同一真实Cons和实际Cell；配对／并集／追加实际构造两张新图，内部后继、图及原EX6见证全部消去。
4. 空辅助FoldAt的精确纤维为自然seed且输出等于seed。Canonical取得真实原有效列表、自然数值和非Nil，实际128见证用内部数词唯一性对齐；原Nil候选被拒绝。
5. 单字节及非零延续的Canonical真实图构造。没有预先假定完整图、长度、内部零或图存在；它们由原操作实际构造并消去。
6. Prefix的数值输入、准确剩余tail与输出均自然。单字节前缀及非零延续前缀实际构造：原Nil／Cons列表码内部取得并消去，规范图闭包与原Bytes闭包在同一列表码上组合。

核心前缀构造句子为：

```text
ZF ⊢ Ω(w) → Num128(B) → n∈B → ActualAffine256(w,n,t,a) → Prefix(w,n,t,a)
ZF ⊢ Ω(w) → Num128(B) → ¬Empty(q) → Prefix(w,q,t,u) →
       Affine(w,B,d,q,n) → Sum(w,d,B,h) → ActualAffine256(w,h,u,a) → Prefix(w,n,t,a)
ZF ⊢ Prefix(w,n,t,a) → n∈w ∧ t∈w ∧ a∈w
ZF ⊢ Nil(w,s) → ¬Canonical(w,n,s)
```

B、d、h、q、u、t和a仍是对象变量。Num128及算术关系在相应构造句子的前提中明确保留；没有把它们当作已经消去的最终仅Ω正确性。所有内部长度和索引保留，未替换成宿主有限列表或外部标准长度。

## 模块和实际验收

| 模块 | 本批职责 |
|---|---|
| PacketVarintCellSyntax／Cell／CellLaws | 独立步公式、自然性和实际构造、两类步互斥及局部字节界 |
| PacketVarintRowSyntax／RowMap | 六个真实行见证、两图全旧行传输及新末行 |
| PacketVarintTraceSyntax／Properties／Transport | 原双图和完整内部索引、长度／有效性／自然域、原等号替换 |
| PacketVarintTraceAppend／TraceBase | 两图实际追加、空图实际构造和准确纤维 |
| PacketVarintSyntax／Domain／Construct | 内部零起点与非空规范图、实际128对齐、终止／延续真实图构造 |
| PacketVarintPrefixSyntax／Domain／Construct | 准确tail前缀、全部数值域、内部列表码消去的两个构造器 |
| ObjectPacketVarintPrefix | 20组闭句经TheoryTransport.sentence和ZFReplay.replay进入原nativeZF核 |

- 定向原native构建2117任务成功；全仓2370任务成功，九命令全部退出0，五个--trust=0入口通过，零警告。
- 17模块168项显式声明先独立trust=0预审计，确认依赖后才接入正式Audit及受限native名单。累计25663审计，475无公理、25188只含允许的记录依赖。
- 20组core足迹恰为propext／Classical.choice／Quot.sound；native恰额外继承原ZF七项固定闭句证书。没有新增native_decide、对象公理、自定义axiom、宿主eval、预算或linter豁免；原choice专用桥范围不变。
- 2150份文件SHA256回读一致，2880对精确证书足迹，23319项Internal显式声明覆盖。七份理论／规则／工具链锁不变，YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净。原Bytes／ByteList及全部旧跟踪PPAC源码未改。
- 独立readback递归比较全部旧布尔叶，零变化。新增true门仅限独立图构造、局部终止／延续互斥、局部字节界、图闭包及准确tail前缀构造。完整规范图反向递归／总唯一／全输入域、Tok双条件、原程序桥、Basic AST、完整byte-tree、schema、Proof及Con未完成状态保持。

验收基点ae3dd13322c4db8b7cef55f9522b93b18affc047，本批17个Lean模块、4个接入文件和6份文档。证据为verification/summary.json、commands.json、build.log、audit.log、packet-varint-prefix-readback.json及.local/packet-varint-prefix-preaudit.json。复验命令C:/Python314/python.exe -X utf8 scripts/verify.py；仅本地提交。

## 清理与编译

定向首次因Lean保留字prefix报错，已改为prefixCode后通过；预审计和正式验收使用修正版本。确认Lean／Lake进程0、停止0，逐绝对路径及非reparse普通文件校验后，清理被成功结果替代的失败日志、已并入Audit的临时预审计驱动、已并入CheckStep4的片段及完成用途的一次性接入脚本，共4文件、逻辑34694字节。即时可用空间增加40960字节，清理后约90.71 GiB；随后串行全仓编译。路径、大小、SHA256见.local/packet-varint-prefix-precompile-cleanup.json。有效源码、依赖、工具链、构建缓存、成功日志及有复现用途的脚本保留，没有关闭其他应用。

## 后续agent工程流程表

| 顺序 | 具体实现与依赖 | 必须交付的原核对象结果 | 状态 |
|---|---|---|---|
| T1.2c.3e.1d.2b.1-3b | 原双图、ByteList、Foundation／Separation联合归纳 | 实际Bytes准确递归及唯一输出纤维精确定义域 | 前批已验收 |
| T1.2c.3e.1d.2b.4a.1 | 原列表前插轨迹、零起点数值序列、局部终止／非零延续 | 独立规范图和准确tail前缀的真实构造闭包、局部字节界 | 本批已验收 |
| T1.2c.3e.1d.2b.4a.2 | 两图原Separation限制、完整末行、原Nil／Cons注入性 | 规范图全内部反向分解、准确终止／延续双条件；空辅助轨迹与非空规范图严格区分 | 下一单元 |
| T1.2c.3e.1d.2b.4a.3 | 完整递归及原Foundation／Separation | 规范列表全内部存在唯一、独立ByteList域及真实末位非零规范性，全部IH消去 | 待完成 |
| T1.2c.3e.1d.2b.4b／2c | 上述规范图、Bytes和Tok准确递归及逆唯一 | Tok↔独立规范Prefix，原varint／readTokens对应及准确余输入／拒绝 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词／模板 | 原Basic条件AST到纯关系式Condition的正式推导桥 | 待完成 |
| T1.2c.3e.2d | 原程序桥、原结构递归及内部归纳 | 完整字节包、版本1／marker1、树／森林顺序及完整消费／拒绝 | 待完成 |
| T1.2c.3f／1.2d | 原ProjectEncode／Quotation、primitive subset及全模式 | 原编译器准确桥、全内部Separation／Collection及目标3句公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输、内部Proof变换 | 待完成 |
| T4 | 全内部Con及原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

下一单元先将现有原列表末行逆分解及两张真实限制图复用于本批Cell；不能从已证正向构造跳过反向、总唯一、全部内部规范性和原readTokens程序对应。每批保持独立预审计、精确足迹、串行全仓验收及所有旧状态／锁／哈希回读。
