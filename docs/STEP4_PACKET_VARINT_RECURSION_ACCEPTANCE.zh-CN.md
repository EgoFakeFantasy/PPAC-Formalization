# 独立规范varint全内部准确递归验收（2026-10-25）

独立规范varint的全内部准确递归已验收：原Separation构造双限制前缀图、保留全部旧行，两张原函数图归一完整末行。真实非零尾值与零seed证明较短列表非Nil，构造实际较小规范图；终止头字段经对象等号对齐。完整EX4延续分支和实际128见证双向对齐并消去外部前提，最终仅Ω取得ALL2 Canonical↔终止／延续精确条件。13模块129声明、14组原nativeZF闭句；2383构建、25792审计、零警告，九命令／五trust=0通过。反向递归顶层及对应旧guard子门false→true，其余旧布尔叶保持。全内部规范图总唯一／ByteList域、Tok双条件、原varint／readTokens程序桥、Basic AST、完整字节包、schema、Proof／解释及最终Con仍未完成。

## 对象合同与完整目标

对象语言保持原单排序等号／成员语言，背景为Contract.nativeZF及完整Separation／Collection。正式证书返回原YesMetaZFC.Logic.FirstOrder.Derives；没有新推导核、对象Choice或不可达假设。旧独立Canonical、Cell和双图定义、原Packet十规则、Bytes／ByteList及全部旧跟踪PPAC证明和AST保持原样。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

完整内部Proof仍须覆盖全部内部ω、非标准及无效码、原六规则／27模式和完整公理模式。内部checker、数学解释及最终Con对象定理尚未证明。本批是独立规范图准确递归的验收，不是完整原varint／readTokens程序对应或最终相对一致性的交付。

## 准确对象公式

沿用前批零seed、非空原列表和完整双序列图的CanonicalAt／Canonical定义；本批没有把规范性改为递归答案定义。由它实际证明：

```text
Small(w,B,n,s) := n∈B ∧ ∃e (Nil(w,e) ∧ Cons(w,n,e,s))
LargeAt(w,B,n,s) := ∃d,q,h,x (
  Affine(w,B,d,q,n) ∧ ¬Empty(q) ∧ Sum(w,d,B,h) ∧
  CanonicalAt(w,B,q,x) ∧ Cons(w,h,x,s))
LargeActual(w,B,n,s) := ∃d,q,h,x (
  Affine(w,B,d,q,n) ∧ ¬Empty(q) ∧ Sum(w,d,B,h) ∧
  Canonical(w,q,x) ∧ Cons(w,h,x,s))
Criterion(w,n,s) := ∃B (Num128(B) ∧ (Small(w,B,n,s) ∨ LargeActual(w,B,n,s)))

ZF ⊢ Ω(w) → B∈w → (CanonicalAt(w,B,n,s) ↔ (Small(w,B,n,s) ∨ LargeAt(w,B,n,s)))
ZF ⊢ Ω(w) → Num128(B) → (CanonicalAt(w,B,n,s) ↔ (Small(w,B,n,s) ∨ LargeActual(w,B,n,s)))
ZF ⊢ Ω(w) → ∀n,s (Canonical(w,n,s) ↔ Criterion(w,n,s))
```

最后一式为实际ALL2及标量接口，仅需Ω；n、s仍遍历全部内部集合候选，q、d、h、x、B均为内部对象见证。一般自然B的辅助版本明确保留B∈ω；实际128时由原数词范围定理取得。最终前提不留外部长度、零、图、根行、非标准性、IH或实际数词见证。Criterion保留对象公式内必要的内部EXB及EX4，不能把内部存在量词说成已经从公式删除。

辅助原FoldAt还取得准确零／后继递归：

```text
ZF ⊢ Ω(w) → (FoldAt(w,B,s,t,n) ↔
  (Nil(w,s) ∧ t∈w ∧ t=n) ∨
  ∃h,x,q (Cons(w,h,x,s) ∧ FoldAt(w,B,x,t,q) ∧ Cell(w,B,x,h,q,n)))
```

该FoldAt允许空轨迹。Canonical额外要求零seed及非Nil，二者不能混用。完整全内部Canonical存在唯一性、全部规范列表的独立ByteList域、Tok双条件及原reader对应仍未证明。

## 反向分解为何保留原语义

1. 双限制图：对原长度的实际前驱p，用原Separation的Restriction矩阵分别构造列表图F和数值图G的精确前缀。每个旧内部i∈p对应的真实六见证行保留；i及其后继都正式证明处于限制域。真实函数域、全部旧行、首尾边都保留，没有只保留某个局部字段。
2. 完整末行：从全部原links取得前驱p的完整EX6行；原后继唯一性对齐索引，两张完整functionOn的单值性分别对齐最后列表码和最后数值。原对象等号替换传输Cons输出及整个Cell输出，得到准确EX3末步。
3. 实际较短图：双限制图给尾列表x及旧数值q的完整FoldAt。原内部长度零／后继分解给辅助FoldAt的准确Nil／Cons双条件；两份限制图、六见证行、前驱和根图均对象消去。
4. 终止分支：实际Terminal给原Nil尾、零旧值、h∈B及n=h。用原等号替换对齐实际Cons头h为n，同时传输成员界，实际构造Small的单元素列表见证。
5. 延续分支：实际Continue给非零q、真实base-B仿射和+B字节。如果实际较短列表x是Nil，已验收的FoldAt Nil值定理给zero=q；原空性等号替换迫使q为空，与非零矛盾。因此真实x非Nil，连同实际零seed及限制图构成完整CanonicalAt(w,B,q,x)。这一步没有假定尾列表本来规范或非空。
6. 反向构造：Small调用前批真实终止图构造；LargeAt调用前批真实非零延续图构造。原Nil／Cons、零／序列存在均为实际对象操作。
7. 实际128：对完整EX4分支，CanonicalAt与Canonical用同一个Num128的原内部数词唯一性双向对齐。最终把实际128在两个定义中的内部见证逐一消去并重新引入目标EXB，取得仅Ω的精确双条件及ALL2。

内部长度、索引、列表码和数值可为非标准对象；没有宿主Nat／List运行归纳、模型外部良基、任意值选择或固定长度上限。外部Bool只选择两个固定AST模板（较小CanonicalAt／实际Canonical）；它不是内部运行时值或分支证明的替代品。

## 实现与实际验收

| 模块 | 原核对象工作 |
|---|---|
| PacketVarintRowRestrict／TracePrefix | 两张真实限制图及全部旧行／首尾边，内部图构造消去 |
| PacketVarintRecursionSyntax／Terminal | 完整末行EX3及原对象等号替换，双函数归一 |
| PacketVarintDecomposition／RecursionEquation | 全内部辅助FoldAt准确Nil／Cons递归 |
| PacketVarintCanonicalRecursionSyntax | 独立Small／完整EX4两种表示、Criterion、ALL2及重命名 |
| PacketVarintCanonicalPieces | 终止头等号对齐及非零值迫使真实尾列表非空 |
| PacketVarintCanonicalDecomposition／RecursionEquation | 独立规范图的反向分解及两个分支的真实反向构造 |
| PacketVarintCanonicalRecursionBridge／Laws | 实际128较小规范图双向对齐、最终仅Ω精确递归与ALL2 |
| ObjectPacketVarintRecursion | 14组闭句经TheoryTransport.sentence与ZFReplay.replay进入原nativeZF |

- 定向原native构建2129任务成功；全仓2383任务成功。九条命令全部退出0，五个--trust=0入口通过，零警告。
- 新增13模块129声明先独立trust=0预审计，确认精确足迹后才接入正式Audit、CheckStep4及受限native允许名单。累计25792审计，475无公理、25317仅含记录的允许依赖。
- 14组core恰为propext／Classical.choice／Quot.sound，native恰额外继承原ZF七项固定闭句证书；原choice专用桥范围不变。没有新增native_decide、自定义axiom、对象公理、宿主eval、预算提高或linter豁免。
- 2163份文件SHA256回读一致，2894对精确core／native足迹，23448项Internal显式声明覆盖。七份理论／规则／工具链锁保持；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净。全部旧跟踪PPAC源码保持。
- 独立readback递归核查全部旧布尔叶：仅全内部规范图反向递归顶层门及旧构造guard对应子门false→true，其余旧值保持。新true门限于双限制图、辅助FoldAt递归、实际非空尾证明、实际128双向对齐及最终ALL2。规范图全域总唯一／ByteList域、Tok、原程序桥、Basic AST、完整byte-tree、schema、Proof及Con保持未完成。

验收基点c365e7a74566e6fcf58f26b41fb5e6bbfffa1fea；本批13个Lean模块、4个接入文件和6份文档。证据见verification/summary.json、commands.json、build.log、audit.log、packet-varint-recursion-readback.json与.local/packet-varint-recursion-preaudit.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py；仅本地提交。

## 清理后继续编译

最初的固定Bool模板用if展开时，重命名未归约并触发递归深度及未用simp参数警告；改为显式两个AST模板的match及命名重命名引理后通过。没有增大限制或禁用linter。独立预审计与接入完成后检查Lean／Lake进程0、停止0；逐绝对路径及非reparse普通文件核查后，删除已并入Audit的临时驱动、已并入CheckStep4的片段、被成功编译取代的失败日志，共3文件、逻辑26624字节，即时可用空间增加32768字节。清理后约90.57 GiB，随后串行全仓验收。明细／SHA256见.local/packet-varint-recursion-precompile-cleanup.json。有效源码、工具链、缓存、成功日志和有复现作用的脚本保留，没有关闭其他应用。

## 后续agent工程流程表

| 顺序 | 具体实现与依赖 | 必须交付的原核对象结果 | 状态 |
|---|---|---|---|
| T1.2c.3e.1d.2b.1-3b | 原字节双图、ByteList及原联合归纳 | 实际Bytes全内部准确递归、总唯一及精确输入域 | 前批已验收 |
| T1.2c.3e.1d.2b.4a.1 | 独立零seed双图及原终止／非零延续公式 | 实际图构造闭包、局部字节界、准确tail前缀构造 | 前批已验收 |
| T1.2c.3e.1d.2b.4a.2 | 原双限制图、末行归一、非零真实尾证明及内部128对齐 | 辅助FoldAt和独立Canonical的全内部准确递归，最终ALL2仅Ω | 本批已验收 |
| T1.2c.3e.1d.2b.4a.3a | 原base128除法／严格商下降、固定联合对象矩阵 | 同时处理规范列表存在、全部实际规范候选ByteList域、同数值列表唯一性 | 下一单元 |
| T1.2c.3e.1d.2b.4a.3b | 原Foundation／完整Separation及该联合矩阵 | 全部内部IH消去、Canonical唯一列表纤维准确自然域及独立字节合法性 | 待完成 |
| T1.2c.3e.1d.2b.4b／2c | Canonical／Bytes准确递归、原Tok递归及已证前缀逆唯一 | Tok↔独立规范Prefix，原varint／readTokens程序对应、准确余输入及拒绝 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词／模板 | 原Basic条件AST到纯关系式Condition正式桥 | 待完成 |
| T1.2c.3e.2d | 原程序桥及原结构递归、内部归纳 | 完整字节包、版本1／marker1、树／森林顺序及完整消费／拒绝 | 待完成 |
| T1.2c.3f／1.2d | 原ProjectEncode／Quotation、primitive subset及全模式 | 原编译器准确桥、全内部Separation／Collection及目标3句公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输、内部Proof变换 | 待完成 |
| T4 | 内部Con及原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

下一单元用真实规范递归与原商下降联合证明总性、全部实际规范候选的独立ByteList域和列表唯一性。不能只证明有某个输出、只处理标准有限列表，或以Tok定义Canonical来跳过独立对应。每批继续预审计、精确足迹、串行全仓验收和旧状态／锁／哈希／提交字节回读。
