# 全内部有界token流的整段逆向与初始化对象验收（2026-10-25）

全内部有界token流的整段逆向与初始化双条件已验收：原Formula5按真实字节码成员归纳，完整Separation／Foundation关闭全部IH；任意累加器、载荷及返回候选下，成功运行重建真实token列表、独立Encoded及精确Output。实际128／0／1见证对象消去；Ω、ByteList和Some下取得Parse↔Encoded，Ω下有界成功像准确等于独立Encoded，实际Some见证也由原对象存在构造取得。10模块79声明、9组原nativeZF闭句；2634构建、28530审计、零警告，九命令／五trust=0通过。仅四个已证明的有界整段逆向旧门false→true，其余旧布尔叶保持。完整readBytes／树／森林／packet程序桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 背景及尚未证明的最终目标

对象语言保持纯EqMem，背景为原完整ZF（全Separation／Collection），正式关系为原FirstOrder.Derives。闭句经TheoryTransport.sentence及ZFReplay.replay取得原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。未加入新核、对象Choice、不可达、外部标准ω或模型外部良基前提；静态Fin槽位只用于公式构造。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

该最终内部Con主句仍未证明。完整Basic AST、原六规则／27模式、全公理模式及全部内部Proof码（含非标准／无效码）、数学解释和内部证明变换仍须完成。token流正确性不能替代这些端点。

## 整段逆向的实际对象合同

公开接口PacketReaderInverseInduction.inverse：

```text
Ω ∧ Num128(B) ∧ Empty(z) ∧ Succ(o,z) ∧ ByteList(L)
∧ Eval(L,z,o,A,p) ∧ Some(O,p)
→ ∃tokens (Encoded(tokens,L) ∧ Output(A,tokens,O))
```

A、O、p为任意对象候选；没有外加Valid(A)、p∈ω、O∈ω或残留IH。实际State及累加器有效性从Eval恢复。Encoded仍为预先独立定义的真实双轨迹／Canonical段／Splice关系，没有用成功解析重定义它。

固定Formula5参数为w／B／z／o／输入码L，内部ALL3量化A／O／p。Nil分支从原实际成功EOF取得Reverses(A,O)，选择真实Nil token并用准确Nil编码与右Nil拼接构造Output。

非Nil分支调用已验收的规范首段EX5，保留T∈L及ByteList(T)。原零／单位算术唯一性将发射u准确归一为token值n，真实Cons头替换保持同一个累加器码c。由真实较小输入码在T调用IH，取得独立尾token编码；内部构造完整Cons token列表，通过原准确编码Cons式和OutputBackward.step恢复同一真实token见证的编码与输出顺序。

原BoundedInduction.induction_on_set以matrix.neg的完整Separation及Foundation消去所有较小输入假设。下降来自实际码成员关系，不是宿主List.length或外部良基；覆盖全部内部非标准输入长度及原guard下的任意无效候选。

## 初始化与完整有界成功像

PacketReaderInverseInitialized.at_literals接入原InitLiterals；实际Nil累加器的Output恒等式识别抽取token码与Some载荷相等，原eqSubst传输Encoded。at_success再通过原with_units和实际Num128存在构造消去128／0／1见证，得到：

```text
Ω ∧ ByteList(bytes) ∧ Some(tokens,p)
→ (Parse(bytes,p) ↔ Encoded(tokens,bytes))
```

进一步定义一个单独的实际成功关系，保持独立编码定义不动：

```text
Accepted(tokens,bytes) := ∃p (Parse(bytes,p) ∧ Some(tokens,p))
BoundedAccepted(tokens,bytes) := ByteList(bytes) ∧ Accepted(tokens,bytes)
Ω → (BoundedAccepted(tokens,bytes) ↔ Encoded(tokens,bytes))
```

从Encoded到成功像的方向由原Some.exists构造实际p，再用已验收正向消费；p的存在和消去均在对象推导内。字节界明确保留：原始reader可在任意自然数列表上运行，不能把无界Accepted直接等同于Encoded。本批证明的是完整有界token-stream接口，不是完整数值packet／树／森林decode。

## 实际验收及清理

- 全仓2634构建任务全部通过，0警告。
- 28530声明审计：504无公理，28026仅允许依赖。
- 新10模块／79显式声明，9组原核/native闭句精确依赖全部符合；总计3221组闭句对，Internal显式覆盖26186。
- 9条命令全部exit 0，其中5条--trust=0；2414文件哈希全部回读。
- 仅四个旧守卫更新为true：prefix中的完整多token逆向、byte-bound中的有界规范逆向、multitoken中的有界逆向分解、single-varint中的多token分段／顺序／有界逆向复合门。所有其余旧布尔叶保持；全packet、Basic／Proof／解释／Con未翻转。
- 7个锁文件及YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6与干净依赖树保持。
- 清理4个显式临时文件，共11711逻辑字节，停止0个进程；清理前无工作区编译器。磁盘实测99137490944→99137507328字节，差值不等同于删除量。源码、依赖、有效缓存和历史证据保留，清理后执行全仓验收。

本地证据：verification/reader-inverse-readback.json、summary.json、commands.json、build.log、audit.log；.local/reader-inverse-batch.json、reader-inverse-preaudit.json、reader-inverse-precompile-cleanup.json。提交后再核对Git blob、全部工作哈希及干净状态，不自动发布本地日志。

## 后续agent友好工程流程

| 单元 | 实际接口／输入 | 原核交付与工程验收 | 状态 |
|---|---|---|---|
| R4b.3b.2b／2c.0／2c.1 | 独立Encoded、完整ByteList、规范首段EX5 | 正向消费、全局字段界、成功首段与真实rest∈input | 已验收 |
| R4b.3b.2c.2／2c.3 | InverseInduction.inverse、InverseInitialized.at_success、InverseAccepted.bounded_iff | 整段逆向、精确输出、全部IH／初始化常量消去、有界成功像双条件 | 本批已验收 |
| R5a | 实际Splice及PacketBytesTraceSyntax.bytes | 按真实prefix码证明Bytes拼接组合，任意数值tail／输出，原有无效候选保留 | 下一单元 |
| R5b | Encoded、Bytes、TokenCanonicalLaws.at_canonical_list | 独立PackedTokens及准确Nil／Cons／原Tok递归，区分列表尾与数值尾 | 待完成 |
| R5c | 原NatPacket.readBytes、商256／终止一／零拒绝 | 建立真正实际程序关系和全部内部码正确性，不以规范谓词定义成功 | 待完成 |
| R5d | 原readTree/readForest、内部fuel、版本一、空余输入检查 | 原Tree／Forest／Packet图与完整程序双条件，所有无效码 | 待完成 |
| A／P | 原Basic AST、六规则／27模式、全Separation／Collection | 全内部ProofZF／ProofU及公理／证明变换正确性 | 待完成 |
| I／C | 对象数学解释、原语言／理论对应 | nativeZF中的最终内部Con蕴含 | 待完成 |


注意PacketBytesTraceSyntax.bytes(w,C,t,a)中的C是实际字节列表，而t／a是自然数码；Encoded的两个参数是token列表码和字节列表码。原Tok是tag2数值前缀关系，不能将列表拼接误当数值合成。下一批先证明Bytes在Splice上的准确组合，再接PackedTokens、readBytes及完整树／森林／packet程序；任意数值tail0并不保证编码单射，实际packet终止标记一须准确保留。

后续源码接口与具体任务如下。它们是只读计划，尚未实现或验收R5。

### R5接口与具体实现计划

本节为后续R5的只读源码映射；本批有界stream逆向已验收，后续完整packet／程序／AST桥仍未验收。

## What the present objects mean

- PacketTokensBytes.encoded(w,tokens,bytes): actual internal token-list code -> actual internal byte-list code; paired original traces, each token contributes an independent Canonical segment spliced before the previous actual bytes. This relation has no numeric packet tail/output and no tree grammar.
- PacketByteInputSyntax.byteList(w,bytes): independent complete original encoding/Fields graph, every value below actual 256. PacketReaderInverseAccepted.boundedAccepted is explicitly ByteList AND EX p(Parse AND Some); bounded_iff compares it to independent Encoded. Unbounded accepted must not be equated to Encoded.
- PacketVarintSyntax.canonical(w,n,C): one nonempty actual canonical LEB128 byte list, independent zero-seeded numeric base128 trace.
- PacketBytesTraceSyntax.bytes(w,C,t,a): actual little-endian base256 fold of actual byte-list C onto numeric tail t, yielding numeric a. This is not concatenation of byte lists. PacketBytesExecution.fiber_iff gives exact total unique output domain ByteList(C) AND t in omega; PacketBytesExecutionInduction.output_unique/input_domain give all-candidate facts.
- PacketVarintPrefixSyntax.prefixCode(w,n,t,a) := EX C(Canonical(w,n,C) AND Bytes(w,C,t,a)). Here t,a are NUMBERS, unlike actual list T,L in Splice.
- PacketTokenAcceptedSyntax.accepted(w,n,t,a): original tag2 Tok row plus PacketTraceSyntax.condition. PacketTokenCanonicalLaws.actual_iff proves Tok iff prefixCode for every candidate under Omega; at_canonical_list proves Tok(n,t,a) iff Bytes(C,t,a) for any actual Canonical(n,C). This does not itself describe an entire token list or runtime readTokens.

Actual source interfaces are PPAC/Migration/Internal/PacketBytesTraceSyntax.lean, PacketBytesLaws.lean, PacketBytesCons.lean, PacketBytesExecution.lean, PacketVarintSyntax.lean, PacketVarintPrefixSyntax.lean, PacketTokenCanonicalLaws.lean and PacketReaderInverseAccepted.lean.

## Pinned source and final packet target

Pinned source program: .lake/packages/YesMetaZFC/YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/NatPacket.lean. readBytes(code,acc) descends by quotient256, accepts terminal numeric1 and rejects terminal0; readTokens is the byte-stream layer; readTree/readForest use actual fuel and count; decode runs readBytes, then readTokens initialized0/1/Nil, requires version token1, invokes readTree with payload.length+1, and rejects a nonempty remaining token tail.

Pinned grammar: .lake/packages/YesMetaZFC/YesMetaZFC/Automation/ObjectPacketGraph.lean has the unchanged ten-rule table:
 tags0/1 are affine128/affine256, tag2 Tok, tag3 Tree, tag4 Forest, tag5 Packet. ObjectPacket.condition(packet,treeCode) is the native original Horn target. ObjectPacketData.lean defines host bytes/token/tree/forest and bytes_append/encode_eq, but these host recursions do not establish all-internal correspondence.

Current actual original grammar targets:
- PacketStructureAcceptedSyntax.tree(w,n,t,a)
- PacketStructureAcceptedSyntax.forest(w,n,count,t,a)
- PacketStructureAcceptedSyntax.packet(w,packetNumber,treeCode)
They are original tagged rows and PacketTraceSyntax.condition, not definitions by program success.
- PacketStructureSearchLaws.tree_iff/forest_iff/packet_iff give exact object recursive equations with original environmentNat guards for ALL candidates.
- PacketStructureAcceptedSyntax.treeCase uses actual RawNode(tag,childrenCode,n), Forest(childrenCode,count,t,u), Tok(count,u,v), Tok(tag,v,a).
- forest Cons uses actual Cons(head,tail,n), successor count, Forest(tail,smallerCount,t,u), Tree(head,u,a); Nil retains numeric-tail naturality.
- packetCase is EX e,u(Num1(e) AND affine256Accepted(e,u,packetNumber) AND Tree(treeCode,e,u)). This separately fixes outer version byte1 and final numeric marker1.
- PacketStructureTailChildren.raw_payload/cons_children already provide actual strict child-code descent from accepted original fields. PacketStructureTailBounds and PacketStructureTailLaws give all-internal numeric tail<=output.

## Smallest next reusable unit A: Bytes across actual Splice

Proposed API, not currently present:
 Omega(w), Splice(w,C,T,L), Bytes(w,T,t,u)
 => (Bytes(w,L,t,a) iff Bytes(w,C,u,a)).

Keep all numeric tails and candidate a arbitrary; existing Bytes premises provide needed naturality. Do not add positivity of t: byte fold works at numeric0 as well. No ByteList(C) antecedent is necessary if both directions retain actual Bytes predicates; invalid prefix bytes make both sides false.

Use fixed Formula2 P(w,C) universally quantifying T,L,t,u,a, with actual Splice and actual Bytes tail premises. Nil uses Splice.nil_iff, Bytes.nil_iff and actual Bytes output uniqueness. Cons uses Splice.cons_forward and PacketBytesCons.cons_iff to align the SAME actual Cons; transport the smaller Bytes predicate under the internal intermediate-value EX, then rebuild the actual Cons. Actual Cons.components gives smaller prefix code in C. Full Separation(matrix.neg)+Foundation closes all internal C. Existing byte-list validity/field guards are retained by the actual Bytes relations.

Suggested agent unit: PacketBytesSpliceSyntax/Point/Step/Induction/Laws plus original native closed schemas.

## Unit B: compose actual Encoded with numeric Bytes and Tok

A small independent relation can avoid another large paired-trace implementation:
 PackedTokens(w,tokens,t,a) := EX bytes(Encoded(w,tokens,bytes) AND Bytes(w,bytes,t,a)).
It is independent of reader success.

Prove exact Nil:
 Nil(tokens) -> (PackedTokens(tokens,t,a) iff (t in omega AND t=a)).
Prove exact Cons on actual natural h/x and Cons(h,x,tokens):
 PackedTokens(tokens,t,a) iff EX u(PackedTokens(x,t,u) AND Tok(h,u,a)).

Use Encoded.cons_iff, unit A, canonical-list existence/uniqueness, PacketTokenCanonicalLaws.at_canonical_list, and actual Bytes totality for intermediate u. Construct/remove all byte/C/u witnesses inside object EX. Domain/unique output follows existing Encoded and Bytes fibers for exactly Valid(tokens) AND t natural. Combine with boundedAccepted iff Encoded for runtime stream/numeric-fold correspondence.

Important: arbitrary numeric tail0 permits collisions such as empty versus trailing zero bytes. Do not infer inverse byte-list/token-list injectivity for arbitrary numeric tails from output uniqueness. Marker1 and actual readBytes semantics belong to the next unit.

## Unit C: actual readBytes, marker1 and complete numeric packet input

No current actual readBytes state/history/program relation was found in PPAC/Migration/Internal. Build the original numeric-code/reverse-accumulator state, quotient256 actual step, actual terminal0/1, actual Option return and actual history. Do not define the reader by Bytes.

Existing arithmetic: PacketDivisionSyntax.decomposes, division existence/unique modules, PacketDivisionDescentCore.quotient_strict true supply actual remainder/quotient and q in oldCode for nonzero oldCode; original <2 branch and unit/zero must be represented exactly. Original low bytes come from guarded affine256 and are automatically <256.

Target generalized successful inverse:
 ReadBytesEval(code,A,p) AND Some(out,p)
 => EX bytes(ReverseAppend(A,bytes,out) AND Bytes(bytes,one,code) AND ByteList(bytes)).
Also prove forward pack and exact initialized Some characterization with marker1. Original Foundation induction is on actual code in omega, not host Nat. This establishes correct marker presence, zero rejection and full byte consumption.

Suggested agent split: arithmetic/guards; raw state+step+code; actual histories/termination; exact program/Bytes inverse and native acceptance.

## Unit D: tree/forest token grammar and actual fuelled parser

Need independent actual TreeTokens/ForestTokens on structural tree/list codes and actual ordered token lists. StructuralTreeValiditySyntax.valid, validChildren, nodeData and StructuralTreeRecursion.valid_iff_recursive already describe genuine internal trees. Natural codes alone are not tree validity; preserve malformed tree/forest candidates.

Prove original Tree/Forest numeric grammar iff corresponding actual token lists plus PackedTokens. A joint fixed code-induction property handles Tree and Forest, with strict Raw payload/Cons head-tail descent. Keep actual child count and all ordered fields; never replace internal candidates with quotations of external host Tree/List Tree.

Separately implement actual readTree/readForest state/fuel/Option relations with source equations. A joint fixed object induction on actual fuel suffices for mutual recursive calls, with count retained as another internal field. Prove fuel adequacy at the exact source payload.length+1 using actual HasLength/Cons consumption, with no fixed external cap. Preserve count0 behavior at any fuel, tree fuel0 rejection, truncation, malformed constructors and exact remaining input.

Final all-candidate target is original PacketStructureAcceptedSyntax.packet(w,packetNumber,treeCode) iff actual complete decode success with that treeCode. Need original readBytes marker1 + stream parse + version1 + actual tree parser + exact Nil remainder. All packet/tree/token/byte/fuel/count/output candidates range over internal sets; invalid and nonstandard natural codes remain covered. Finish through TheoryTransport.sentence and ZFReplay.replay to original Derives nativeZF [].

Do not claim this full packet program bridge, Basic AST, original six-rule/27-schema Proof checker, object interpretation or final Con implication from the newly completed byte-stream inverse.
