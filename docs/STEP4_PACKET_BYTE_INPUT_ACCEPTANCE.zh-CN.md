# 独立有效字节输入守卫及全内部递归验收（2026-10-25）

独立有效字节输入守卫及全内部Nil／Cons递归已验收：定义直接使用原Encoding／HasLength／完整Fields图和图值域小于256，不引用Bytes执行。完整图边界与全部内部逐字段界双向等价；真实零字段取得头字节界，后继字段对应给尾界并构造反向界。长度、完整字段图、零／后继及256见证对象消去；最终仅Ω取得ALL1 ByteList↔Nil∨EX2(Cons∧Byte_head∧ByteList_tail)，全局自然性从原有效列表取得，辅助原Cons注入／字段定律保留自然性前提。9模块135声明、16组原nativeZF闭句；2341构建、25361审计（474无公理／24887允许依赖）、零警告；九命令／五trust=0通过，2121哈希、2844对精确足迹、23017项Internal覆盖。全部旧布尔叶保持。字节执行全域存在唯一、规范varint／readTokens对应、Basic AST桥、完整字节包、schema、Proof／解释及最终Con仍未完成。

## 对象合同与完整目标

对象语言保持原纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection，正式证书返回原YesMetaZFC.Logic.FirstOrder.Derives。没有新推导核、公理、对象Choice或不可达假设；原Packet／Bytes定义、原字段图及全部旧证明源码保持。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

完整内部Proof仍须覆盖全部内部ω、原六规则／27模式及完整公理模式，包含非标准和无效码。完整Proof、数学解释及最终Con尚未证明；本批不是字节执行全域总唯一性或原bytes／varint／readTokens完整对应的验收。

## 独立输入公式

原Fields包含精确域l上的完整函数图、真实Kuratowski字段像及全边双条件；没有只取某个局部字段或宿主列表。直接定义：

```text
InputAt(w,C,n) := ∃l,f (OriginalEncoding(w,f,l,n) ∧ Bounded(f,C))
OriginalEncoding(w,f,l,n) := (n∈w ∧ HasLength(w,n,l)) ∧ Fields(w,n,l,f)
Bounded(f,C) := ∀i,y (Edge(f,i,y) → y∈C)
Byte(h) := ∃C (Num256(C) ∧ h∈C)
ByteList(w,n) := ∃C (Num256(C) ∧ InputAt(w,C,n))
Bounds(w,C,n,l) := ∀i,y (i∈l → Field(w,n,i,y) → y∈C)
```

n、l、f、i、y、C均为对象变量。长度l及字段索引包含内部非标准值。InputAt和ByteList的定义与本批证明不使用Bytes执行谓词，也不把“有输出”作为输入合法性的条件。

## 原核精确结果

```text
ZF ⊢ Ω(w) → (InputAt(w,C,n) ↔ ∃l (HasLength(w,n,l) ∧ Bounds(w,C,n,l)))
ZF ⊢ Ω(w) → C∈w →
       (InputAt(w,C,n) ↔ Nil(w,n) ∨
          ∃h,t (Cons(w,h,t,n) ∧ h∈C ∧ InputAt(w,C,t)))
ZF ⊢ Ω(w) → ∀n (ByteList(w,n) ↔ Nil(w,n) ∨
          ∃h,t (Cons(w,h,t,n) ∧ Byte(h) ∧ ByteList(w,t)))
```

最后一式是全内部ALL1及标量双条件，仅需Ω。还有ByteList⇒原有效列表／n∈ω及Ω下Byte⇒自然性，适用于全部候选值。一般内部C的递归反向明确保留C∈ω，因为h∈C需要实际推导h∈ω；最终固定256时由原内部数词范围定理消去该额外前提。

给定原Cons字段的辅助反向定理仍保留h∈ω、t∈ω：

```text
Ω(w), h∈w, t∈w, Cons(w,h,t,n), InputAt(w,C,n)
  ⊢ h∈C ∧ InputAt(w,C,t)
```

全局分解从原有效列表的真实分解取得这些字段自然性，没有静默把任意未带守卫Cons字段视作自然数。最终EX2仍是内部真实头／尾见证；没有把合法内部码改成外部有限模式。

## 具体对象证明

1. 完整图／逐字段界：Fields全边式Edge(f,i,y)↔i∈l∧Field(w,n,i,y)直接给两个方向。图界传到全部内部字段界，字段界也实际证明给定完整图的Bounded(f,C)。从HasLength取得l∈ω，原字段图存在唯一纤维实际构造f，再形成原Encoding及InputAt；f对象消去。对于任意另一份实际HasLength，由原长度唯一性及对象等号替换传回同一Bounds。
2. 真实头界：内部取得零z；原Succ(s,r)和自然序给z∈s，原StructuralListFieldCons.zero_value给Field(w,n,z,h)，把完整Bounds应用在该实际字段得h∈C。零／一见证对象消去。
3. 尾界反向：对任意内部i∈r及尾字段Field(w,t,i,y)，实际取得其后继j，原自然序证明j∈s=r+1。原successor_backward给父字段Field(w,n,j,y)，父界给y∈C。对全部内部i,y取得尾Bounds，后继见证消去。
4. Cons前向界：对任意父索引i∈s，用原内部ω零／后继分解。零分支由原zero_point对齐y与h；后继分支用原predecessor_inside证明前驱属于r，原successor_forward读回尾字段，应用尾Bounds。没有宿主List或Nat运行归纳。
5. 原长度与图构造：Nil实际长度为空，字段界由空性给出，再实际构造完整字段图。Cons从尾HasLength取得真实后继长度，由原cons_length构造父HasLength，合成父字段界并实际构造父完整图。反向从父真实长度及原cons_predecessor取得尾长度，合成头界和尾界后实际构造尾完整图。所有长度、图和前驱见证均消去。
6. 全内部递归：从InputAt取得原有效列表，再用原valid_decomposition得到Nil或真实自然头及有效尾；应用上述辅助反向结果给EX2字节Cons分支。两个反向构造完成一般自然C的准确递归。
7. 固定256：Byte与ByteList各自内部取得字面量；原数词唯一性对齐到同一个256并作对象等号替换。原内部数词存在／范围构造并消去C，合成仅Ω的实际ByteList递归及ALL1。没有额外图、长度、字面量或执行见证前提。

这些证明提供独立合法输入守卫，不自动证明Bytes输出存在或唯一。字节执行的准确域、全部IH消去、规范varint和readTokens仍须后续正式对象证明。

## 实际验收

- 原native定向2090任务成功；全仓2341任务成功。九条命令、五个--trust=0入口全部退出0，零警告。
- 新增9模块135声明先独立--trust=0预审计，再正式Audit全覆盖。累计25361审计，474无公理、24887仅含记录的允许依赖。
- 新增16组core／native精确足迹：core恰为propext／Classical.choice／Quot.sound，native恰额外继承原七项固定闭句证书；原choice专用桥范围不变，没有新对象公理、native_decide、宿主eval、预算或linter豁免。
- 2121文件SHA256回读一致，累计2844对精确足迹、23017项Internal显式声明覆盖。七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净，全部旧跟踪PPAC证明与AST未改。
- 独立readback递归比较全部旧布尔叶，零旧状态变化。新完成门只覆盖独立Fields图输入守卫、图界／字段界等价、真实头尾界、Nil／Cons递归、全部见证消去和ALL1仅Ω；字节执行总唯一、完整varint／byte-tree／Basic AST／schema／Con门保持false。

验收前基点867b9cd79c4788845945128647781741df74b228。本批9模块、4接入文件、6份文档；证据verification/summary.json、commands.json、build.log、audit.log、packet-byte-input-readback.json及.local/packet-byte-input-preaudit.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py；仅本地提交。

## 清理与编译

原native定向及独立预审计通过后、全仓编译前检查Lean／Lake进程0、停止0。逐绝对路径校验.local内非reparse普通文件后，删除3份被成功结果取代的失败日志、已并入Audit的临时驱动、已并入CheckStep4的片段和完成用途的一次性接入脚本，共6份、逻辑30296字节。窗口可用空间变化+45056字节，不等同于长期磁盘回收。路径／大小／SHA256见.local/packet-byte-input-precompile-cleanup.json。有效源码、工具链、缓存、有用复现脚本和应用服务保留；随后串行全仓验收，无磁盘阻塞。

## 后续agent工程流程表

| 顺序 | 具体实现与依赖 | 原核对象验收产出 | 状态 |
|---|---|---|---|
| T1.2c.3e.1d.2b.1-2 | 原双序列图、原限制、完整末行、内部长度分解 | 独立Bytes图和仅Ω的全内部准确递归 | 前批已验收 |
| T1.2c.3e.1d.2b.3a | 原Encoding／HasLength／完整Fields、全部字段小于256 | 独立ByteList输入守卫、真实头尾界及仅Ω的ALL1准确递归 | 本批已验收 |
| T1.2c.3e.1d.2b.3b.1 | 独立ByteList、实际Bytes递归、原Cons尾码严格界 | 固定联合对象矩阵，保留存在性／准确输入域／输出唯一三项内部IH | 下一单元 |
| T1.2c.3e.1d.2b.3b.2 | 原Foundation／完整Separation及联合矩阵 | 全部IH消去，实际Bytes全内部总唯一纤维定义域恰为ByteList∧自然tail | 待完成 |
| T1.2c.3e.1d.2b.4 | 原varint／readTokens规范约束及内部有序字节序列 | 独立终止／延续、末位非零、准确余输入公式，全部非标准长度 | 待完成 |
| T1.2c.3e.1d.2c | 规范字节序列、真实Tok递归及已证前缀联合逆唯一 | 实际Tok与规范LEB128前缀双向正式对应、非法候选处理 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词及模板 | 原Basic条件AST到纯关系式Condition正式桥接 | 待完成 |
| T1.2c.3e.2d | 原字节程序、准确结构递归及内部结构归纳 | 完整字节包，版本1／marker1、树／森林顺序及完整消费／拒绝 | 待完成 |
| T1.2c.3f／1.2d | 原ProjectEncode／Quotation、primitive subset及全公理模式 | 原编译器准确桥接、全内部Separation／Collection及目标3句公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输及内部Proof变换 | 待完成 |
| T4 | 全内部Con公式和原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

下一步可用一个固定Formula2联合矩阵P(w,n)同时包含：ByteList(w,n)下任意自然尾的输出存在性；任意实际Bytes接受推出ByteList(w,n)；相同尾部的两个实际输出相等。存在性用头字节guard、较小尾输入及实际256仿射总性构造；域方向用真实末步接受给头Byte及较小尾Bytes；唯一性用两份真实Cons字段自然性、原注入性和原仿射唯一性。严格尾码小于n由原Cons组件界实际证明，最终用原Foundation／Separation消去全部IH。不能只证明有效输入上的唯一性就跳过任意实际接受的准确输入域。

每批先独立trust=0及精确足迹，再串行全仓构建和类型检查，最后回读哈希、锁、全部既有布尔叶及提交字节。完整目标保持原nativeZF内部Con蕴含。
