# 原Packet结构规则完整正向展开验收（2026-10-25）

原tree／forestNil／forestCons／packet四条完整局部矩阵及正向应用已验收：arity7／1／6／3、空guard、全部head字段和有序前提保持原样；rawNode、Nil、Cons／后继及单位见证对象消去。完整有界应用与保留原自然性／搜索界的结构结果双向等价，并推出无搜索界的正向结果；tag3／4／5按完整原十规则准确分派。仅Ω对象构造同一个规范接受集合及ALL4／ALL5／ALL3三类根定律。13模块196声明、13组原nativeZF闭句；2274构建、24558审计（471无公理／24087允许依赖）、零警告；九命令／五trust=0通过，2054哈希、2744对精确足迹、22214项Internal覆盖。全部既有布尔叶原值保持。指定根字段归一、联合tail界、反向搜索界消去、完整字节程序、原Basic AST桥、schema、Proof／解释及最终Con仍未完成。

## 对象合同与最终目标

对象语言保持原纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection；证书返回原YesMetaZFC.Logic.FirstOrder.Derives。没有新推导核、对象Choice、公理或不可达前提。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

全内部Proof_T仍须准确覆盖任意内部ω、原六规则／27模式及完整公理模式，包含非标准及无效码。本批只完成原结构规则的对象正向展开与有界局部规范化；内部Proof、数学解释及最终Con尚未证明。

## 四条原规则及数值局部式

源是锁定YesMetaZFC.Automation.ObjectPacketGraph中的实际四条Rule，未重写表或改arity。原十规则表和全部源码锁不变。

| 原规则 | arity | head与原有序前提 | 本批辅助见证 |
|---|---|---|---|
| treeRule | 7 | Row3(rawNode(v0,v1),v2,v3)；Forest(v1,v4,v2,v5)、Tok(v4,v5,v6)、Tok(v0,v6,v3) | 实际Raw(v0,v1,n)，对象EX1 |
| forestNil | 1 | Row4(Nil,0,v0,v0)；无前提 | 空集z及后继e=z+1，Nil=e；对象EX2 |
| forestCons | 6 | Row4(Cons(v0,v1),succ(v2),v3,v4)；Forest(v1,v2,v3,v5)、Tree(v0,v5,v4) | 实际Cons码n及后继s；对象EX2 |
| packetRule | 3 | Row5(v1,v0)；Affine256(1,v2,v1)、Tree(v0,1,v2) | 实际Num1(e)，对象EX1 |

四条guard全部为空，所有head和premise的表达式仍引用原固定Rule。Forest与Tree在此表中是对同一个内部轨迹V的准确tag4／tag3行成员公式；Tok是原tag2行成员公式，尚未在本批消去V而改为统一的独立结构接受谓词。Row3／Row4／Row5分别有3／4／2个字段，名字中的数字表示原tag，不是arity。

PacketStructureMatrix在已给定实际结构见证时证明完整原局部matrix双条件；PacketStructureLocal内部构造这些见证，并在原EX中消去。最终四份局部双条件只需Ω与原env自然性，没有外部rawNode、Nil、Cons、后继或单位运行oracle。

PacketStructureExpr使用原HornExprConstructor及完整有限字段图对应，并对真实premise的EX行成员关系作对象同余。所有运行值、行码和轨迹都是任意内部集合；仅固定表达式、有限Branch四种规则索引与Family三种tag索引在宿主层用于构造公式和证明证书。最终系统显式同时包含全部三种Family，没有把内部运行数据外部化。

## 完整有界应用与正向展开的区别

```text
Local_b(w,V,r,env) = 本批准确结构数值式，含对象EX辅助见证
BoundedOutcome_b = ∃env (Nat(env) ∧ Bound_r(env) ∧ Local_b)
Outcome_b = ∃env Local_b
ZF ⊢ Ω(w) → (OriginalApplication_b(w,r,V) ↔ BoundedOutcome_b(w,V,r))
ZF ⊢ Ω(w) → (OriginalApplication_b(w,r,V) → Outcome_b(w,V,r))
```

env存在块长度始终是原7／1／6／3；Nat与Bound均直接使用原environmentNat／environmentBound，Bound是每项赋值不超过原根行码的准确搜索条件。反向构造OriginalApplication时，这两组guard由同一对象见证保留，并未偷偷假定它们可从无界Local推出。

因此本批没有证明Outcome_b→OriginalApplication_b；这需要后续联合tail界和实际head数值界来消去全部辅助赋值搜索界。该缺口与本批已完成的准确有界双条件分开标记。

## 原十规则分派及全部内部根

对任意实际tag3／tag4／tag5根行，读取完整原十规则step。非匹配Rule通过实际head外标签分类及原节点不交性逐一排除。匹配规则恰为tree、forestNil／forestCons、packet；守卫、字段和前提没有调整。

对每个Family，App_f是对应一条或两条原application的准确析取，B_f和O_f分别把它们替换为BoundedOutcome和Outcome。本批得到：

```text
ZF ⊢ Ω(w) → Row_f(w,xs,r) → (PacketStep(w,r,V) ↔ App_f(w,V,r))
ZF ⊢ Ω(w) → Value_Packet(w,V) → Row_f(w,xs,r) →
       ((Condition_Packet(w,r) ↔ B_f(w,V,r)) ∧
        (Condition_Packet(w,r) → O_f(w,V,r)))
```

PacketStructureSystemSyntax把xs全部字段和根r分别放进ALL4、ALL5、ALL3；全部内部集合候选，包括非法候选和非标准自然数均保留。Row_f作为实际形状前提，不把外部标准有效输入当作全称域。

```text
ZF ⊢ Ω(w) → ∃V (Value_Packet(w,V) ∧
       AllLaw_tree(w,V) ∧ AllLaw_forest(w,V) ∧ AllLaw_packet(w,V))
```

规范V由原Separation所构造的PacketTraceCore.exists_value取得；三份定律使用同一个V。最终exists_system仅需Ω，没有外部V、字面量或模型前提。源形式化证书经TheoryTransport.sentence与ZFReplay.replay返回原nativeZF闭句。

指定根与实际展开见证的各个输入／tail／output字段虽然共同出现在真实构造器等式中，本批没有继续逐一用constructor_input_eq替换归一到指定字段；这留给下一单元。不能将此处根条件展开称为已完成实际tree／forest的全部无界递归式。

## 实际验收

- 原native定向2079任务成功；全仓2274任务成功。九条命令全部退出0，其中五个--trust=0入口；零警告。
- 新增13模块196个显式声明先独立预审计，随后正式Audit完整覆盖；累计24558审计，471无公理、24087仅含记录的允许依赖。
- 新增13组core／native精确足迹：core恰为propext／Classical.choice／Quot.sound，native恰额外继承原七项固定闭句证书。choice专用桥和理论基线没有扩大；未新增对象公理、宿主eval、native_decide或预算／linter豁免。
- 2054份文件SHA256回读一致，累计2744对精确足迹、22214项Internal显式声明覆盖。七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净。原跟踪PPAC证明和AST未改。
- 递归比较全部既有布尔叶，无旧值变化；新增完成门仅覆盖四条局部矩阵、准确有界应用、正向应用、三tag分派和全内部正向根系统。新设指定根字段归一／联合tail界／无界反向搜索界完成门均为false。原Basic AST、完整字节包、schema、Proof和Con相关门保留未完成。

验收前基点71e8bb8f47610d7530529297cdb3decf03142153。本批13模块、4个接入文件、6份文档。证据verification/summary.json、commands.json、build.log、audit.log、packet-structure-readback.json及.local/packet-structure-preaudit.json；复验C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交。

## 清理及编译状态

定向构建与独立预审计成功后、全仓编译前确认Lean／Lake进程0，停止0。逐路径校验.local内非reparse的明确白名单，删除5份被成功定向结果取代的失败日志，以及已并入Audit／CheckStep4的临时审计驱动和检查片段，共7份、逻辑44680字节。窗口可用空间变化+61440字节，不能等同于长期磁盘回收。回执.local/packet-structure-precompile-cleanup.json保留路径、大小、SHA256与前后空间；有效源码、工具链、缓存和有用复现脚本保留。随后串行完成本批全仓编译，没有磁盘阻塞。

## 后续agent工程流程表

| 顺序 | 实现与依赖 | 原核对象验收产出 | 状态 |
|---|---|---|---|
| T1.2c.3e.1a-d.1 | 真实Tok准确递归、原商归纳及数值比较 | 实际输出存在唯一、input及tail不超过output | 前批已验收 |
| T1.2c.3e.2a.1 | 原结构四规则、原表达式图及全部赋值 | 完整局部式、准确有界双条件、正向应用、三tag分派及仅Ω根系统 | 本批已验收 |
| T1.2c.3e.2a.2 | 本批EX7／1／6／3展开、原constructor_input_eq及对象等号替换 | 指定tree／forest／packet根与所有实际head字段对齐；准确固定根正向递归式 | 下一单元 |
| T1.2c.3e.2b | 指定根展开、原结构分量严格子码界、固定联合Formula及原Foundation／Separation | 实际Tree／Forest联合tail≤output；全部内部子码IH对象消去 | 待完成 |
| T1.2c.3e.2c | 已证Tok界、联合tail界及原head数值界 | 全部辅助赋值搜索界消去，Outcome↔OriginalApplication且保留非法候选 | 待完成 |
| T1.2c.3e.1d.2 | 原varint／bytes、规范序列和真实Tok | 规范LEB128／前缀消费正式对应、无效候选拒绝 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词和模板 | 原Basic条件AST到纯关系式Condition正式桥接 | 待完成 |
| T1.2c.3e.2d | 准确结构应用、联合归纳、字节序列及原marker | 全内部完整字节包、版本／marker／完整消费及拒绝 | 待完成 |
| T1.2c.3f | 原ProjectEncode／Quotation及primitive subset降语言 | 原数值字节包到实际纯成员Compiler准确桥接 | 待完成 |
| T1.2d | 完整Separation／Collection模式及目标3句 | 全内部码准确原理论公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输及内部Proof变换 | 待完成 |
| T4 | 全内部无矛盾式及原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

联合归纳必须在对象层按真实结构码分量下降：Tree的payload森林子码、ForestCons的tree子码与forest尾子码均由原数值构造器内部严格子码界取得。先在同一个固定对象Formula中同时处理Tree／Forest的tail性质，再通过原Foundation／Separation消去IH；不得把内部ω假成宿主标准Nat，也不能把Tree-tail或Forest-tail的一方作为另一方的未证oracle。已证明的Tok-tail数值界只在真实Tok接受前提下使用。

每批先独立trust=0与精确足迹，再串行全仓构建和类型检查，最后回读哈希、锁、全部既有布尔叶及提交字节；所有边界按实际原核推导分别标记。
