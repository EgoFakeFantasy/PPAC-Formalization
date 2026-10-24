# 实际十规则Packet闭轨迹与仿射根分派验收（2026-10-25）

Packet实际十规则的关系式闭轨迹已验收：原Separation构造全部内部接受根集合，包含任意内部闭轨迹且自身闭合；仅Ω推出覆盖所有根候选的统一展开系统。原十规则的仿射根行准确分派到base／step，零点及后继接受已对象消去统一轨迹见证。12模块153声明、20组原nativeZF闭句；2180构建、23457审计（459无公理／22998允许依赖）、零警告；九命令／五trust=0通过，1960哈希、2610对精确足迹、21113项Internal覆盖。原Basic AST条件翻译、完整仿射算术等价、字节包、schema、Proof／解释及最终内部Con仍未完成。

## 背景、最终目标及准确层次

对象语言仍为纯等号／成员；背景为Contract.nativeZF及完整Separation／Collection；正式产出返回原YesMetaZFC.Logic.FirstOrder.Derives。完整目标保持：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

这是最终规格，完整内部Proof_T及上述蕴涵尚未证明。Proof_T须处理全部内部ω、六规则／27模式及完整公理模式。本批为原Rule驱动的纯关系式编译轨迹对象推导；它不自动证明原BasicSetTheory函数项／ObjectTrace.condition的AST翻译对应，也不代替最终Con。

## 规则表显式参数与实际Packet实例

HornClosedTraceSyntax将固定原Rule列表作为显式参数，定义：

~~~text
Closed_L(w,R) = ∀x (x∈R → Step_L(w,x,R))
Witness_L(w,r,R) = R⊆w ∧ (r∈R ∧ Closed_L(w,R))
Condition_L(w,r) = ∃R Witness_L(w,r,R)
Step_L = HornStepSyntax.step L
~~~

Step仍由原Rule的真实head、guards、premises和完整有界赋值application组成。PacketTraceSyntax的四个定义直接使用锁定原ObjectPacket.rules，保留其完整十规则及顺序。没有改名复用特化于ObjectSyntaxTransform.rules的旧condition／closed，也没有更换原规则表。

Generic Extension复用已有与规则表无关的集合包含／子集引理，使用Pairing／Union内部构造插入后的集合，以原规则的轨迹单调性保留闭合。所有根行及插入集合在对象量词内，不抽取宿主轨迹函数。

这里Closed为原条件的“每个轨迹成员均有一步支持”的方向。轨迹允许任意内部子集及无关行；本批不将其改为宿主有限运行，也不宣称它是最小固定点。后续算术sound证明仍必须排除任意内部闭轨迹中的错误仿射接受。

## 原Separation取得全部内部接受根

HornClosedTraceValueSyntax令Value_L(w,V)为从w按Condition_L(w,x)分离得到的实际集合。原Separation推出该V存在，且：

~~~text
x∈V ↔ (x∈w ∧ Condition_L(w,x))
Condition_L(w,x) → x∈w
x∈V ↔ Condition_L(w,x)
~~~

第二式直接由轨迹见证R⊆w及x∈R推出，因而第三式无需额外自然性前提。任意内部R⊆w及Closed_L(w,R)均推出R⊆V：每个x∈R沿同一个R即可得到Condition_L(w,x)，随后取得x∈V，没有选择外部见证。

对任意接受根，消去其内部R见证，使用Closed_at及R⊆V的单调性取得Step_L(w,x,V)。由此证明V自身Closed_L。反向若Step_L(w,x,V)，通过原Pairing／Union实际插入x，构造新的原轨迹见证得到Condition_L(w,x)。

Ω下，任意原规则application的头图推出其根自然，故统一展开不再外加x∈w：

~~~text
Ω(w) → Value_L(w,V) →
  ∀x (Condition_L(w,x) ↔ Step_L(w,x,V))

Ω(w) → ∃V (Value_L(w,V) ∧
  (Closed_L(w,V) ∧ ∀x(Condition_L(w,x) ↔ Step_L(w,x,V))))
~~~

所有根候选包括无效和非自然候选。非自然根另有对象拒绝定理；没有从全称范围删去它们。L固定为原Packet十规则即得到本批实际Packet统一系统存在，仅需Ω前提。

## 实际十规则的仿射分派

PacketAffineDispatchData对wide=0／1分别将其余八条规则分类：另一套仿射base／step加原规则表drop4。others只用于成员分类，实际Step继续使用原十规则原顺序。有限head标签元数据经核检查，未调用Expr.eval或宿主数值解码。

对任意其它规则的实际application，原有界arity块被完整消去，取得其真实头图和内部自然赋值。由标签外形及HornNodeDisjoint.node_contradiction，在对象层排斥给定仿射三字段根行。于是：

~~~text
Ω(w) → Row_i(w,d,t,n,r) →
  (Step_Packet(w,r,R) ↔
    (Application(base_i,w,r,R) ∨ Application(step_i,w,r,R)))
~~~

接上前批已完成的有界application双条件，Num_radix(B)下得到准确BaseOutcome／StepOutcome析取；V为本批实际统一轨迹值时，再与Condition统一展开组合：

~~~text
Ω(w) → Num_radix(B) → Value_Packet(w,V) → Row_i(w,d,t,n,r) →
  (Condition_Packet(w,r) ↔
    (BaseOutcome_i(w,B,r) ∨ StepOutcome_i(w,B,V,r)))
~~~

这是覆盖实际十规则的根行分派与真实结构输出接口，尚未把存在绑定的三个原参数通过字段注入性归一到指定d、t、n；后续需完成这个步骤，再消去内部归纳IH取得准确算术A。

## 统一轨迹见证实际消去的正向接受

PacketTraceCore.base_accept在对象EX中实际取得V，恢复原base应用、引入真实十规则一步，利用统一展开反向推出Condition。最终只需Ω、实际Num_radix(B)和BaseOutcome，不需要外加V或Closed证书。

PacketTraceCore.step_accept给出：

~~~text
Ω(w) → Num_radix(B) → Row_i(w,d,t,a,q) → Condition_Packet(w,q) →
Succ(s,t) → Sum(w,a,B,n) → Row_i(w,d,s,n,r) → Condition_Packet(w,r)
~~~

旧接受根由V成员双条件进入同一个内部V；实际原Entry前提、后继与addConst对应被组合成完整step应用，再得到新根Condition。V在对象EX内取得并消去，不预给轨迹选择函数或共享轨迹oracle。该后继定理尚未替代全内部tail归纳。

## 未完成事项与门禁

本批新增五项true门：显式表内部统一轨迹构造、实际Packet十规则关系式系统、全十规则仿射根分派、全内部根统一展开、消去V的base／successor接受。

原BasicSetTheory的ObjectTrace.condition使用ω函数项及有界存在于𝒫(ω)；本批Condition使用显式w和R⊆w的纯关系式公式。必须正式证明原函数图、powerset成员、有界量词和原模板实例的翻译对应；新的object_Packet_original_Basic_AST_condition_translation_proved保持false。

完整Condition↔affine A仍需字段注入归一、任意闭轨迹sound和内部ω归纳complete。object_Packet_actual_Horn_affine_condition_correspondence_proved继续false。完整NatPacket字节包、逆digit／quotient、规范LEB128、版本／marker／完整消费均待证明。原ProjectQuotation的primitive subset到纯成员展开和绑定移位也尚未桥接；完整schema、Proof／解释及最终Con继续false。

## 实际验收与清理

- 定向原native构建1985任务成功；全仓2180任务成功；九命令及五个--trust=0入口均退出0，零警告。
- 新增12模块153项显式声明全部覆盖；累计23457项声明审计：459无公理、22998仅含记录的允许依赖。
- 在允许名单接入前，独立预审计153项声明及20对精确core／native足迹。core精确保持propext／Classical.choice／Quot.sound，native精确再继承原七项固定证书；无新增对象Choice、自定义axiom、宿主求值或预算／linter豁免。
- 1960份文件SHA256独立回读一致；累计2610对精确足迹一致，21113项Internal显式声明覆盖。前批所有布尔完成门保持原值。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净；此前跟踪的PPAC证明和AST不变。
- 全仓编译前核对残留Lean／Lake进程0、停止0。本批定向运行均成功，没有被替代失败日志或可确认无用脚本，删除0；有效源码、缓存及有用生成／回读脚本保留。检查时C盘98024181760字节可用。

验收前基点4b7d048be18aaefcc8343cd07eae6759483b76c3。本批12模块、4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,packet-closed-trace-readback.json}，.local/packet-closed-trace-preaudit.json及.local/workspace-cleanup-packet-closed-trace-result.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交，未推送远端。

## agent工程流程表

| 顺序 | 实现与依赖 | 必须返回的对象接口 | 状态 |
|---|---|---|---|
| T1.2c.2 | 十二构造真实Compiler、原Foundation及Separation | 全内部准确源接受及类型唯一纤维 | 前批已验收 |
| T1.2c.3a／b | 原仿射算术、addConst／graph、完整Matrix、原有界arity应用 | 仿射递归式及准确application双条件 | 前批已验收 |
| T1.2c.3c.1a | 显式表Closed／Condition，原Separation及单调插入 | 实际Packet十规则统一内部轨迹及全候选展开系统 | 本批已验收 |
| T1.2c.3c.1b | 原Basic函数图、ω／powerset、bounded量词和原ObjectTrace模板 | 原Basic条件AST到实际纯关系式Condition的正式翻译对应 | 待完成 |
| T1.2c.3c.2a | 原十规则标签元数据、对象节点排斥、完整arity消去 | 仿射根只分派到正确两条原应用并取得真实结构析取 | 本批已验收 |
| T1.2c.3c.2b | 三字段构造器注入、内部EX参数／零元／后继对齐 | 指定根d、t、n的准确base／predecessor方程 | 下一步 |
| T1.2c.3c.3a | 本批无V前提base／successor接受、内部tail对象ω归纳 | A到全部内部仿射根接受，归纳IH及辅助见证消去 | 正向两步已验收，统一归纳待完成 |
| T1.2c.3c.3b | 准确根方程和任意内部闭轨迹；内部ω归纳 | 任意接受仿射根推出准确A，无外部良基／有限性前提 | 待完成 |
| T1.2c.3c.4 | 合并数学双向及原AST翻译 | 原完整Horn condition↔affine A，方可翻转全局门 | 待完成 |
| T1.2c.3d／e | 内部除法、实际十规则token／tree／forest／packet | 全内部规范字节包、完整消费及无效码拒绝 | 待完成 |
| T1.2c.3f／T1.2d | 原Project／subset降语言及完整公理模式数值程序 | 原字节源包到纯成员Compiler及完整理论测试 | 待完成 |
| T2／T3 | 六规则／27模式、内部Proof、原PPAC解释和证明码变换 | 实际checker准确性、原核推导传输及内部Proof转换 | 待完成 |
| T4 | 全内部无矛盾式和最终原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

每批在新增允许项前完成独立trust=0与精确足迹预审计，再接入全仓构建／类型检查，随后回读锁文件、哈希、前批门禁及本地提交的实际字节。仅在相应准确对象闭句证明后更新对应完成门。
