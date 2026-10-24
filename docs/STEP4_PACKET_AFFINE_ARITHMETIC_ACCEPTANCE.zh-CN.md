# 关系式Packet仿射算术全内部双向验收（2026-10-25）

关系式Packet仿射算术的全内部双向等价已验收：指定根的真实EX2／EX5字段经对象注入性归一，原ω归纳消去全部tail IH，统一轨迹和根行见证均对象消去；最终ALL3覆盖任意内部digit／tail／output，ALL4给出准确根条件对应，并取得实际128／256系统EX、有效输入输出存在唯一及无效候选拒绝。14模块154声明、20组原nativeZF闭句；2194构建、23611审计（460无公理／23151允许依赖）、零警告；九命令／五trust=0通过，1974哈希、2630对精确足迹、21267项Internal覆盖。原Basic AST翻译、完整NatPacket字节包、schema、Proof／解释及最终内部Con仍未完成。

## 背景与最终目标

对象语言为纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection，正式返回原YesMetaZFC.Logic.FirstOrder.Derives。完整目标不变：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

完整Proof_T须处理全部内部ω、原六规则／27模式及完整公理模式；它和最终Con尚未证明。本批完成原十规则驱动的纯关系式仿射子关系算术对应，没有把整个PPAC迁移改成这个子目标。

## 独立的接受关系与实际原核结论

本批接受关系独立定义为真实根存在且被原十规则的关系式轨迹接受：

~~~text
Accepted_i(w,d,t,n) = ∃r (Row_i(w,d,t,n,r) ∧ Condition_Packet(w,r))
A(w,B,d,t,n) = B∈w ∧ (d∈B ∧ (t∈w ∧ (n∈w ∧
  ∃p (Product(w,B,t,p) ∧ Sum(w,d,p,n)))))
i = 0 or 1; radix = 128 or 256
~~~

Accepted的定义没有引用A或算术答案。i／wide只索引原两套固定有限规则；digit、tail、output和全部见证始终为内部对象，不能把它们限制成模型外部标准自然数。

原nativeZF中的最终闭句包括：

~~~text
close(Ω(w) → Num_radix(B) → ∀d,t,n
  (Accepted_i(w,d,t,n) ↔ A(w,B,d,t,n)))

close(Ω(w) → Num_radix(B) → ∀d,t,n,r
  (Row_i(w,d,t,n,r) → (Condition_Packet(w,r) ↔ A(w,B,d,t,n))))

close(Ω(w) → ∃B ((B∈w ∧ Num_radix(B)) ∧
  (AllAcceptedArithmeticLaw_i(w,B) ∧ AllRootArithmeticLaw_i(w,B))))
~~~

ALL3保留所有内部数据候选，包括不满足digit界或tail／output自然性者；没有在右侧另加未证明的有效性oracle。有效d∈B及t∈w时，实际Accepted输出对象存在且标量唯一；无效digit、tail、output另有显式拒绝闭句。尚未证明的是从任意输出逆求digit／quotient，不把正向存在唯一冒充逆除法。

## 原EX字段的对象归一

BaseOutcome的两份内部见证为digit及零元；StepOutcome的五份内部见证为旧digit、前驱、旧输出、新tail和新output。RootBase／RootStep完整消去真实EX2／EX5，调用SyntaxNodeInjective.constructor_input_eq比较同一个原根行的三个字段。

对象等号替换把原存在digit对齐到指定d，后继字段对齐到指定t，和输出对齐到指定n。得到准确根方程：

~~~text
r∈V ↔
  ((Empty(t) ∧ (d∈B ∧ n=d)) ∨
    ∃p,a (Succ(t,p) ∧ (Sum(w,a,B,n) ∧ Entry_i(w,V,d,p,a))))
~~~

这里Ω、实际Num_radix(B)、V为前批实际统一接受根集合、Row_i(w,d,t,n,r)是显式前提。Entry继续是真实前提行及其V成员，没有被算术正确答案替换。

## 完整内部tail归纳

归纳性质固定为对象公式：

~~~text
Correct_i(w,B,V,t) = ∀d,n,r
  (Row_i(w,d,t,n,r) → (r∈V ↔ A(w,B,d,t,n)))
~~~

PacketAffineInductionSyntax.matrix是带w、B、V参数的有限Formula4。PacketAffineInduction直接使用ZFArithmetic.induction，即原对象ω后继归纳及该矩阵的完整Separation实例；没有对内部tail使用宿主Nat归纳、模型外部良基或标准性假设。

零点处，任何实际前驱都与Empty(t)矛盾；剩下原base分支与乘／加零律相合。后继处，先以原自然前驱唯一性对齐两份内部前驱，再用IH把真实Entry转成旧A，或由旧A实际构造前提根行及Entry。最后分别使用乘／加后继的advance／retreat。

归纳不是仅证明某个宿主给定序列：它推出全部内部t∈w上的Correct，内部d、n、r仍全称量化。source all_correct和最终membership_iff的签名没有IH前提。

sound方向包括任意内部闭轨迹：前批统一接受根集合包含任意内部闭轨迹，成员归纳因此比较所有可接受根。没有把原支持轨迹条件改成最小固定点或宿主有限运行。

## 统一轨迹和根码见证消去

PacketAffineAccepted.condition_iff实际通过原Separation在对象EX内取得V，应用完整内部归纳，将V成员与A对应，再利用前批成员↔Condition返回原关系式Condition。最终根定理不带V、Closed或IH前提。

Accepted正向消去其真实内部根r并应用上述根定理；反向从A的自然守卫取得d、t、n自然性，实际构造三字段根码，证明它被Condition接受，再引入Accepted。根码也在对象EX内取得并消去，没有宿主数据选择。

20组闭句经TheoryTransport.sentence及ZFReplay.replay返回原nativeZF，CheckStep4逐项验证返回类型。只有Ω的系统EX进一步实际取得128／256基数证书，消去外加基数见证前提。

## 信任及未完成边界

本批新增六项true门：准确根前驱方程、完整内部ω IH消去、关系式根Condition准确算术、全部内部Accepted双条件、实际字面量算术系统存在、实际Accepted正向执行存在唯一。此前跟踪门保持原值。

object_Packet_original_Basic_AST_condition_translation_proved仍false：原BasicSetTheory的ObjectHorn／ObjectTrace条件含ω函数项、powerset与有界量词，本批是显式w及R⊆w的纯关系式编译条件；原AST到该关系的形式对应仍须证明。因此保留给原Basic条件完整对应的object_Packet_actual_Horn_affine_condition_correspondence_proved继续false，并非本批关系式数学等价仍缺IH。

本批只覆盖原关系0／1的仿射子程序。原最终ObjectPacket.condition使用tag5的packet／tree输入，token／tree／forest／packet其余六条规则的完整字节程序尚未正确性验收。内部逆除法、规范LEB128、版本／marker／完整消费、无效包拒绝仍待证明。

结构树码、NatPacket字节包与纯成员Compiler继续区分；原ProjectQuotation的primitive subset展开及绑定移位尚未桥接。完整schema、Proof／数学解释和最终Con均未完成。

## 实际验收与清理

- 定向原native构建1999任务成功；全仓2194任务成功，九命令及五个--trust=0入口均退出0，零警告。
- 新增14模块154项显式声明全部覆盖；累计23611项声明审计：460无公理、23151仅含记录的允许依赖。
- 先独立预审计154声明及20对精确core／native足迹，再接入允许名单。core精确保持propext／Classical.choice／Quot.sound，native精确继承原七项固定证书。无新增对象Choice、自定义axiom、宿主eval、外部tail归纳、预算提高或linter豁免。
- 1974份文件SHA256独立回读一致，累计2630对精确足迹一致，21267项Internal显式声明覆盖；前批全部布尔完成门保持原值。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净；此前跟踪的PPAC证明及AST不变。
- 编译前检查遗留Lean／Lake进程0、停止0；删除3份已被成功native及trust=0预审计替代的失败日志，逻辑19354字节。该检查窗口可用空间净变动为-1437696字节，不能将逻辑删除量声称为实测等额回收；清理后C盘97961566208字节可用。有效源码、缓存和有用生成／回读脚本保留。

验收前基点63a9549dde43154a45201ad401a0f98b90056183。本批14模块、4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,packet-affine-arithmetic-readback.json}，.local/packet-affine-arithmetic-preaudit.json及.local/workspace-cleanup-packet-affine-arithmetic-result.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交，未推送远端。

## agent工程流程表

| 顺序 | 实现与依赖 | 必须返回的对象产出 | 状态 |
|---|---|---|---|
| T1.2c.2 | 十二构造真实Compiler、原Foundation及Separation | 全内部准确源接受及类型唯一纤维 | 前批已验收 |
| T1.2c.3a／b | 原仿射算术、addConst／graph、完整Matrix和有界arity应用 | 算术递归式与准确application双条件 | 前批已验收 |
| T1.2c.3c.1a／2a | 原十规则关系式统一轨迹、全部标签分派 | 全根候选展开及仿射根准确base／step分派 | 前批已验收 |
| T1.2c.3c.2b | 原EX2／EX5、三字段对象注入及等号传输 | 指定d、t、n的准确零点／前驱方程 | 本批已验收 |
| T1.2c.3c.3 | 原对象ω归纳、内部Entry双向构造、advance／retreat | 关系式Condition／Accepted↔A，全部内部数据与所有IH、V、根码见证消去 | 本批已验收 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset及bounded量词／模板实例 | 原Basic条件AST到实际纯关系式Condition正式对应，再合成本批A定理 | 待完成 |
| T1.2c.3d | 对内部输出的对象ω归纳、余数界及本批正向执行定理 | 128／256逆digit／quotient存在唯一；不得仅由正向唯一性推断 | 下一算术单元 |
| T1.2c.3e | 原十规则的tokenSmall／Large、tree／forest／packet及内部结构归纳 | 全内部规范LEB128、版本／marker、完整消费及无效包拒绝 | 待完成 |
| T1.2c.3f | 原ProjectEncode／Quotation及primitive subset降语言 | 原数值字节包到实际纯成员Compiler准确桥接 | 待完成 |
| T1.2d | 完整Separation／Collection模式及目标3句数值测试 | 全部内部码的准确原理论公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof、原PPAC解释和证明码变换 | 实际checker准确性、原核传输及内部Proof转换 | 待完成 |
| T4 | 全内部无矛盾式及最终原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

每批先独立trust=0与精确公理预审计，再接入全仓构建／类型检查；随后回读理论锁、哈希、前批门禁及本地提交的实际字节。仅在相应准确对象闭句证明后更新完成门。
