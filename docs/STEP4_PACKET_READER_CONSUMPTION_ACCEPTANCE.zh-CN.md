# reader真实输入投影与逐内部步消费对象验收（2026-10-25）

reader真实输入投影与逐内部步消费已验收：原始及带码转移取得真实单格Cons消费，余输入码严格属于旧输入码。每条实际历史边都有真实状态carrier，每个内部域索引都有实际唯一有效输入字段；所有内部步索引均取得后继及前后输入、真实Cons消费见证。Nil输入和原字节拒绝不能继续，Nil输入只能出现于末索引。10模块133声明、18组原nativeZF闭句；2452构建、26632审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。全局长度界／完整停止历史、EOF实际逆序、原reader程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 原理论、语言和最终目标

对象语言保持原纯EqMem，背景为完整ZF及完整Separation／Collection，证书返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。原19条Source规则经既有TheoryTransport.sentence和ZFReplay.replay传输；没有新增推导核、对象Choice、不可达、外部标准ω或外部良基前提。YesMetaZFC固定提交仍为 `039c8e132cc19671d73a3933c66b4799d2599dd6`。

最终目标始终是：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

Proof须覆盖全部内部ω（含非标准和无效码）、原六规则／27模式及完整ZF／目标公理模式。完整内部Proof／检查／编译、数学解释及最终Con主句均未证明。

## 实际单格消费与原码下降

未修改原State、Advance、状态四字段码、CodedStep或History。消费直接要求原HeadRest，包含真实自然头、有效尾及Cons：

```text
Tail(w,L,K) = ∃h HeadRest(w,L,h,K)
Input(w,n,L) = ∃v,s,a StateCode(w,L,v,s,a,n)
InputAt(w,f,i,L) = ∃n (Edge(f,i,n) ∧ Input(w,n,L))
```

原始LocalStep两个真实分支都给余输入r=rest；完整Advance中的两字段实际存在块经对象等词替换给Tail。原Cons组件定理和尾码自然性证明K∈L，得到对象自然码上的严格下降；没有用任意大小不等式替代真实Cons。

对任意真实源／目标StateCode，带码步先在源实际字段上准确归一，再消去完整目标存在块，并以原状态码字段注入性对齐实际目标输入；因此同一Tail关系及严格K∈L传到全部接受的带码步。仅需Ω及实际投影／接受前提，未要求外部给定128余数界或正scale。

## 历史所有内部索引的实际唯一输入

Input是原状态码的真实第一字段投影，码字段注入性取得唯一性；StateCarrier实际给有效输入存在。

对每个实际历史边Edge(f,i,N)，先从原完整functionOn域及自然后继域取得内部i∈ω，再用原内部零／后继分解：空索引对齐真实seed，后继索引通过原后继域阈值取得实际前驱行。真实Row目标与该边经图单值性对齐，取得N的实际StateCarrier。这里没有把模型的ω当外部标准自然数，也没有外部递归解包历史。

每个实际i∈d随后取得对象公式的唯一有效输入纤维：

```text
∃L ((ValidList(w,L) ∧ InputAt(w,f,i,L))
     ∧ ∀K (InputAt(w,f,i,K) → K=L))
```

实际图边存在由原SequenceLogic.value_at取得；码、输入字段及唯一性见证均在对象量词内取得和消去，没有Lean Type数据抽取。

对于所有内部i∈l，原核还证明：

```text
∃j,L,K (Succ(j,i) ∧ InputAt(w,f,i,L) ∧ InputAt(w,f,j,K) ∧ Tail(w,L,K))
```

不要求外部预先给出后继或前后输入。对于任意已给的实际相邻输入投影，取得同一真实Tail及严格K∈L；所有步的消费公式由对象全称量词统一覆盖。

## 停止边界和明确缺口

真实源代码的原Admissible失败会禁止任何下一带码步；Nil输入和原非规范字节拒绝分别给出该结论。对历史中的实际InputAt，Nil输入不能属于逐步域；若该索引属于完整历史域，则必等于末索引。

Nil无下一步不代表EOF必成功；EOF守卫仍可能失败，实际返回的acc.reverse尚未构造。本批未取得全局长度界、完整停止历史存在唯一、完整输入消费／初始化不变量、原reader到Bytes／Canonical程序桥、Basic AST或最终Con。严格相邻下降和逐索引消费不能替代这些终点。

原raw reader的任意Nat字节和scale=0范围保持；没有把byte<256或scale>0暗加为原状态定义域。所有内部及无效候选均保留对象量词范围。

## 模块、证书和实际验收

新模块：PacketReaderConsumptionSyntax, PacketReaderConsumptionTransport, PacketReaderRawConsumption, PacketReaderInputProjection, PacketReaderCodedConsumption, PacketReaderHistoryStates, PacketReaderHistoryInput, PacketReaderHistoryConsumption, PacketReaderConsumptionStopping, ObjectPacketReaderConsumption。133项显式def／theorem，18组Source闭句／原sourceZF核证书／原nativeZF证书，均已接入PPAC导入、Audit全部声明审计、CheckStep4逐组原核fixture及scripts/verify.py独立消费守卫。全部旧跟踪PPAC证明、AST、原规则及原状态／历史定义保持。

- 定向构建2191 jobs，零警告；133项新增声明trust=0预审计与清单精确对应。
- scripts/verify.py：2452构建任务、26632项审计（484无公理／26148允许依赖），零警告。
- 九命令与五个trust=0入口全部退出0；2232份独立工作区哈希一致，3001对精确核／native足迹，24288项Internal显式声明覆盖。
- 18组新增核证书足迹准确为propext／Classical.choice／Quot.sound；native证书准确加底座已有七项FreeClosed证书。无新axiom、native_decide或允许依赖扩大，不宣称底座七项已消除。
- 全部旧布尔叶递归比较不变。新增真实输入投影／相邻消费门true，旧组合门中的完整停止历史、EOF逆序、reader程序桥、Basic AST、Proof／解释及Con保持false。
- 七个可信基／规则／理论／配置锁及YesMetaZFC固定提交未变，其工作树干净。本批精确20文件只做本地提交。

验收证据：`verification/packet-reader-consumption-readback.json`、`verification/summary.json`、commands／build／audit日志及 `.local/packet-reader-consumption-preaudit.json`。accepted_commit字段从提交后Git字节回读取得。

## 清理与编译

清理前枚举0个Lean／Lake编译进程，停止0个；核对绝对路径位于工作区、为普通文件且非reparse后，删除4个本轮失败日志及已整合临时文件，共27685逻辑字节。该窗口实测空闲变化-2953216字节，仅报告观测值。删除前SHA256／绝对路径清单见 `.local/packet-reader-consumption-precompile-cleanup.json`。保留源代码、依赖、工具链、必要缓存与验收证据，清理时可用约90.38 GiB；随后单线程串行全仓验收通过。

## 后续工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、真实输入Cons及完整单步 | 准确域／类型／联合唯一及原四类观察、数字特化 | 已验收 |
| R3a | 状态码、带码步、独立历史及追加／比较 | 实际编码／准确带码步／真实零步与追加；全内部共同索引一致及同长度端点唯一 | 已验收 |
| R3b.1 | 实际状态输入投影和逐内部索引单格消费 | 每个真实边／域索引有实际状态和唯一有效输入；每步真实Cons及严格下降；Nil／拒绝停止边界 | 本批已验收 |
| R3b.2a | 全索引严格下降及原自然数序 | 原核内取得全局消费／长度界，处理全部内部及非标准长度，不把外部良基用于取最短运行 | 下一单元 |
| R3b.2b | 输入界、真实历史构造及完整Foundation／Separation | 完整停止历史存在唯一，严格分开追加闭包与任意长度无条件存在 | 待完成 |
| R4 | EOF实际逆序、原初始化及规范varint分段 | 实际acc.reverse及准确返回／拒绝，value／scale／acc与原程序顺序对应 | 待完成 |
| R5 | reader、Bytes／Canonical／Tok和原Basic AST | 全内部程序／规格双条件、完整字节包及AST桥，含全部无效码 | 待完成 |
| P／I／C | 原六规则／27模式及完整ZF／U公理 | 内部Proof／检查／编译、完整数学解释、原nativeZF内部Con蕴含 | 待完成 |


下一单元将全部逐步严格输入下降汇总成原核内的全局界，再结合真实历史构造建立完整停止历史。不能将Nil只在末索引、码下降或已接受前缀的确定性误记为任意初始状态的终止证明。

下一关拟定的原核规格（尚未实现、未计入本批验收）：给定初始实际输入L0及原HasLength(w,L0,t0)，对任意实际历史索引i、输入InputAt(w,f,i,L)与原HasLength(w,L,ti)，证明原加法Sum(w,i,ti,t0)。由ti的自然性取得i≤t0及历史长度界。再以内部ω归纳构造“已有停止历史或具有指定长度的真实前缀”，在t0+1处用长度界排除仍在运行的前缀分支；停止索引／端点唯一性须结合本批之前的共同索引确定性与无下一步边界。这些均为后续工程计划，完整停止存在唯一仍未证明。
