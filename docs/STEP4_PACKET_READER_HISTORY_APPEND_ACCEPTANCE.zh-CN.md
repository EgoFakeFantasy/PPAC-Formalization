# reader历史追加与全内部索引确定性对象验收（2026-10-25）

reader历史追加及全内部索引确定性已验收：原序列追加真实取得新图，旧图精确为新图的旧域限制，全部旧行保留并加入真实带码末步。固定对象Formula3经原ω归纳和完整Separation消去全部比较IH；同一起点任意两段内部历史的共同实际索引值相同，同内部长度的末状态码唯一，实际索引自然性从原图定义域取得。8模块88声明、15组原nativeZF闭句；2442构建、26499审计、零警告，九命令／五trust=0通过；仅旧历史追加／确定性子门false→true，其余旧布尔叶保持。输入消费／完整运行、EOF实际逆序、原reader程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 原对象合同与最终目标

语言保持原纯EqMem，背景为完整ZF及完整Separation／Collection，证书返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。原19条Source规则经既有TheoryTransport.sentence与ZFReplay.replay传输，未增加推导核、对象Choice、不可达、外部标准ω或外部良基假设。YesMetaZFC固定提交仍为 `039c8e132cc19671d73a3933c66b4799d2599dd6`。

最终目标不变：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

内部Proof须覆盖全部内部ω（包括非标准和无效码）、原六规则／27模式及完整ZF／目标公理模式。专用内部Proof、全内部检查／编译、数学解释与最终Con主句均未证明。

## 实际追加闭包

沿用未改动的原State、状态四字段码、CodedStep和独立History。若History(w,B,z,o,n,r,l,d,f)、实际CodedStep(r,s)及Succ(e,d)，则对象层实际构造同一个新图g，联合满足：

```text
Append(g,e,f,d,s,w) ∧ History(w,B,z,o,n,s,d,e,g)
```

Append保持原完整functionOn、自然值域、精确新边和旧域限制。每个旧Row的两条真实边由图包含迁移，带码步原样保留；新末行使用原Succ(d,l)、真实旧末边及实际新边，不用最终答案倒定义轨迹。

这对全部内部长度及全部实际接受的g成立，不预设外部标准长度；但它是给定真实下一步后的追加闭包，不是每个长度都无条件存在有效reader运行。

## 固定Formula3的全内部比较

比较矩阵仅用两个实际图及一个内部索引：

```text
Agree(f,g,i) = ∀a,b (Edge(f,i,a) → Edge(g,i,b) → a=b)
AllAgreement(w,f,g) = ∀i∈w Agree(f,g,i)
```

对于任意同一源状态码n出发的两段History（长度可不同），原ZF中已经完成：

1. 任意内部空索引由空集唯一性对齐到真实零seed；原图单值性取得同一初值。
2. 后继比较从两张真实目标边取得原functionOn的精确定义域，用内部后继阈值推导前驱确实属于两段历史的逐步域，再取得两份完整实际Row。
3. 两份三字段Row存在块实际消去；两个后继索引与真实目标索引对齐，图单值性对齐当前输出；前驱Agree对齐两个源状态码，再由已验收CodedStep唯一性比较新状态码。
4. 原ZFArithmetic.induction使用该固定Formula3的完整Separation实例，证明AllAgreement并消去全部IH。没有Lean宿主Nat归纳或任何剩余比较假设。
5. 对任意实际共同边，索引自然性从原图定义域及自然后继域导出，不作为额外输入前提；故全部实际共同索引值唯一。两段历史长度相同时，真实末边给末状态码相同。

主接口all_agreement只要求Ω、B∈ω及两份真实历史；共同边接口不要求外部给定索引范围，端点唯一接口不要求预先给出两图相等。固定4／3字段数是公式元数据；运行时索引／长度仍是内部对象。原Num128也给AllAgreement的准确对象特化。

完整消费、停止历史存在与唯一、EOF实际acc.reverse及原reader程序对应仍未完成。此处的历史是执行前缀，不能凭追加闭包或确定性宣称程序终止或最终内部Con已证明。

## 模块和实际验收

新模块：PacketReaderHistoryRowMap, PacketReaderHistoryAppend, PacketReaderHistoryAgreementSyntax, PacketReaderHistoryAgreementRows, PacketReaderHistoryAgreementPoint, PacketReaderHistoryAgreementInduction, PacketReaderHistoryUnique, ObjectPacketReaderHistoryAppend。88个新增显式def／theorem，15组Source闭句／原sourceZF核证书／原nativeZF证书；全部接入PPAC导入、Audit全声明、CheckStep4逐组原核fixture和scripts/verify.py独立守卫。全部旧跟踪PPAC证明、AST、State／CodedStep／History定义及原规则不变。

- 定向构建2182 jobs，零警告；88项新增声明trust=0预审计与清单精确对应。
- scripts/verify.py：2442构建任务、26499项审计（484无公理／26015允许依赖），零警告。
- 九命令及五个trust=0入口全部退出0；2222份独立工作区哈希一致，2983对精确原核／native足迹，24155项Internal显式声明覆盖。
- 15组新增核证书足迹准确为propext／Classical.choice／Quot.sound，native证书准确继承底座七个原FreeClosed证书；没有新增axiom、native_decide或扩大允许范围，不宣称底座七项已消除。
- 独立回读递归比较全部旧布尔叶，仅 `Packet_reader_state_code_coded_step_history_base_guard.arbitrary_length_history_append_and_determinism` false→true，其余旧值保持。输入消费／完整运行、EOF逆序、reader程序桥、Basic AST、Proof／解释及最终Con门保持false。
- 七个可信基／规则／理论／配置锁未改，YesMetaZFC提交及工作树干净。本批精确18文件仅本地提交，未自动发布。

证据：`verification/packet-reader-history-append-readback.json`、`verification/summary.json`、commands／build／audit日志及 `.local/packet-reader-history-append-preaudit.json`。accepted_commit字段由提交后Git字节回读取得。

## 清理后再编译

清理前枚举0个Lean／Lake编译进程，停止0个。核对每个绝对路径在工作区内、为普通文件且非reparse后，删除本轮5个失败／旧警告日志及已整合临时文件，共23950逻辑字节。窗口实测空闲变化32768字节，仅报告观测值。删除前SHA256和绝对清单见 `.local/packet-reader-history-append-precompile-cleanup.json`。保留源代码、依赖、工具链、必要缓存及验收证据；清理时可用约90.33 GiB，随后单线程串行完成全仓验收。

## 后续工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、真实输入Cons、完整单步与四类观察 | 类型保持、准确域、四项联合确定性及原数字特化 | 已验收 |
| R3a.1 | 原状态四字段码、带码步与独立历史 | 编码准确域／唯一／注入；带码步准确归一／唯一／准确域；真实零步历史 | 已验收 |
| R3a.2 | 原序列追加、所有旧行与新末行、固定比较矩阵 | 真实延长历史、旧域精确限制；全内部共同索引一致、同长度端点唯一；全部IH原ω归纳消去 | 本批已验收 |
| R3b.1 | 每个带码步的真实原Cons余输入 | 从实际状态字段解码取得严格输入tail下降；逐内部索引消费对应及拒绝／停止边界 | 下一单元 |
| R3b.2 | 输入下降、历史构造、完整Foundation／Separation | 全内部完整停止历史存在唯一及完整消费；不能把一步追加闭包误当任意长度无条件运行 | 待完成 |
| R4 | EOF实际逆序、原初始化及规范分段 | 构造acc.reverse及准确返回／拒绝；原varint与value／scale／acc顺序对应 | 待完成 |
| R5 | reader、Bytes／Canonical／Tok及原Basic AST | 全内部程序／规格双条件、完整字节包及AST桥，含无效码 | 待完成 |
| P／I／C | 原六规则／27模式、完整ZF／U公理 | 内部Proof／检查／编译、完整数学解释、原nativeZF内部Con蕴含 | 待完成 |


下一单元从真实带码步的实际原Cons取得严格余输入下降，并将每个内部索引的状态码投影到实际输入列表；再证明完整消费和停止历史。不得从本批共同索引确定性跳过完整运行、实际EOF逆序或原Basic AST。
