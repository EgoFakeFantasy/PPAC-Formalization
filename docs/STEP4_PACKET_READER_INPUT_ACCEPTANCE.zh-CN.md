# 原readTokens完整输入单步对象验收（2026-10-25）

原readTokens完整输入单步已验收：当前输入与真实Cons(head,rest)绑定，原有限列表Nil／Cons分解取得头尾，原注入性对齐并消去全部见证。完整状态类型保持、四项后继联合唯一；后继存在准确等价于原状态合法、非Nil且真实头字节未拒绝。EOF守卫通过／失败、字节拒绝和后继存在四类覆盖且互斥，观察定义域准确为原始State；保留全部内部及无效候选，不限制byte<256或scale>0。8模块121声明、16组原nativeZF闭句；2423构建、26275审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。完整执行历史／消费、EOF实际acc.reverse、readTokens↔Bytes／Canonical、Basic AST、Proof／解释及最终Con仍未完成。

## 原对象合同和完整目标

语言保持原纯等号／成员签名。背景为完整ZF及完整Separation／Collection；证书返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。Source.Derives原19规则经既有TheoryTransport.sentence和ZFReplay.replay传输，没有新增推导核、对象Choice、不可达假设、标准ω或模型外部良基前提。源锁定YesMetaZFC提交仍为 `039c8e132cc19671d73a3933c66b4799d2599dd6`。

最终目标未变：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

内部Proof须覆盖全部内部ω（包括非标准和无效码）、原六规则／27模式、完整ZF／目标公理及模式。专用内部检查／编译、数学解释和最终Con主句均未证明。

## 完整输入公式及实际推导

上批局部Step只接受给定head／rest。本批将当前完整输入l纳入独立单步矩阵，未修改旧State、局部Step、Tok／Bytes／Canonical／Prefix或原Packet十规则：

```text
HeadRest(w,l,b,x) = b∈w ∧ ValidList(w,x) ∧ Cons(w,b,x,l)
HasHead(w,l) = ∃b,x HeadRest(w,l,b,x)
Blocked(w,B,z,o,l,s) = ∃b,x (HeadRest(w,l,b,x) ∧ Reject(B,z,o,b,s))
Advance(w,B,z,o,l,v,s,a,r,y,q,c) =
  State(w,l,v,s,a) ∧ ∃b,x (HeadRest(w,l,b,x) ∧ LocalStep(w,B,z,o,b,x,v,s,a,r,y,q,c))
ExistsResult(w,B,z,o,l,v,s,a) = ∃r,y,q,c (State(w,r,y,q,c) ∧ Advance(...))
Admissible = State(w,l,v,s,a) ∧ ¬Nil(w,l) ∧ ¬Blocked(w,B,z,o,l,s)
EOFPass = State(w,l,v,s,a) ∧ Nil(w,l) ∧ (s=o ∧ v=z)
EOFFail = State(w,l,v,s,a) ∧ Nil(w,l) ∧ ¬(s=o ∧ v=z)
Outcome = EOFPass ∨ EOFFail ∨ (State ∧ Blocked) ∨ ExistsResult
```

原始readTokens可接收任意Nat字节和scale=0；本批及所有原核闭句保留此范围。字节<256和由初始scale=1得到的正性属于后续程序不变量，未暗加到原定义域。

实际对象推导包括：

1. 原valid_decomposition给出Nil或真实自然head与有效rest；两个真实Cons分解的head／rest经原注入性联合相等，内部头尾见证实际消去。
2. 对任意给定实际HeadRest，完整Advance精确等价于原State与该实际head／rest的LocalStep；Blocked精确等价于该头的Reject。两份存在块并非用宿主选择抽取。
3. 原Nil不允许Advance或Blocked；非法原State不允许任何Advance。完整Advance保持后继State，全部四项输出联合唯一，不再要求外部给定head／rest。
4. 在Ω与自然B／z／o下，ExistsResult↔Admissible对全部内部原输入及候选成立。反向利用原有效列表分解、实际未拒绝局部更新和四项后继对象见证；正向实际排除Nil和Blocked。
5. Outcome↔State，且四类分派互斥：EOFPass与EOFFail守卫相反；Nil与Blocked／ExistsResult互斥；Blocked与ExistsResult互斥。全部无效状态的观察域准确排除。
6. 原Num128 B、Num0 z、Num1 o通过SyntaxNumerals.range取得准确自然范围，并在原核中给出精确后继域和四类分派的原数字特化。

EOFPass／EOFFail只是原分支守卫的观察，未构造Option返回值或acc.reverse。完整内部运行历史、初始化不变量和原reader程序统一正确性仍未证明；单步结果不能代替完整程序桥。

## 文件和审计覆盖

新模块：PacketReaderInputSyntax, PacketReaderInputFields, PacketReaderInputTransport, PacketReaderInputNormalize, PacketReaderInputStep, PacketReaderInputExistence, PacketReaderInputOutcomes, ObjectPacketReaderInput。新增121个显式def／theorem，16组Source闭句／原sourceZF核证书／原nativeZF证书。PPAC导入、Audit全部显式声明、CheckStep4每组原核fixture及scripts/verify.py独立完整输入单步守卫已接入。

全部旧跟踪PPAC源码与AST不变；原局部Step、Canonical、Prefix、Bytes、Tok、规则、数字、算术与列表核保持。新增判定使用全部内部集合／自然候选量词，没有外部有界回放或标准自然数归纳替代。

## 实际验收结果

- 定向原核模块构建2165 jobs，零警告；121项新增声明在trust=0预审计中与清单精确对应。
- scripts/verify.py：2423构建任务、26275项声明审计，其中482无公理／25793允许依赖，零警告。
- 九条命令全部退出0，五个trust=0入口全部通过。2203份独立工作区哈希一致；2953对精确核／原生足迹；23931项Internal显式声明覆盖。
- 16组新增核证书足迹准确为propext／Classical.choice／Quot.sound；native证书准确继承底座七个原FreeClosed证书。没有新增native_decide、公理或扩大允许依赖；不宣称已经消除底座七项证书。
- 全部旧布尔叶递归比较不变。新完整输入单步门true；完整历史、EOF实际逆序、readTokens程序桥、Basic AST、Proof／解释及最终Con保持false。
- 七个配置／理论／规则／可信基锁未改，YesMetaZFC固定提交与工作树干净。本批精确18文件仅本地提交，不自动发布。

验收证据：`verification/packet-reader-input-readback.json`、`verification/summary.json`、commands／build／audit日志及 `.local/packet-reader-input-preaudit.json`。提交号从readback的accepted_commit字段独立回读。

## 清理后再编译

编译前检查0个Lean／Lake编译进程，停止0个。验证每个绝对目标位于工作区内、为普通文件且非reparse后，删除本轮4个失败日志／已整合临时文件，共33983逻辑字节。该清理窗口实测空闲变化-167936字节，仅报告观测值；删除前SHA256与绝对路径见 `.local/packet-reader-input-precompile-cleanup.json`。保留源文件、依赖、工具链、必要缓存与验收证据。清理时可用约90.53 GiB；随后单线程串行完成全仓验收。

## 后续工程流程

| 单元 | 实现职责 | 原核交付要求 | 状态 |
|---|---|---|---|
| R1 | 给定head／rest，原value／scale／acc及128／0／1 | 无界局部更新、真实Cons累积、类型保持、后继确定性／准确域 | 已验收 |
| R2 | 完整当前输入l与原Cons(head,rest) | 真实头尾内部取得、对齐、消去；完整状态单步准确域／四项联合唯一；Nil／Cons及四类分派 | 本批已验收 |
| R3a | 完整状态四元组、原内部有限序列图 | 用原构造器编码状态，定义独立合法逐步历史、内部逐索引输入消费；不得用最终运行结果倒定义历史 | 下一单元 |
| R3b | 原序列追加、真实严格tail下降及Foundation／Separation | 全内部完整运行存在唯一；中间value／scale／acc及余输入不变量；不假设外部标准ω或外部良基 | 待完成 |
| R4 | EOF实际逆序、规范分段及原返回类型 | 构造并证明acc.reverse及准确成功／拒绝，证明原初始化下的规范varint和值／scale不变量、完整消费 | 待完成 |
| R5 | reader、已验收Bytes／Canonical／Tok及原Basic AST | 原程序／规格的全内部双条件、完整字节包与AST桥，含全部无效码 | 待完成 |
| P／I／C | 原六规则／27模式、全部ZF／U公理及完整模式 | 内部Proof／检查与编译正确性、完整数学解释、原nativeZF内部Con蕴含 | 待完成 |


下一单元首先编码完整状态四元组并定义独立逐步历史，接入原内部序列图及全部内部索引，再建立消费与结束条件。不能从本批单步／四类观察跳过实际EOF逆序、完整运行、规范分段和原Basic AST。
