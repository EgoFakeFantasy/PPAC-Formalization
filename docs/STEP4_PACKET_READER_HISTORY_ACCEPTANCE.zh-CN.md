# reader实际状态码、带码单步与独立历史零步基例对象验收（2026-10-25）

reader实际状态编码、带码单步及独立历史零步基例已验收：原四字段列表码存在恰好等价于原State，码自然且唯一，同一码的四字段联合唯一。完整八字段带码转移在任意实际源状态码上准确归一，输出唯一，后继域等价于原Admissible。独立内部序列历史逐内部索引检查真实带码步，真实单点序列构造零步历史，任意已接受零步历史首尾相等。11模块136声明、15组原nativeZF闭句；2434构建、26411审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。任意长度历史追加／确定性、输入消费／完整运行、EOF实际逆序、原reader程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 原背景理论与最终目标

对象语言保持原纯EqMem，背景是完整ZF（含完整Separation／Collection），证书返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。原19条Source规则经既有TheoryTransport.sentence及ZFReplay.replay传输；未引入新推导核、对象Choice、不可达、外部标准ω或外部良基前提。固定YesMetaZFC仍为 `039c8e132cc19671d73a3933c66b4799d2599dd6`。

最终目标始终为：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

内部Proof须覆盖全部内部ω（含非标准和无效码）、原六规则／27模式及完整ZF／目标公理模式。完整内部Proof／检查／编译、数学解释及最终Con主句均未证明。

## 实际状态码与带码步骤

不另造编码约定，状态四元组沿用原 `SyntaxForestSyntax.forest 4` 的精确四字段内部列表码，按余输入、value、scale、acc顺序：

```text
StateCode(w,l,v,s,a,n) = State(w,l,v,s,a) ∧ Forest4(w,[l,v,s,a],n)
StateCarrier(w,n) = ∃l,v,s,a StateCode(w,l,v,s,a,n)
CodedStep(w,B,z,o,n,r) = ∃l,v,s,a,x,y,q,c
  (StateCode(w,l,v,s,a,n) ∧ StateCode(w,x,y,q,c,r) ∧ Advance(w,B,z,o,l,v,s,a,x,y,q,c))
NextAt(w,B,z,o,l,v,s,a,r) = ∃x,y,q,c
  (StateCode(w,x,y,q,c,r) ∧ Advance(w,B,z,o,l,v,s,a,x,y,q,c))
```

实际原核推导：

- 仅Ω即可证明自然码存在↔原State；码自然、输出唯一、同一码的四字段联合唯一。原列表码构造、唯一性及字段注入性均实际调用，编码不是任意关系名或宿主元组。
- 任意实际源StateCode下，CodedStep↔NextAt覆盖全部内部候选目标码；八字段存在块真实消去，四项源字段经原列表注入性与对象等号对齐。
- 任意CodedStep都给出真实源／目标StateCarrier及自然范围；仅Ω、自然B及两份实际接受即给目标码唯一，不再要求外部给定源字段。
- 任意实际源码下，存在自然带码后继↔原Admissible。反向先取得真实完整原状态后继，再构造其实际码；正向归一回原Advance并推出原定义域。原Num128／Num0／Num1也给出准确对象特化。

原State、完整Advance、局部Step、128／0／1、Bytes、Canonical、Prefix、Tok和Packet十规则均未修改。原raw reader允许byte≥256和scale=0；本批保持此范围，未把后续字节／正性不变量暗加到定义域。

## 独立内部历史及真实零步构造

历史直接使用原内部序列图，不以最终输出、运行结果或宿主列表倒定义：

```text
RowAt(w,B,z,o,f,i,j,n,r) = Succ(j,i) ∧ Edge(f,i,n) ∧ Edge(f,j,r) ∧ CodedStep(w,B,z,o,n,r)
Links(w,B,z,o,l,f) = ∀i∈l ∃j,n,r RowAt(w,B,z,o,f,i,j,n,r)
History(w,B,z,o,n,r,l,d,f) = StateCarrier(w,n) ∧ Empty(z) ∧ l∈w ∧ Succ(d,l)
  ∧ Sequence(f,d,w) ∧ Edge(f,z,n) ∧ Edge(f,l,r) ∧ Links(w,B,z,o,l,f)
```

l、d、f、i、j和状态码都是内部对象。固定4／8仅为公式字段数元数据，不是运行时长度上界。History表示合法执行前缀，尚不要求EOF或结束，因此不能把历史存在当作完整reader成功。

本批证明任意内部i∈l都有真实相邻带码步，历史首尾均自然；实际零步历史由原空序列加一次真实SequenceAppend构造单点集合图，同时得到原functionOn、准确域、零seed／末边和全部空索引行。任意已接受零长度历史由空集唯一性及原图单值性推出首尾码相等。任意实际StateCode都能作为此真实零步历史的起点。

尚未证明任意长度历史的追加构造和逐索引确定性、输入消费／完整运行存在唯一、EOF实际acc.reverse、原初始化和规范分段不变量。这些是后续明确缺口；本批未将AST存在、零步基例或编译通过当作完整程序证明。

## 模块与验收

新增模块：PacketReaderStateSyntax, PacketReaderStateCode, PacketReaderCodedSyntax, PacketReaderCodedTransport, PacketReaderCodedNormalize, PacketReaderCodedUnique, PacketReaderCodedExistence, PacketReaderHistorySyntax, PacketReaderHistoryLaws, PacketReaderHistoryBase, ObjectPacketReaderHistory。共136个显式def／theorem，15组Source闭句／原sourceZF核证书／原nativeZF证书。全部接入PPAC导入、Audit全声明审计、CheckStep4明确原核fixture及scripts/verify.py独立守卫。

- 定向构建2175 jobs，零警告；136项新增声明trust=0预审计与清单精确对应。
- scripts/verify.py：2434构建任务、26411项审计（482无公理／25929允许依赖），零警告。
- 九条命令及五个trust=0入口全部退出0；2214份独立哈希一致，2968对精确核／原生足迹，24067项Internal显式声明覆盖。
- 15组新增原核证书足迹准确为propext／Classical.choice／Quot.sound，native证书准确加底座已有七项FreeClosed证书；没有新axiom、native_decide或允许范围扩大，不宣称底座七项证书已消除。
- 全部旧布尔叶递归比较不变，新增状态码／带码步／历史零步门true，完整历史／运行、EOF逆序、程序桥、Basic AST、Proof／解释／Con保持false。
- 全部旧跟踪PPAC证明与AST、七个可信基／配置／规则锁及YesMetaZFC固定提交保持，其工作树干净。本批精确21文件仅做本地提交。

证据：`verification/packet-reader-history-readback.json`、`verification/summary.json`、commands／build／audit日志及 `.local/packet-reader-history-preaudit.json`；提交号由readback的accepted_commit回读。

## 编译前清理

核对0个遗留Lean／Lake编译进程，停止0个。对绝对路径、工作区内界、普通文件且非reparse逐项核查后，删除本轮3个失败日志／已整合临时文件，共19637逻辑字节。该窗口实测空闲变化28672字节，仅报告观测值。删除前SHA256及清单见 `.local/packet-reader-history-precompile-cleanup.json`。保留源文件、依赖、工具链、必要缓存与验收证据；清理时可用约90.37 GiB，随后单线程串行完成全仓验收。

## 后续工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界局部状态、完整输入Cons、准确单步／四类观察 | 全部内部候选的类型、定义域、联合确定性及原128／0／1特化 | 已验收 |
| R3a.1 | 原四字段列表编码、带码转移及独立逐索引历史 | 状态编码准确域／唯一／字段注入，带码步准确归一／唯一／准确域；真实单点零步历史及精确零长度端点 | 本批已验收 |
| R3a.2 | 原序列追加及全部旧边保留、新末行 | 实际构造延长历史，证明全部旧行保留和新行；全部内部长度上的同起点历史逐索引／端点确定性 | 下一单元 |
| R3b | 真实Cons输入消费、严格tail下降及Foundation／Separation | 全内部完整运行存在唯一、完整输入消费；保留value／scale／acc不变量，无外部标准ω或良基假设 | 待完成 |
| R4 | EOF实际逆序及原初始化／规范分段 | 真实acc.reverse及准确返回／拒绝；规范varint、value／scale与累积顺序对应 | 待完成 |
| R5 | reader、Bytes／Canonical／Tok及原Basic AST | 全内部程序／规格双条件、完整字节包及AST桥，含全部无效码 | 待完成 |
| P／I／C | 原六规则／27模式及完整ZF／U公理 | 内部Proof／检查／编译正确性、完整数学解释、原nativeZF内部Con蕴含 | 待完成 |


下一单元用原序列追加真实构造延长历史，逐一保留全部旧行并加入新末行，证明同起点同长度历史逐索引及端点确定性；再接入真实输入消费与终止证明。不得跳过完整运行或实际EOF逆序而将本批历史基例记为程序桥。
