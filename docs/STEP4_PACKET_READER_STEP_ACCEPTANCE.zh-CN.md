# 原readTokens给定head／rest局部转移对象验收（2026-10-25）

原readTokens给定head／rest的对象层局部转移已验收：原终止／非规范零拒绝／延续守卫覆盖并互斥；未限制byte<256或scale>0。内部差分B+d=byte、无界value+digit*scale、真实Cons前插acc均取得存在、范围与唯一性；四项后继联合唯一，合法后继存在当且仅当未触发原拒绝守卫。128／0／1按原对象数字特化。8模块122声明、15组原nativeZF闭句；2415构建、26154审计、零警告，九命令／五trust=0通过；全部旧布尔叶保持。当前完整输入Cons绑定、整段内部执行、EOF实际逆序、readTokens↔Bytes／Canonical程序桥、Basic AST、Proof／解释及最终Con仍未完成。

## 理论、目标和交付层次

对象语言是原纯EqMem，背景为完整ZF（含完整Separation／Collection模式），正式接口为原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`。本批通过原19规则的Source.Derives、TheoryTransport.sentence和ZFReplay.replay回到原核，没有新增推导核、对象Choice、不可达假设或标准ω前提。

最终目标保持：

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

Proof_T仍须覆盖全部内部ω（含非标准和无效码）、原六规则／27模式及完整ZF／目标公理。专用内部Proof、全内部检查／编译、数学解释及最终Con主句均未证明。

## 独立状态公式和局部合同

原程序取自锁定YesMetaZFC提交 `039c8e132cc19671d73a3933c66b4799d2599dd6` 的 `NatPacket.readTokens`。原输入是任意List Nat、value Nat、scale Nat和acc List Nat，因此不能在原始状态中添加byte<256或scale>0。解码所得字节上界、由初始scale=1得到的正性将作为后续不变量另证。

```text
State(w,l,v,s,a) = ValidList(w,l) ∧ v∈w ∧ s∈w ∧ ValidList(w,a)
Finish(B,z,o,b,s) = b∈B ∧ (s=o ∨ b≠z)
Reject(B,z,o,b,s) = b∈B ∧ s≠o ∧ b=z
More(B,b) = B=b ∨ B∈b
EOF(z,o,v,s) = s=o ∧ v=z
Equation(w,d,v,s,n) = ∃p (Product(w,d,s,p) ∧ Sum(w,v,p,n))
Emission(w,b,v,s,a,c) = ∃n (Equation(w,b,v,s,n) ∧ Cons(w,n,a,c))
Continuation(w,B,b,v,s,y,q) =
  ∃d (d∈w ∧ Sum(w,B,d,b) ∧ Equation(w,d,v,s,y) ∧ Product(w,s,B,q))
```

这里Equation只复用原无界乘加矩阵，未使用要求数字界的PacketAffineSyntax.affine。Continuation中的d没有d<128限制，忠实保留原程序对任意byte≥128的自然差分。

给定已解出的head=b和rest=x，本批局部Step的完整后继(r,y,q,c)为：终止分支要求Finish、r=x、y=z、q=o及Emission；延续分支要求More、r=x、c=a及Continuation。它尚未把原当前输入l与Cons(b,x,l)绑定，因此本批是给定head／rest的局部转移，不是完整reader的准确单步或完整运行证明。

本批闭句全部变量都由对象全称量词封闭，EX见证均在对象量词中取得、消去：

- 自然B、b下，Finish／Reject／More覆盖；两种低字节状态互斥，与高字节互斥；Reject禁止任何局部Step。
- 任意自然b、v、s下，Equation实际存在自然输出；自然性与输出唯一性不要求scale非零或byte<256。
- 在More及自然输入下，Continuation实际存在自然y、q；任意两次接受的y、q联合唯一；实际接受推出More和输出自然范围。
- 对有效acc，Emission实际构造Cons并保持列表有效性；任意两次接受输出唯一，未用列表关系别名替代构造。
- 对State(w,x,v,s,a)及自然B／z／o／b，任意已接受局部Step保持后继State，四项后继联合唯一；存在合法四项后继当且仅当¬Reject。
- 真实Num128 B、Num0 z、Num1 o通过原SyntaxNumerals.range直接取得同一原核的准确后继定义域特化。

EOF仅保留原scale=1且value=0的守卫公式并证明逻辑分派；未证明该分支的实际acc.reverse输出。完整源程序与内部关系的统一对应仍待完成。

## 文件与证书

8个新模块为：PacketReaderStepSyntax, PacketReaderGuards, PacketReaderArithmetic, PacketReaderContinuation, PacketReaderEmission, PacketReaderStep, PacketReaderStepExistence, ObjectPacketReaderStep。共122个显式def／theorem，15组闭句各含source、原sourceZF核证书及原nativeZF证书。新模块全部纳入PPAC导入、Audit全声明审计、CheckStep4明确原核fixture及scripts/verify.py的独立局部转移守卫。

原Tok／Canonical／Bytes／Prefix、Packet十规则、全部旧跟踪PPAC证明与AST均未修改。原数字、算术、列表原核与依赖锁保持。

## 实际验收

- 定向原核模块构建：2158 jobs，零警告；新增122项在trust=0预审计中与清单精确对应。
- scripts/verify.py：2415构建任务，26154项声明审计（482无公理／25672允许依赖），零警告。
- 九条命令全部退出0，其中五个trust=0入口；2195份独立工作区哈希一致，2937对精确核／原生公理足迹，23810项Internal显式声明全覆盖。
- 全部15组新核证书公理足迹准确为propext／Classical.choice／Quot.sound；native证书准确加上底座七个已有FreeClosed证书。未新增任何公理或native_decide；不把继承的七项证书说成已经消除。
- 全部旧布尔叶递归比较不变；新局部转移门为true，完整readTokens程序桥、原Basic AST、Proof／解释及最终Con门保持false。
- 七个配置／理论／规则／可信基锁未改，YesMetaZFC依赖提交及其工作树干净。仅对本批明确文件做本地提交，不自动发布。

证据：`verification/packet-reader-step-readback.json`、`verification/summary.json`、commands／build／audit日志；新增声明独立预审计 `.local/packet-reader-step-preaudit.json`。最终本地提交号由验收readback的accepted_commit字段回读。

## 清理与编译顺序

编译前枚举到0个Lean／Lake编译进程，停止0个进程；未把仍在运行的工具服务判为废弃进程。以绝对路径、工作区内界、普通文件且非reparse逐项校验后，删除6个本轮失效脚本／已整合临时文件／失败日志，共33232逻辑字节；该窗口实测空闲变化为45056字节，仅报告观测值，不把并发磁盘变化全归因于清理。保留源代码、依赖、工具链、必要缓存和验收证据。随后单线程串行全仓编译及五个trust=0入口完成。

清理清单含每个删除前SHA256，见 `.local/packet-reader-step-precompile-cleanup.json`。清理时C盘空闲约90.49 GiB。

## 后续工程流程

| 后续单元 | 输入与实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1 | 给定内部head／rest，原value／scale／acc及128／0／1 | 精确局部转移、类型保持、四项确定性、后继存在↔非拒绝 | 本批已验收 |
| R2 | 当前完整输入l及真实Cons(b,x,l) | 头尾在对象量词中取得、绑定并消去；Nil／Cons分派；全部候选的完整状态单步总唯一／拒绝 | 下一单元 |
| R3 | 原完整Fields及内部有限历史 | 全内部索引消费、value／scale／acc不变量、完整运行存在与唯一；不假设外部标准ω或外部良基 | 待完成 |
| R4 | EOF分支、实际逆序、规范varint边界 | 终止规范零守卫与累计值／scale对应，acc逆序及完整消费，准确失败与成功结果 | 待完成 |
| R5 | 原readTokens与已验收Bytes／Canonical／Tok | 全部内部有效及无效候选上的程序／规格双条件；原Basic AST及完整字节包 | 待完成 |
| P／I／C | 原六规则／27模式、全部ZF／U公理及完整模式 | 专用内部Proof与检查／编译正确性、数学解释、原nativeZF内部Con蕴含 | 待完成 |


下一单元先将完整当前输入与原Cons头尾绑定，再证明真实状态单步的全部内部候选确定性和准确Nil／Cons分派。不能从本批局部确定性跳过内部历史消费、EOF实际逆序、规范分段／accumulator不变量或完整原Basic AST对应。
