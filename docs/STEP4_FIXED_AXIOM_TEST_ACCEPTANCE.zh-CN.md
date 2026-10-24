# 固定公理部分测试及包算术验收（2026-10-24）

本批完成七条固定原生ZF公理及目标三句的**部分对象测试**：实际包算术、准确行字段、固定公式报价及隐藏ω见证已经连接，11组闭句已传入原FirstOrder.Derives nativeZF。完整Separation／Collection内部测试、实际Bool／Proof_T和最终Con仍未证明。

## 背景、内部Con与验收层次

对象语言为纯等号／成员ℒ，背景为Contract.nativeZF，即原SetTheory.ZF的Project.fo_theory像，含完整Separation／Collection。目标理论保持ZF+PP+ACwo+¬AC。正式推导使用原FirstOrder.Derives，最终仍要求：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

这里的p遍历全部内部ω，原六规则／27逻辑模式及完整理论公理模式必须保留。上述Con是最终工程规格；完整实际Proof_T／Con主句尚未建成并证明。本批的类型数据、有限模式及成功编译均不替代它。

## 实际实现与对象接口

| 模块 | 已完成范围 |
|---|---|
| NativeAxiomCertificateData | 精确无Choice证书类型，七固定公理、任意UnarySchema分离及BinarySchema收集；nativeZF／targetTheory宿主数据的sound／complete与编码往返；目标三句独立标签 |
| FixedAxiomPacketSyntax／Arithmetic／Facts | 小标签字节包的对象多项式规格，重命名／输入等词传输，自然范围、输出唯一及标签单射 |
| FixedAxiomPacketExistence／Unique | 六个算术槽及结果均对象EX构造／消去；不同标签互斥、范围与准确值纤维 |
| FixedAxiomTableSyntax／Facts | 两张实际有限Formula1测试；七固定原生ZF分支和目标额外三分支；同码字段对齐、隐藏ω唯一性、准确报价双条件及Choice标签拒绝 |
| FixedAxiomTableExistence | 实际包、公式报价、二字段行码均在对象EX内取得并消去；只有Ω前提的接受行存在 |
| ObjectFixedAxiomTest | 11组source／sourceZF原核／nativeZF闭句；CheckStep4逐组检查并展开主接口 |

NativeAxiomCertificateData完整模式的sound／complete及数据往返是**宿主中间结果**。对象测试当前只包含固定7／10分支，不能把完整证书数据类型误报成已覆盖内部任意模式码。

固定标签为0…6、10、11、12，依次对应原七固定ZF公理及PP、ACwo、¬AC。标签7为上游Choice，基础和目标两张部分测试均拒绝它；本工程没有采用上游含Choice的完整ZFC呈现。

两种数值编码保持区分：上游NatPacket使用ULEB128字节包；PureQuotationSyntax.formula采用现有结构树配对码。对tag<128，真实NatPacket叶包满足：

~~~text
encode(leaf(tag)) = (256*(256*256) + 256*tag) + 1
~~~

本批对象Leaf关系用Num256／Numtag、三个乘积、一次和及后继计算该表达式，避免展开Num16777217。包存在／唯一算术模式可对任意外部Nat索引写出；它与单字节原包的数值等式只在tag<128使用。所有固定标签均有该界证明。没有宣称完成任意内部长度的ULEB128解析器或完整原ProofT字节包检查器。

主要对象结论如下；PartialTest和Quote都是实际有限对象公式，Row是实际原数值构造器：

~~~text
nativeZF ⊢ close(Ω(w) → ∃c (c∈w ∧ Leaf(tag,w,c)))
nativeZF ⊢ close(Ω(w) → Row₂,₀(w,[c,f],row) → Leaf(tag(k),w,c)
                       → (PartialTest(target,row) ↔ Quote(fixedFormula(k),w,f)))
nativeZF ⊢ close(Ω(w) → Row₂,₀(w,[c,f],row) → Leaf(7,w,c)
                       → ¬PartialTest(target,row))
nativeZF ⊢ close(Ω(w) → ∃row (row∈w ∧ PartialTest(target,row)))
~~~

第二式的k属于所选固定分支表；最后一式选定表内任意一个固定分支，包／公式／行的见证全部对象消去。该存在式只说明部分测试接受实际构造的固定行，不等于完整理论测试或Proof_T正确性。

## 实际验收

| 项目 | 实测结果 |
|---|---|
| 新模块／显式声明／原核闭句组 | 10／140／11 |
| 定向构建 | 1779项，退出0、零警告 |
| 清理后全仓构建 | 1984项，退出0 |
| 声明审计 | 21557项：426无公理、21131允许依赖；零警告 |
| 验收命令 | 9条全部退出0，含5个trust=0入口 |
| 独立SHA256 | 1767份一致 |
| 全部精确core／native对 | 2420对，含本批11对 |
| Internal显式声明覆盖 | 19213项 |
| 上游及锁 | YesMetaZFC 039c8e132cc19671d73a3933c66b4799d2599dd6干净；7锁不变 |

信任足迹逐声明锁定140项，没有扩大旧声明的许可集。五组包算术core恰含propext／Classical.choice／Quot.sound，native另含原七项证书。六组固定测试因直接引用原生固定句子的FreeClosed证书，其core和native均继承同样七项。不能将这些core误报为仅三项标准依赖。没有新增Choice证书或新自定义公理；既有7证书基线见TRUST_BASELINE.json。

所有此前跟踪的PPAC证明及接受AST保持原Git字节。本批只增加10模块并修改4个接入文件及6个文档。验收前HEAD为68ad223b132ec41b1c4aba92c918bef8baba175c；提交后accepted_commit及逐文件字节回读保存于本地verification/fixed-axiom-readback.json。复验命令为C:/Python314/python.exe -X utf8 scripts/verify.py。

本地证据包括verification/{summary.json,commands.json,build.log,audit.log,fixed-axiom-readback.json}及.local/fixed-axiom-native-directed-2.log。未推送远端。

## 工作区清理及恢复编译

在全仓验收前按显式白名单删除16份过时诊断文件／空日志，删除前记录SHA256、删除后逐一确认不存在。逻辑删除13347字节，盘面实测增加20480字节；清理后可用101572562944字节。当前空间恢复主要来自用户释放磁盘，本批清理不冒领该增量。

清理时残留本项目编译进程为0，停止失效进程0；此前为定位性能问题主动中止的编译另列收据。有效证明、构建缓存和有用生成／回读脚本均保留。清理后已实际完成上述全仓构建、审计及trust=0检查。收据.local/workspace-cleanup-fixed-axiom-result.json。

性能修复：空列表长度须显式化简；先证明符号base的fold等式再实例化256，避免内核在一个定义相等检查中展开大型数值表达式。深层AST的congruence改用显式congrArg。失败／中止构建不计入验收结果。

## 修订后的agent工程流程

| 单元 | 输入与具体实现 | 对象层验收出口 | 当前状态 |
|---|---|---|---|
| T1.0 | 锁定nativeZF／target及精确无Choice证书类型、完整schema数据和往返 | 先明确编码／语言／理论；宿主数据仅作编译器接口 | 数据部分完成；内部schema测试未完成 |
| T1.1，本批 | 固定7+3标签、字节包多项式、原二字段行、实际纯公式报价；所有见证对象取得／消去 | 上述准确双条件、标签7拒绝、只有Ω的接受行存在，全部原核Derives | 已验收 |
| T1.2，下一步 | 对全部内部参数数目及schema体构造原分离／收集实例；处理扩展Project语法的subset／外延相等、纯语言翻译、闭性和binder顺序 | 真实Formula1完整理论测试；全部内部ω码的合法性／拒绝双向证明，不以标准Nat枚举代替 | false |
| T1.3 | 把源Replacement与原Collection既有对象互导编译为实际数值公理证书转换；证明语言／参数／码对应 | 原理论公理码及推导码转换的内部正确性 | false |
| P1 | 接完整公理测试到已证六规则／27模式局部表；构造实际共享Bool／Proof_ZF／Proof_target AST及方程 | 全部内部码上的实际方程，实例化已证对象Foundation唯一性；无假定检查器正确性 | false |
| I1 | 将论文所需解释、ZF各公理模式、强迫／对称名、PP全秩和ACwo／非AC见证转成内部证明转换 | 普通ZF背景中的解释及逐公理原核推导；核对universe／模型范围，不混入强不可达前提 | false |
| C1 | 用内部转换处理任意内部反证码，构造最终Con句并装配 | FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | false |

每个单元保持相同验收顺序：核对接口和所有量词 → 小批对象推导 → 原核包装 → 全声明精确足迹 → 串行全仓／trust=0 → 独立哈希与旧证明不变回读 → 文档与本地提交。具体完整测试、Proof／解释与最终Con未完成前，对应门禁始终false；不恢复退役反射实现。
