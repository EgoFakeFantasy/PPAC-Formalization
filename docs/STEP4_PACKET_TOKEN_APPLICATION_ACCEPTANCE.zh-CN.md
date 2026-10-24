# 原token两规则、完整赋值应用及关系式展开验收（2026-10-25）

原tokenSmall／tokenLarge的完整规则应用已验收：真实128移位、全部guard及三个有序大分支前提对象归一；全部六赋值的自然性由真实行推出，辅助digit／quotient／递归输出的搜索界由规范接受集合中的实际仿射算术推出。原arity3／6应用双向等价、十规则标签分派和ALL4关系式Condition展开完成；仅Ω取得128／256及规范V的实际EX3系统。15模块147声明、15组原nativeZF闭句；2225构建、24003审计（463无公理／23540允许依赖）、零警告；九命令／五trust=0通过，2005哈希、2682对精确足迹、21659项Internal覆盖。指定根字段归一、完整token存在唯一、varint／字节包、原Basic AST桥、schema、Proof／解释及最终Con仍未完成。

## 对象合同与最终目标

对象语言是原纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection，正式返回原YesMetaZFC.Logic.FirstOrder.Derives。没有新增推导核、对象Choice、强不可达或自定义axiom。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

全部内部ω、原六规则／27模式及完整公理模式的规格不变。完整内部Proof、数学解释及最终Con尚未证明。本批落实原Packet中tag2的实际token规则应用，为下一步沿商归纳提供真实递归方程。

## 原规则及准确对象矩阵

PacketTokenRuleData直接使用未修改的ObjectPacket.tokenSmall与tokenLarge。前者arity=3，guard为n<128，唯一前提是tag1仿射行；后者arity=6，head仍只有n、tail、output三个字段，两个guard为0<q与d<128，三个有序前提依次为tag0分解、tag2递归token、tag1带128移位的字节仿射。

纯关系式归一的实际矩阵如下，其中Entry_k是实际tag-k三字段根行存在且属于同一个内部集合V：

```text
Small(w,B,V,n,t,a,r) = Row_2(w,n,t,a,r) ∧ n∈B ∧ Entry_1(w,V,n,t,a)

Large(w,B,V,r;n,t,a,d,q,u) = ∃z,y
  (Empty(z) ∧ Sum(w,d,B,y) ∧ Row_2(w,n,t,a,r) ∧
   (z∈q ∧ d∈B) ∧
   (Entry_0(w,V,d,q,n) ∧ Entry_2(w,V,q,t,u) ∧ Entry_1(w,V,y,u,a)))
```

B为真实内部Num128对象。实际addConst128表达式图经HornExprAddConst转为Sum；两条guard和全部三个前提保留原顺序。零元z与移位digit y在对象EX2内取得并消去。矩阵级显式environmentNat前提只描述其局部赋值；完整应用反向中的全部自然性随后从真实行证据推导，不保留额外自然性oracle。

SmallOutcome是真实EX3(n,t,a)；LargeOutcome是真实EX6(n,t,a,d,q,u)再套上述EX2。没有删除原六赋值中的辅助变量，也没有把搜索块换成宿主有限数据。

## 三个辅助赋值的原搜索界

原tokenLarge的d、q、u没有出现在头行中，不能用“头表达式含全部变量”的仿射规则证明。PacketTokenApplicationBounds实际利用规范根集合Value(w,V)中已有的全内部仿射正确性：

```text
Entry_0(w,V,d,q,n) → A_128(w,d,q,n)
Entry_1(w,V,y,u,a) → A_256(w,y,u,a)
```

前批原ω归纳已经消去这些仿射事实的全部IH；本批不再把其正确性当成假设oracle。由真实和式得到d≤n，由已证商界得到q≤n及u≤a。原构造器child-member严格界给出n、t、a各不超过头行码r，原内部顺序传递性合成全部六赋值≤r。

全部六值的自然性亦来自实际头行和前提行的三个字段。反向HornApplicationRules.intro_application实际取得environmentNat与environmentBound，不把有限搜索界删掉或外加为定理前提。

因此原nativeZF证明：在Ω、真实Num128／Num256及规范V下，原arity=6有界application与完整LargeOutcome双向等价；arity=3的小分支双向等价不需要规范V前提。大分支的规范V范围是明确合同，不声称任意未验证V都有相同算术界。

## 原十规则分派与全根系统

原表另外八条规则的外层标签全部与2不相同。PacketTokenDispatch逐条处理实际十规则，用原对象构造器标签不交性排除八个分支，精确保留small／large两个application，再接完整原arity块等价。

实际原核结论包括：

```text
close(Ω(w) → Num128(B) → Num256(C) → Value(w,V) → Row_2(w,n,t,a,r) →
  (Condition_Packet(w,r) ↔ (SmallOutcome(w,B,V,r) ∨ LargeOutcome(w,B,V,r))))

close(Ω(w) → Num128(B) → Num256(C) → Value(w,V) → ∀n,t,a,r
  (Row_2(w,n,t,a,r) →
    (Condition_Packet(w,r) ↔ (SmallOutcome(w,B,V,r) ∨ LargeOutcome(w,B,V,r)))))

close(Ω(w) → ∃B,C,V
  (Frame128(w,B) ∧ Frame256(w,C) ∧ Value(w,V) ∧ AllRootEquation(w,B,C,V)))
```

最后一个系统只需Ω：B、C、V均由原对象定理在EX3中取得并消去，不能误读成宿主预选的字面量或接受集合。ALL4保留全部内部n、t、a、r候选，非法值由实际Row守卫拒绝。

本批方程完整保留EX3／EX6及内层EX2，而未把其前三个存在字段显式替换成给定根的n、t、a。指定根字段的逐项对象注入性归一是下一步，尚不把上述展开记为已经完成最简数值token递归方程或实际输出存在唯一性。

## 实际验收及清理

- 原native定向构建2030任务成功；全仓2225任务成功；九条验收命令、五个--trust=0入口全部退出0，零警告。
- 新增15模块147个显式声明先独立预审计，再全量覆盖；累计24003声明审计：463无公理、23540仅含记录的允许依赖。
- 新增15组core／native足迹先预审计再允许：core恰为propext／Classical.choice／Quot.sound，native恰继承原七项固定闭句证书；没有扩大原choice桥的额外专用证书范围，没有添加新的对象公理、宿主eval或预算／linter豁免。
- 2005份文件SHA256独立回读一致，累计2682对精确core／native足迹一致，21659项Internal显式声明完整覆盖。此前全部布尔完成门逐项保持原值，七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净，此前跟踪的PPAC证明及AST未改。
- 定向编译及预审计成功后、全仓编译前检查Lean／Lake进程0、停止0；按明确路径白名单删除4份被成功构建替代的失败日志和1个已并入正式Audit.lean的临时审计驱动，共20217字节。该检查窗口可用空间净增32768字节，清理后C盘97918914560字节可用；路径、大小与SHA256保留在清理回执，有效源码、工具链、缓存及复现脚本保留。

新增六项true门限于原token规则矩阵、六赋值搜索界、规范V下有界应用等价、原十规则标签分派、关系式Condition递归展开及实际双radix系统存在。新增的完整token算术与实际执行存在唯一门均明确false；全部此前布尔门逐项保持原值。

原Basic AST条件到纯关系式Condition的正式对应仍未完成；object_Packet_original_Basic_AST_condition_translation_proved及object_Packet_actual_Horn_affine_condition_correspondence_proved保持false。全内部token运行存在唯一、规范LEB128的完整字节程序、tree／forest／packet、版本／marker／完整消费与无效包拒绝、Project primitive subset降语言、全部内部schema测试、Proof／解释及最终Con均未完成。

验收前基点544cd890bb64d84d1827e931f82bcf70fc7206bd。本批15模块、4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,packet-token-readback.json}、.local/packet-token-preaudit.json及.local/workspace-cleanup-packet-token-result.json；复验C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交，未推送远端。

## 修订后的agent工程流程表

| 顺序 | 实现与依赖 | 原核对象验收产出 | 状态 |
|---|---|---|---|
| T1.2c.2 | 十二构造实际Compiler、Foundation／Separation | 全内部准确源接受与类型唯一纤维 | 前批已验收 |
| T1.2c.3a／b／c | 原仿射算术、实际根字段、十规则关系式轨迹及ω归纳 | 全内部独立AffineAccepted↔A | 前批已验收 |
| T1.2c.3d | 对输出的原ω归纳、商区间与抵消、Foundation／Separation | 逆分解存在唯一、商下降、准确停止条件与商递归归纳模式 | 前批已验收 |
| T1.2c.3e.1a | 原tokenSmall／Large的真实矩阵、完整arity3／6块与辅助界 | 全根实际Condition展开及仅Ω的双radix规范系统 | 本批已验收 |
| T1.2c.3e.1b | 真实EX3／EX6及EX2、三字段对象注入与等号传输 | 指定n／tail／output的准确small／large数值递归方程 | 下一单元 |
| T1.2c.3e.1c | 本批实际递归前提、原商下降归纳、真实128移位字节界 | 全内部合法token输入的实际输出存在唯一与准确类型 | 待完成 |
| T1.2c.3e.1d | 原varint／bytes内部程序、规范字节序列及实际token | 规范LEB128／前缀消费正确性与无效候选拒绝 | 待完成 |
| T1.2c.3c.1b／4 | 原Basic函数图、ω／powerset／有界量词及模板实例 | 原Basic条件AST到纯关系式Condition的形式对应 | 待完成 |
| T1.2c.3e.2 | 原tree／forest／packet、内部结构归纳及实际token | 完整字节包、版本／marker、完整消费及拒绝 | 待完成 |
| T1.2c.3f | 原ProjectEncode／Quotation与primitive subset降语言 | 原数值字节包到实际纯成员Compiler的准确桥接 | 待完成 |
| T1.2d | 完整Separation／Collection模式与目标3句 | 全内部码的准确原理论公理测试 | 待完成 |
| T2／T3 | 原六规则／27模式、内部Proof及原PPAC解释 | checker准确性、原核传输与内部Proof变换 | 待完成 |
| T4 | 全内部无矛盾式与最终原核审计 | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

每批先独立trust=0与精确足迹预审计，再全仓串行构建及类型检查；随后回读原门、哈希、理论锁与提交字节。只清理本工程明确失效的产物，保留有效源码、工具链、缓存及有用复现脚本。
