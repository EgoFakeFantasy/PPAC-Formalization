# 原Packet仿射算术对象推导验收（2026-10-25）

原Packet的128／256仿射算术单元已验收：全部内部digit／tail／output候选的零点、后继及递归方程，合法输入的输出存在唯一，以及仅Ω前提下实际128／256基数系统的对象存在性。11模块139声明、14组原nativeZF闭句；2152构建、23105审计（458无公理／22647允许依赖）、零警告；九命令／五trust=0通过，1932哈希、2563对精确足迹、20761项Internal覆盖。原四条affine规则的有限元数据已精确核对，但原Horn条件与算术的等价、完整NatPacket字节包、schema、Proof／解释及最终内部Con仍未完成。

## 背景、表示及完整目标

对象语言为纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection；正式返回原YesMetaZFC.Logic.FirstOrder.Derives。完整目标保持：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

Proof_T必须覆盖全部内部ω、六规则／27逻辑模式及完整理论公理模式。本批只完成下面的实际对象算术单元，没有完成完整Proof_T或内部Con。

必须分别处理三种表示：既有StructuralNode／List的Gödel配数结构树码、NatPacket的版本一LEB128／256进制字节包，以及Project编译后的纯成员公式树。它们目前没有完整统一桥接，不能凭宿主编码往返或有限规则元数据相等直接识别。

另有语言差异：原ObjectProjectQuotation.run把subset保留为BasicSetTheory的原始关系，而最终纯成员语言的Project编译器把subset展开为带绑定移位的全称成员式。后续须明确证明降语言过程，不能将原run直接等同于既有纯成员编译器。

## 本批实际对象结论

定义A(w,B,d,t,n)为B∈w、d∈B、t∈w、n∈w及对象存在p满足Product(w,B,t,p)和Sum(w,d,p,n)的合取。所有自然数及乘／加见证都是内部对象；显式守卫避免零乘积对非自然B的潜在接受。

14组闭句均经TheoryTransport.sentence及ZFReplay.replay返回原nativeZF，CheckStep4逐项核对返回类型。主要结论为：

~~~text
close(Ω(w) → B∈w → d∈B → t∈w →
  ∃n ((n∈w ∧ A(w,B,d,t,n)) ∧ ∀a(A(w,B,d,t,a) → a=n)))

close(Ω(w) → A(w,B,d,t,n) → A(w,B,d,t,a) → n=a)

close(Ω(w) → B∈w → ∀d,t,n
  (A(w,B,d,t,n) ↔
    ((Empty(t) ∧ d∈B ∧ n=d) ∨
      ∃s,a (Succ(t,s) ∧ A(w,B,d,s,a) ∧ Sum(w,a,B,n)))))

close(Ω(w) → ∃B (Frame_radix(w,B) ∧
  AllInternalFibers(w,B) ∧ AllInternalRecursiveEquation(w,B)))
Frame_radix(w,B) = B∈w ∧ Num_radix(B)
radix = 128 or 256
~~~

最后一个式子表示代码system的合取结构，具体AST以PacketAffineLiteralSyntax为准。Bool只选择两套固定有限证明模板，绝不把内部数域限制为外部标准自然数。全部digit／tail／output候选保留；无效digit、tail、output另有显式拒绝闭句。基数见证通过SyntaxNumerals.exists_numeral在对象EX中取得并消去，最终无需外加基数证书前提。

零点证明从实际乘积评价零和加法评价零得到n=d；正向后继从旧乘积加B构造新乘积，再以加法结合返回新输出；反向后继在对象EX中取得前乘积及前输出，使用乘法后继方程与加法反结合。最终内部ω分解为零或前驱，消去后继方程的辅助见证。没有对内部数据使用外部Nat归纳。

## 原规则对应的精确范围

PacketAffineRuleData直接导入锁定上游ObjectPacketGraph，证明关系0／1的实际rulesFor分别恰为affineBase和affineStep，核对arity、head、guards及premises。实际step的输出字段确为ObjectPacket.Expr.addConst radix (.var 2)。这是原有限程序元数据的等式；本批尚未证明该表达式graph与Sum相等，也未证明原闭包／轨迹condition与A相等。

因此以下三项完成门为true：128／256仿射算术存在唯一、全部内部递归方程、实际基数字面量系统存在。原Horn-affine对应、完整NatPacket字节树桥及完整varint内部程序门保持false。所有既有接受门保持原值；完整schema、Proof与Con门继续false。

已有HornExprSyntax.graph直接解释原固定ObjectHorn.Expr，并已有对象存在唯一及结构构造器引理。下一单元应复用这一接口证明原Expr.addConst与Sum的对象等价，避免另造无关表达式解释器。

## 实际验收与清理

- 定向native构建1957任务成功；全仓2152任务成功。九命令及五个--trust=0入口均退出0，零警告。
- 审计23105项声明：458项无公理、22647项仅含记录的依赖；新增139项声明全部覆盖。
- 新增14组core精确依赖propext、Classical.choice、Quot.sound，native精确再继承锁定原七项证书；先独立预审计，再加入允许名单。没有新增对象Choice或自定义axiom。
- 1932份文件SHA256独立回读一致，累计2563对core／native精确足迹一致，20761项Internal显式声明覆盖。
- 七份理论／规则／工具链锁不变，依赖YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净；此前跟踪的PPAC证明及AST不变。
- 本批仅删除3份已被成功构建及预审计替代的失败日志，逻辑8933字节、实测释放16384字节；遗留编译进程0、停止0。有用生成／回读脚本、有效源码及缓存保留。编译前C盘约91.4GiB可用。

验收前基点9f7883c1fa886a21db0f2e3b5fb4286342ce30c7。本批11模块、4个接入文件及6份文档；证据verification/{summary.json,commands.json,build.log,audit.log,packet-affine-readback.json}、.local/packet-affine-preaudit.json及.local/workspace-cleanup-packet-affine-result.json。复验：C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交，未推送远端。

## agent工程流程表

| 顺序 | 依赖与具体实现 | 必须返回的对象接口／验收 | 状态 |
|---|---|---|---|
| T1.2c.2 | 既有十二构造源语法、真实Compiled、Foundation及Separation | 原核全内部准确源接受及类型唯一纤维 | 已验收，保留 |
| T1.2c.3a | 真实128／256规则元数据；Product／Sum及内部ω分解 | 原核仿射存在唯一、零／后继／全部候选递归方程、实际基数系统EX | 本批已验收 |
| T1.2c.3b | 复用HornExprSyntax.graph；对原Expr.addConst固定有限语法建立Sum等价；对齐原Node／参数及guard | 原规则局部矩阵与A的准确对应，所有内部赋值，不预设condition正确 | 待完成 |
| T1.2c.3c | 原Horn轨迹／最小闭包规则；仿射递归方程；对象ω归纳 | 原condition在全部内部候选上恰为A，消去轨迹前提 | 待完成 |
| T1.2c.3d | 对内部输出做对象ω归纳，建立Euclidean digit／quotient、界及唯一性 | 128／256逆分解存在唯一，含0、marker、非法字节处理 | 待完成 |
| T1.2c.3e | 原tokenSmall／Large及tree／forest／packet十规则，内部列表／树归纳 | 原NatPacket版本、规范LEB128、终止marker、完整消费及无效码拒绝；全部内部码双向等价 | 待完成 |
| T1.2c.3f | 原ProjectEncode／ObjectProjectQuotation；显式处理原primitive subset→纯成员展开 | 原数值源包与既有纯成员Compiler准确桥接；核对语言／universe及绑定移位 | 待完成 |
| T1.2d | 依上述数值桥及既有schema结构程序，完整Separation／Collection及目标3句 | 实际原理论数值公理测试在全部内部码上准确 | 待完成 |
| T2 | 全六规则／27模式及内部证明码 | 完整Proof_T、原checker准确性及源推导→原核传输 | 待完成 |
| T3 | 实际集合论解释与证明转换编码 | 原核内部证明转换，保持目标PP／ACwo／¬AC及背景 | 待完成 |
| T4 | 对全部内部p的Proof转换与无矛盾式 | Derives nativeZF [] (Con_ZF→Con_target)及最终原核审计 | 待完成 |

每批先锁定实际关系和原规则，独立trust=0／公理预审计，再接入全仓验收；只在准确对象闭句成立时翻转对应完成门。外部模式索引可保留，不能以宿主求值、有限quotation、语义模型或构建成功替代全部内部对象推导。
