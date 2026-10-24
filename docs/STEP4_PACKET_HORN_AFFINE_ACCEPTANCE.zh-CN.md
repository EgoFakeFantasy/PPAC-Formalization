# 原Packet仿射表达式及局部矩阵验收（2026-10-25）

原Packet仿射规则的表达式与完整局部矩阵已验收：原Expr.addConst求值图与内部Sum双向对应，base／step头、比较guard和真实递归前提准确传输；零元／后继／加法辅助见证均对象消去，并得到ALL3／ALL5全内部局部定律及仅Ω前提的实际128／256基数系统存在。8模块103声明、13组原nativeZF闭句；2160构建、23208审计（458无公理／22750允许依赖）、零警告；九命令／五trust=0通过，1940哈希、2576对精确足迹、20864项Internal覆盖。原arity有界赋值应用、完整Packet闭轨迹／字节包、schema、Proof／解释及内部Con仍未完成。

## 背景及完整目标

对象语言为纯等号／成员，背景为Contract.nativeZF及完整Separation／Collection，正式返回原YesMetaZFC.Logic.FirstOrder.Derives。完整目标保持：

~~~text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
~~~

这里的Con是最终规格，完整内部Proof_T及最终蕴涵尚未实现并证明；不能以当前算术、结构树接口或编译结果代替。Proof_T须覆盖全部内部ω、六规则／27逻辑模式及完整公理模式。

## 原有限表达式与全部内部值

HornExprAddConst直接使用锁定原ObjectPacket.Expr.addConst及既有HornExprSyntax.graph。对每个固定有限k及Expr e，原核证明：

~~~text
close(Ω(w) → EnvNat(w,env) → Graph(e,w,env,x) → Num_k(B) →
  (Graph(original_addConst(k,e),w,env,y) ↔ Sum(w,x,B,y)))
~~~

外部k／e仅索引固定有限程序的证明模板，x、B、y和全部环境值均为内部对象，y没有预设自然性。原radix=128／256及实际var2表达式有专门闭句。没有调用Expr.eval、addConst_eval或宿主自然数算术作为对象结论。

反向按固定有限表达式的后继构造证明：零常量由对象加法零律及等号替换取得原表达式值；后继在对象EX中消去前驱基数和旧加法输出，使用真实加法后继律，再引入原graph的succ构造。正向在对象EX中取得规范加法输出，以原表达式graph唯一性将候选输出对齐，再作对象等号替换。外部归纳不作用于内部运行数据。

## 原规则完整局部矩阵

本批矩阵是HornRuleSyntax.matrix对锁定原Rule.head／guards／premises的纯关系式编译。原四条规则来自前批PacketAffineRuleData，保持实际原arity和常量，没有替换原程序。当前不声称这一层已经消去Rule.template的有界arity块，或完成原BasicSetTheory闭包条件的纯成员翻译对应。

记Row_i(w,d,t,n,r)为实际三字段原节点构造，Entry_i(w,V,d,t,n)=∃q(Row_i(w,d,t,n,q)∧q∈V)。i=0／1仅为两套原固定有限关系模板。对象推导在Ω及Num_radix(B)下，给出以下局部双条件：

~~~text
∀d,r,V (EnvNat(w,[d]) →
  (Matrix(original_affineBase,w,r,V,[d]) ↔
    ∃z (Empty(z) ∧ (Row_i(w,d,z,d,r) ∧ d∈B))))

∀d,t,a,r,V (EnvNat(w,[d,t,a]) →
  (Matrix(original_affineStep,w,r,V,[d,t,a]) ↔
    ∃s,y (Succ(s,t) ∧ (Sum(w,a,B,y) ∧
      (Row_i(w,d,s,y,r) ∧ Entry_i(w,V,d,t,a))))))
~~~

全部内部自然赋值均保留，候选r和V为任意内部对象；没有预设r已经具备正确结构。非自然赋值仍在全称量词范围内，但这些定理在EnvNat前提下断言双条件，没有宣称对所有非自然赋值的原矩阵拒绝。前驱、和、零元均在对象EX内实际取得并消去；最终局部双条件不再要求这些见证作为额外前提。

base真实比较guard恰为d∈B；step真实递归前提保留为Entry_i，绝不替换为已正确的仿射答案。MatrixAt辅助定理对齐任意实际后继／和见证，然后Local模块用对象存在性消去它们。最终BaseLaw为ALL3，StepLaw为ALL5，均由原量词规则构造。

PacketHornAffineLaws.exists_system仅以Ω为前提，实际给出：

~~~text
close(Ω(w) → ∃B (Frame_radix(w,B) ∧ (BaseLaw(w,B) ∧ StepLaw(w,B))))
Frame_radix(w,B) = B∈w ∧ Num_radix(B)
~~~

13组闭句均经TheoryTransport.sentence与ZFReplay.replay返回原nativeZF。它们不是宿主Prop或任意模型中的语义断言。

## 尚未消去的实际原应用和闭包

原HornApplicationSyntax.application的定义是对象EX arity块，内部体同时含EnvNat、EnvBound及实际Matrix。本批完成Matrix本身的双向对应；尚需对真实原head中的全部变量证明界、消去原arity赋值块并证明准确根行应用等价。不能删除EnvBound或把局部Matrix定理称为完整application定理。

已有HornStepSyntax.step可接受任意固定原规则表；但originalStep、HornLookupSoundSyntax.closed、HornLookupConditionSyntax.condition及HornUniversalTraceSyntax.value均特化于ObjectSyntaxTransform.rules。Packet必须使用其实际十规则建立相应轨迹，不能把旧Transform轨迹改名当成Packet轨迹。

整体condition与仿射算术的准确对应、内部逆digit／quotient、规范LEB128、版本／终止字节／完整消费仍待证明。原ProjectQuotation保留primitive subset，与最终纯成员展开及绑定移位也须单独桥接。结构树码、字节包和纯成员编译器继续严格区分。

## 验收、依赖与清理

- 定向原native构建1965任务、全仓2160任务成功，九命令及五个--trust=0入口均退出0，零警告。
- 新增8模块103项显式声明全部覆盖；累计23208项声明审计，458无公理、22750仅含记录的允许依赖。
- 先独立预审计103项声明及13对core／native精确足迹，再接入允许名单。core保持propext／Classical.choice／Quot.sound，native精确继承原七项固定证书，无新增对象Choice或自定义axiom。
- 1940份文件SHA256回读一致，累计2576对精确足迹一致，20864项Internal显式声明覆盖；前批所有布尔完成门保持原值。
- 七份理论／规则／工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且干净；前批跟踪的PPAC证明和AST不变。
- 清理8份被本批成功native构建及trust=0预审计替代的失败／警告日志：逻辑23702字节，实测释放40960字节。遗留编译进程0、停止0，有效源码、缓存及生成／回读脚本保留；清理后C盘98024251392字节可用。

本批新增四项完成门：原addConst对象加法对应、原仿射完整局部矩阵对应、全内部局部定律、实际字面量矩阵系统存在。原全局Horn-affine对应、完整NatPacket、varint、完整schema、Proof及最终Con门保持false。

验收前基点8595e571bcfda657fab0139d580c255adfc74409。本批8模块、4个接入文件及6份文档。证据verification/{summary.json,commands.json,build.log,audit.log,packet-horn-affine-readback.json}，.local/packet-horn-affine-preaudit.json及.local/workspace-cleanup-packet-horn-affine-result.json。复验C:/Python314/python.exe -X utf8 scripts/verify.py。仅本地提交，未推送。

## agent工程流程表

| 顺序 | 实现和依赖 | 对象层验收产出 | 状态 |
|---|---|---|---|
| T1.2c.2 | 真实十二构造Compiler、原Foundation及Separation | 全内部准确源接受及类型唯一纤维 | 前批已验收 |
| T1.2c.3a | Product／Sum、内部ω分解及128／256常量 | 仿射存在唯一及全内部递归方程 | 前批已验收 |
| T1.2c.3b.1 | 原addConst、既有graph、真实head／guard／premise | 原完整局部Matrix双条件，辅助见证消去，ALL3／ALL5及仅Ω系统EX | 本批已验收 |
| T1.2c.3b.2 | HornExprBounds.variable_bound证明原head全部变量的内部界；复用HornApplicationRules | 原arity=1／3的有界赋值块完整双向消去；准确根行application接口 | 下一步 |
| T1.2c.3c | 为实际ObjectPacket.rules建立闭轨迹；关系标签不交；原对象ω／成员归纳 | 原condition在所有内部候选上恰为仿射，消去轨迹与归纳前提 | 待完成 |
| T1.2c.3d | 对内部输出的对象ω归纳及除法余数界 | radix128／256逆digit／quotient存在唯一 | 待完成 |
| T1.2c.3e | 实际十规则的token／tree／forest／packet及内部结构归纳 | 全内部规范LEB128、版本／marker／完整消费及无效码拒绝 | 待完成 |
| T1.2c.3f | 原ProjectEncode／Quotation及primitive subset到纯成员的降语言 | 原字节源包到实际纯成员Compiler准确桥接 | 待完成 |
| T1.2d | 完整Separation／Collection模式及目标3句数值测试 | 全部内部码的准确原理论公理测试 | 待完成 |
| T2 | 全六规则／27模式及内部证明数据 | 完整Proof_T、实际checker准确性与原核推导传输 | 待完成 |
| T3 | 原PPAC数学论证的内部解释与证明码变换 | 内部Proof转换定理，保持PP／ACwo／¬AC和原背景 | 待完成 |
| T4 | 全部内部证明码的无矛盾式 | Derives nativeZF [] (Con_ZF→Con_target)及最终全仓原核审计 | 待完成 |

每批在新增允许项之前完成独立trust=0与精确公理审计；随后全仓构建、原核类型检查、哈希／理论锁／前批门禁回读，再本地提交。只在相应准确对象闭句证明后更新完成门。
