# 全11历史无关类型递归式与实际类型系统验收

日期2026-10-22；分支migration/yesmeta-step3。
本批基点b5a72def63a62c0411b1307cb520154c57a469d8。
完成4c.b.3c：全部内部候选码/上下文的历史无关完整类型递归双条件，
并在原ZF中实际取得ω、三层载体、完整状态递归及全称递归定律的闭句证书。
新增12个完整Source/sourceZF核/nativeZF核闭句模式。
原编码识别/构造正确性、内部替换、ProofZF/U和最终Con仍未完成。

## 对象合同

对象语言仍只有原等词/成员，背景仍为原ZF；最终证书使用原FirstOrder.Derives。
没有新增对象AC、Con、不可达、推导核或谓词公理。
Typed和新递归判据都展开为有限纯公式，不是内部统一真值谓词。
候选码、bound/free长度、后继集合、状态、历史及递归图均为对象变量。
外部Bool/Fin 4/Nat标签只索引有限原构造模式，每个实例返回完整对象闭句证明。

## 历史无关递归判据

AdvancedTyped(w,C,x,b,f):=∃k(Succ(k,b)∧Typed(w,C,x,k,f))。
StepCheck_false就是Typed(w,C,x,b,f)，StepCheck_true就是AdvancedTyped。
新SingleCase保留Ctx、原精确单字段构造、严格子码x∈n和StepCheck。
新BinaryCase保留Ctx、原精确二字段构造、x∈n、y∈n及两个相同上下文的Typed子式。
AllCases为原四种Atomic及否定、四种binary、两个量词的精确析取。
Criterion(w,C,n,b,f):=n∈w∧AllCases(w,C,n,b,f)。

| 原构造 | 标签/字段 | 历史无关子式条件 |
|---|---|---|
| falsum / truth | 0/1，零字段 | 原Atomic常量条件与完整Ctx |
| membership | 2，原scalar符号字段及两个项 | 原关系编号0及同上下文Term |
| equal | 3，两个项 | 两个同上下文Term |
| neg | 4，单字段x | Typed(w,C,x,b,f) |
| conj / disj / imp / iff | 5/6/7/8，x,y | Typed(w,C,x,b,f)∧Typed(w,C,y,b,f) |
| forall / exists | 9/10，单字段x | ∃k(Succ(k,b)∧Typed(w,C,x,k,f)) |

检查的是语法类型。neg不否定子式类型，disj/imp仍要求两个子式都类型正确。
量词体free保持f，bound由真实内部后继见证改变，不冻结父式b。

## 原核双条件证明

完整历史图h的域为n、Ω(w)、n∈w且x∈n时，先由对象ω传递性推出x∈w，
再用前批已证实际图值/类型对应，证明Read(h,x,b,f)↔Typed(w,C,x,b,f)。
同样对全部内部后继见证k迁移Advanced，不以外部标准索引或宿主取值替代。

迁移逐一保留原构造、完整字段及严格子码界；旧单字段/二字段分支与新分支双向等价。
组合全部11个分支，得到真实历史下Local↔AllCases。
实际Separation状态给出Edge(V,b,f)↔Local，实际状态值给出Typed↔Edge(V,b,f)，
因此得到Typed↔Criterion。

最终recursive_iff对全部内部候选n,b,f成立，只要求Ω(w)、实际A=P(w)、C=P(A)。
不把n∈w作为最终句子的额外前提：自然分支实际构造状态值；非自然分支由两边根守卫正式拒绝。
输出是对象Formula.iff的Derives，不是Lean命题等价或模型语义断言。

## 消去ω与载体存在前提

UniversalLaw(w,C):=∀n∀b∀f(Typed(w,C,n,b,f)↔Criterion(w,C,n,b,f))。
它量化全部内部集合候选，不仅是外部标准公式样本。

System(w)实际存在A,C,U，保留：
Tower(w,A,C,U)、该C上的全部内部原序数唯一完整递归图、UniversalLaw(w,C)。
原PowerSet和已有全Separation/递归证明实际取得这些见证，未从Prop抽取宿主集合。
进一步由原Infinity、Extensionality和Separation取得真实最小归纳集ω，
证明闭句∃w(Ω(w)∧System(w))，没有残留额外存在前提。
ObjectSyntaxTypeRecursive.native_existence是该完整闭句的原nativeZF证书。

## 实际验收

9个新模块、96项显式声明全部加入Audit。
12个闭句模式：read、advanced、check、single、binary、local、atState、atValue、
recursive、universal、actualSystem、existence。
CheckStep4另检查四个binary实例、否定和两个量词实例、真实后继AST、
全内部三重量词、根自然守卫和实际系统存在闭句。

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：两个固定源锁检查、Lean版本、全仓wfail构建，以及
Check/CheckStep2/CheckStep3/CheckStep4/Audit五份lake env lean --trust=0入口。
604个构建任务；5874项声明审计；235项无公理依赖、5639项允许依赖；0警告。
Internal累计3559项显式声明全覆盖；累计377对核心/native证书或模式通过精确依赖核验，新增12对。
新增核心恰为propext、Classical.choice、Quot.sound；native端点另继承原七项ZF证书。
Classical.choice是Lean证明基础依赖，没有引入对象AC；原choice额外证书仍单独限域。
573份源码SHA256独立重算差异0；原19规则、九类源ZF、两份可信基和依赖锁不变。
固定YesMetaZFC仍为039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
本地回读verification/syntax-type-recursive-readback.json；日志/探针/哈希不入库。
本批未推送；原OpenAI完整构建与Comparator未运行。

## 已通过与仍未完成

object_bound_free_context_type_recursion_proved现为True：
实际状态、原递归图、全部内部上下文、前段读取对应及全11历史无关递归式均有原核证据。
完整原编码识别/构造关卡尚未验收，因此object_all_eleven_formula_constructors_type_check_proved保持False。

下一关4c.b.3d消去载体参数并与原编码精确接合，证明已知原码的具体类型分支、
合法输入实际构造、完整字段恢复和错码排除；不能只跑外部标准SyntaxEncode样本。
然后完成内部非单射捕获规避替换、ZF/U原六规则/27模式检查、任意内部证明码正确性和内部编译器。
最终Derives nativeZF [] (Formula.imp Con_ZF Con_target)仍未完成，相关门禁均保持False。
