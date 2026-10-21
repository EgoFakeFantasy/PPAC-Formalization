# 实际带类型原码构造与接受根完整字段验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点118924c10dbf80f148937f2190d968c219853107。
本批完成4c.b.3d.2a；同时完成接受根的实际完整字段唯一解码/重编码，以及精确内部标签/字段数分类和非匹配Shape拒绝。
新增12模块259项显式声明、46个完整Source/sourceZF核/nativeZF核闭句模式。
完整递归字段类型解码、原树有效性、内部替换、ProofZF/U及最终Con仍未完成。

## 原对象合同保持不变

签名只有原等词/成员；背景是原YesMetaZFC的ZF纯语言像；所有最终证书使用原FirstOrder.Derives。
不添加对象AC、Con、不可达、语义模型或新的推导核。
所有实际码、上下文、标签值、长度、payload及完整字段图均为对象变量。
外部Nat/Bool/Fin及有限变量向量只索引原构造的有限定理模式，不把内部ω限制为外部标准自然。

## 实际构造及唯一性

TypedAt(k,tag,w,xs,n,b,f):=Constructor(k,tag,w,xs,n)∧FormulaCode(w,n,b,f)。
TypedFiber实际存在n∈w及TypedAt，且∀r(Constructor(k,tag,w,xs,r)→r=n)。
唯一性覆盖所有原构造候选，不仅已经知道有类型的候选。

通用构造桥使用原实际Constructor唯一纤维和对象全称类型定律Law。
每个具体原模式的Law已由上一批已知码类型双条件实际证明，因此下面的具体证书没有残留Law存在或可证前提。

| 原构造 | 实际构造所需合法输入 | 带类型输出 |
|---|---|---|
| falsum、truth | 真实Ω及完整Ctx | 原标签0/1、零字段的TypedFiber |
| membership | 原ZeroScalar符号及两个同上下文Term | 原标签2、保留s,x,y的TypedFiber |
| membership自动符号版 | 仅真实Ω和两个同上下文Term | 实际存在原zeroScalar符号及对应TypedFiber；不另假定符号码存在 |
| equal | 两个同上下文Term | 原标签3、保留x,y的TypedFiber |
| negation | Ctx及子FormulaCode | 原标签4、保留x的TypedFiber |
| conj、disj、imp、iff | Ctx及两个同上下文FormulaCode | 原标签5/6/7/8、保留x,y的TypedFiber |
| forall、exists | Ctx及∃k(Succ(k,b)∧FormulaCode(w,x,k,f)) | 原标签9/10、保留x的TypedFiber |

合法子式条件实际推出所有输入的自然守卫；没有额外要求用户提供子码自然性证明。
量词输入的bound变化是实际对象后继，free仍为f；没有固定父bound或使用宿主标准后继。
46个原核闭句模式中包括每种类型定律、实际唯一纤维及忘掉唯一性的实际存在证书。
关键接口为ObjectFormulaCodeConstruction.native_*Law、native_*Fiber和native_*Exists。
native_membershipFiber在两个Term前提下实际取得编号0符号及带类型原码。

## 接受根的真实完整字段

先证明任意原精确森林都是原结构列表有效码，再实际取得唯一内部长度与完整有序字段图。
由任意原Node/Constructor取得真实Shape；所有11接受分支进而得到：
Ω(w)∧FormulaCode(w,n,b,f) → ShapeFiber(w,n)。

ShapeFiber对象存在量化标签t、payload p、长度l、完整字段图g，
并对任何其他真实Shape证明这四项分别相等。
Shape保留原Raw、实际HasLength及Fields；Fields展开为完整functionOn、ω值域和全边精确双条件。
这不是截取几个外部标准位置；候选长度和所有图边均在对象层。

原根n本身实际满足Encoding(w,t,l,g,n)。
对任意重编码输出r，原核证明Encoding(w,t,l,g,r)→(r=n∧FormulaCode(w,r,b,f))。
该结果使用真实解码字段和原编码唯一性，通过对象根等词替换保留类型。
ObjectFormulaCodeConstruction.native_acceptedShape、native_shapeUnique、native_roundTrip及native_reencoding是完整原核闭句模式。

这里交付的是根的完整结构字段及原码往返。
还需逐位置将实际g的边与递归操作数的完整FormulaCode/Term/scope条件对应；
没有将根Shape解码等同于完整递归TypedData解码，也没有据此声称原树的递归有效性已证明。

## 内部标签/字段数分类与拒绝

对任意内部实际长度l，原Constructor(k,tag,...)及同根真实Shape推出Num_k(l)。
该证明实际构造内部数码，再用原长度唯一性和对象等词替换；不枚举外部长度候选。

Allowed(11,t,l)是固定有限纯公式，接受且仅列出以下内部数码配对：
(0,0)、(1,0)、(2,3)、(3,2)、(4,1)、(5,2)、(6,2)、(7,2)、(8,2)、(9,1)、(10,1)。
原核证明任何接受根的任意真实Shape都满足Allowed。
在Ω(w)、Shape(w,n,t,p,l,g)及¬Allowed前提下，正式推出¬FormulaCode(w,n,b,f)。
标签值和长度候选都是对象变量，包括外部非标准模型中的内部自然候选。

完整符号/项/递归子式/作用域的逐字段分类仍待装配；
不得把当前标签/字段数分类称作全部错误码的最终分类。

## 实际机器验收

执行C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
九条正式命令均退出0：原19规则锁、原九类ZF锁、Lean版本、完整wfail构建，
以及Check、CheckStep2、CheckStep3、CheckStep4、Audit五份--trust=0入口。

- 构建632任务，审计6349项声明，0警告。
- 242项无公理依赖，6107项允许依赖；Internal累计4034项显式声明全覆盖。
- 累计452对核心/native证书或模式精确依赖核验，新增46对。
- 核心证书恰为propext、Classical.choice、Quot.sound；native证书另继承原七项ZF证书。
- Classical.choice为Lean证明基础依赖，没有新增对象AC；原choice额外证书仍单独限域。
- 601份源码SHA256独立回读差异0；原规则、理论、两份可信基及工具链/依赖锁不变。
- YesMetaZFC仍固定039c8e132cc19671d73a3933c66b4799d2599dd6且依赖工作区干净。
- 原OpenAI完整构建与Comparator未运行；本批未推送。
- 日志、生成脚本、探针及回读留在忽略目录；独立回读为verification/formula-code-construction-readback.json。

CheckStep4覆盖全部46个闭句模式、两种零元具体实例、实际TypedFiber存在/唯一AST及全部11标签的原字段数。
Audit枚举12新模块的全部259项显式声明，verify.py对46个新核心/native证书逐项核对精确公理足迹。

## 工程流程及剩余验收

| 工作单元 | 已取得的对象证据 | 当前状态 |
|---|---|---|
| 4c.b.3d.2a | 全11合法输入实际唯一带类型原码，membership实际零符号 | 完成 |
| 4c.b.3d.2b根数据 | 接受根唯一完整字段图、真实内部长度、原根重编码及保留类型 | 完成 |
| 4c.b.3d.2c根配对 | 全内部候选的精确标签/字段数分类及非匹配Shape拒绝 | 完成 |
| 4c.b.3d.2b.i | 所有内部位置的完整边与递归类型操作数对应 | 下一主项 |
| 4c.b.3d.2b.ii | 全上下文类型码/纯项码到原StructuralTree.valid的对象归纳 | 待做 |
| 4c.b.3d.2c.i–3 | 完整TypedData实际唯一解码、反向识别及全部递归错误字段/作用域排除 | 待做；总关卡False |
| 4c.c及以后 | 内部捕获规避替换、ProofZF/U、任意内部证明码正确性、内部编译器 | 待做 |
| 最终主句 | Derives nativeZF [] (Formula.imp Con_ZF Con_target) | 未完成 |

最新详细职责及验收表见AGENT_WORKFLOW.zh-CN.md，原背景与内部Con规格见OBJECT_TARGET.zh-CN.md。
本批未缩小原目标；object_all_eleven_formula_constructors_type_check_proved和object_Con_theorem_proved仍为False。
