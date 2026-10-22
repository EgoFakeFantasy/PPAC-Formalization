# 全内部公式实际唯一重命名输出验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 e4f746d91e061076905d9f8ffc54f29964a43db3。
本批完成七类逻辑输出推进与对象成员归纳关闭：所有合法内部公式输入均实际存在唯一重命名输出。
精确单构造字段双条件、公式映射恒等/复合、捕获规避替换、ProofZF/U 及最终内部 Con 主句尚未完成。

## 固定对象目标和量化范围

对象语言仍是原 YesMetaZFC 的纯等词/成员语言，背景仍为原 nativeZF（Collection 呈现）的纯语言像。
最终终点保持 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，目标理论仍为 ZF+PP+ACwo+¬AC。
内部 Con 遍历全部内部 ω 证明码，检查原六规则、27 逻辑模式及完整 Separation/Collection。
不加入对象 AC、不可达、Con(nativeZF) 或外部标准模型前提。

Input(w,R,S,a,b,c,d,n) := FormulaCode(w,n,a,b) ∧ (MapCode(w,a,c,R) ∧ MapCode(w,b,d,S))。
Fiber := ∃q(RenameFormula(...,n,q) ∧ ∀t(RenameFormula(...,n,t)→t=q))。
Property(w,n) := ∀R∀S∀a∀b∀c∀d (Input→Fiber)。
Earlier(w,n) := ∀x((x∈w ∧ x∈n)→Property(w,x))。

这些是固定有限纯对象公式。全部码、实际完整图、作用域、输出及归纳下标仍在内部对象量词范围。
不限制外部标准码、外部有限深度或单射映射；独立目标范围不由列表码自动决定。
所有核心结论都有 Source.SetLanguage.ZF、sourceZF 原核及 nativeZF 原核的实际 Derives 证书。

## 完整11标签筛选及对象唯一性接口

原标签0–10下，完整 Cases 精确筛回对应原分支。
异标签分支均由原构造器标签互斥排除，内部字段见证由原存在规则消去。
外部 Fin 11 只索引原11个固定模式；源码和字段仍任意内部对象。
与前批候选解码图精确对齐组合，正式 RenameFormula 可在给定实际图下筛到同一分支。
关键证书：native_tagFilter、native_tagJudgment。

实际 Fiber 的内部全称唯一性可比较任意两个输出；给定内部 Property 和一个实际判断，
原核先恢复 Input，再得到 Fiber，因而比较全部候选，不额外假定目标自然性。
关键证书：native_fiberUnique、native_propertyUnique。

普通子判断保留原 RenameFormula；量词子判断是实际绑定两个后继和提升码的 AdvancedRename。
两者都有对象目标类型和自然性证明。
给 Property(w,x)，普通子判断使用同一映射参数；提升子判断正式取得首个候选提升，
把另一个候选通过已证 CodedLift 参数唯一性对齐，随后在提升作用域下实例化同一个六参数 Property。
关键证书：native_checkTarget、native_checkNatural、native_checkUnique。

## 全部七类的实际存在与唯一性推进

对子码 x，源类型和两幅合法 MapCode 加内部 Property 实际取得普通或提升输出。
量词路线从源 AdvancedCode 取得真实源后继 u 和体类型，原 Pairing/Union 实际构造目标后继 v，
原编码映射提升存在定理实际取得 L。CodedLift 的输出码性质给 MapCode(w,u,v,L)。
以 L、原 free 码 S、u,b,v,d 实例化 Property，实际取得体输出，再构造 AdvancedRename。
所有后继、提升码和输出见证均由原 exE 消去，没有宿主选择抽取。
关键证书：native_checkExists。

否定和四二元分支由原构造器从实际子输出生成目标码；两个量词分支使用上述实际 AdvancedRename。
目标类型来自已证原 FormulaCode 单构造类型双条件，目标作用域来自原 MapCode。
实际字段、严格源码成员界和子判断组成完整 Cases，再经原递归双条件接回 RenameFormula。
单子式只允许原4/false、9/true、10/true三个模式；外部模式证明不作为新增对象公理。
原核分别检查否定、forall、exists三个固定闭句模式及 Fin 4 的全部二元模式。
关键证书：native_negationAtOutput、native_forallAtOutput、native_existsAtOutput、native_binaryAtOutputs。

唯一性先由原同码字段单射对齐源码子式，再用 Earlier 给出同一子码的完整 Property。
子输出唯一性对齐目标字段，原目标构造唯一性给出父输出相等。
四/两个真实分支字段存在量词正式消去，故比较的是所有内部候选输出。
关键证书：native_singleDataUnique、native_binaryDataUnique、native_singleRelationUnique、native_binaryRelationUnique。

对给定源原构造，实际存在与唯一性组成 Fiber；两个 MapCode 解码图见证最终消去。
六次对象全称引入给出 Earlier→Property 的全部逻辑构造推进。
关键证书：三种 native_*ExistsAtGraphs、三种 native_*Fiber、三种 native_*PropertyStep，
及 native_binaryExistsAtGraphs、native_binaryFiber、native_binaryPropertyStep。
此处三种模式为 negation、forall、exists；二元模式的 Fin 4 参数覆盖原四类。

## 原 Foundation/Separation 关闭归纳

原 FormulaCode 完整分类给出四类原子和七类逻辑模式。
每个模式中的原源字段均经正式 exE 取得并消去，组合成任意内部码的 Property 推进。
关键证书：native_codePropertyStep、native_propertyStep。

归纳矩阵 matrix : Formula 2 固定为 Property(w,n)，内部量化全部 R,S,a,b,c,d。
原 BoundedInduction 的 Below 使用两个蕴含式守卫；本工程 Earlier 使用合取守卫。
本批以原全称/蕴含规则明确证明二者的所需转换，未把不同 AST 当作定义相等。
原 Foundation 和 matrix.neg 的一个完整 Separation 实例关闭内部集合 w 上的成员归纳。
这一步没有外部 WellFounded、标准ω或统一真值谓词；其它前置仍使用原 ZF 的既有推导。
关键证书：native_progressive、native_allProperties、native_naturalProperty。

最终取得不带 Earlier 的对象定理：

Ω(w) → ∀n(n∈w → ∀R∀S∀a∀b∀c∀d(Input→Fiber))。
Ω(w) → Input → Fiber。
Ω(w) → Input → ExistsOutput。
Ω(w) → RenameFormula(...,n,q) → RenameFormula(...,n,v) → q=v。

Input 自带源 FormulaCode 的内部自然码守卫；唯一性中的两个输出候选无需另加自然数前提。
关键证书：native_actualFiber、native_actualExists、native_unique、native_uniqueOutput。

## 全候选分类与实际验收

正式消去任意实际输出，原核恢复 Input。
故任意内部候选参数下，Ω 蕴含 ExistsOutput↔Input 以及 Fiber↔Input；非法输入正式推出 ¬ExistsOutput。
这些句子没有额外 Constructor、载体、历史、外部求值或 Earlier 前提。
关键证书：native_fiberIffInput、native_existsIffInput、native_rejectInput。

C:/Python314/python.exe -X utf8 scripts/verify.py 退出0。
两份原源规则/理论锁、版本、全仓 wfail 构建与五个 trust=0 入口共九条命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 763 jobs，退出0 |
| 声明审计 | 8423 项；284 项无公理依赖，8139 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 14模块、222项，全覆盖 |
| Internal 累计显式声明 | 6108 项，无漏审 |
| 新增闭句模式 | 40对核心/native精确足迹 |
| 累计闭句模式 | 773 对核心/native精确足迹 |
| 源码SHA256独立回读 | 732 份，差异0 |
| 九命令/五trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新核心证书精确依赖 propext、Classical.choice、Quot.sound；native另含原七个固定ZF定义证书的既有依赖。
没有新增自定义公理，没有扩大原choice额外闭性证书的隔离范围。
Classical.choice是宿主证明证书依赖，不是新增对象AC或内部集合选择函数。
CheckStep4逐一核验40类native闭句，另固定归纳矩阵、Below守卫和实际子输出存在的AST。
独立复核留在忽略目录 verification/rename-total-output-readback.json。
本批未运行原OpenAI完整构建/Comparator；生成辅助与日志留本地；未推送。

## 剩余工程与门禁

| 单元 | 固定输入 | 必须产生的后续对象证据 |
|---|---|---|
| F1e.4b | 给定原源/目标构造字段及已证完整递归双条件 | 每类构造的规范子判断双条件，显式对齐两端字段；不只交付筛选后的字段存在式 |
| F2 | 允许非单射的完整实际映射图与编码 | 公式重命名恒等、复合、量词下图提升兼容及原规则所需关系 |
| S | 任意内部替换序列、bound/free上下文 | 捕获规避Subst的实际存在唯一、类型、恒等/复合及rename兼容，覆盖原free_substitution/free_strengthening |
| 5–6 | 原六规则/27模式、完整ZF模式与精确目标公理码 | 专用ProofZF/U、全内部码编译正确性、解释及最终原核内部Con蕴含 |

全部合法内部公式的实际唯一输出和对象成员归纳关闭提升为True。
精确单构造律、映射代数、完整FormulaRename总门禁、替换、ProofZF/U及最终内部Con仍为False。
本批不把输出总性/唯一性升级成最终相对一致性定理。
