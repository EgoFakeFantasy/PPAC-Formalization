# 全内部字段严格界与实际树算子递归图验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点568ea61ffbc712e4a71448d9ab5d56bc34de7f5f。
本批完成4b.c.4c.v.b.i–ii：全部域内字段严格子码界、具体树前段算子及实际唯一完整递归图。
完整树接受/拒绝正确性、实际树解码、专用ProofZF/U及最终内部Con仍未完成。

## 对象合同及字段界

语言仅含等词与成员关系，背景原ZF。证明使用Source.Derives，经TheoryTransport/ZFReplay取得
原FirstOrder.Derives nativeZF []完整闭句；未新增公理核、对象AC、Con或外部标准ω假设。

Ω(w)、HasLength(w,n,l)、i∈l、Field(w,n,i,y)正式推出y∈n。
量词覆盖全部内部长度、全部域内索引及任意候选输出对象；结论为实际严格成员界。
原完整Fields(w,n,l,f)和edge(f,i,y)给出i∈l及该字段关系，故全图字段也严格属于原列表码。
原自然标签tag、Raw(w,tag,p,n)、HasLength(w,p,l)下，p的全部域内字段严格属于父码n。
后一结论组合已证p∈n、字段y∈p和原自然数的传递性，未将字段自然性冒充严格界。

证明对实际长度作原Separation支持的对象ω归纳。
空长度无域内索引；后继长度反演实际Cons及给定前驱尾长度。
零字段等于原head，使用原Cons头界；后继字段来自tail，在真实前驱域内应用归纳假设，
再经tail∈n和内部传递性取得当前码严格界。没有宿主Nat/List归纳或外部良基假设。

## 具体树前段算子

严格保留固定上游的treeValue(node(tag,children))=Pair(tag,forestValue(children))+1，
子字段使用已验收原Nil/Cons列表数值格式；原空列表码为内部单位。
本批建立一般自然标签raw树算子，公式语法的有限标签及全部11种原生构造另属后续关卡。

Shape(w,n,tag,p,l,f):=(tag∈w∧Raw(w,tag,p,n))∧(HasLength(w,p,l)∧Fields(w,p,l,f))。
Marks(e,f,h):=∀i∀y(edge(f,i,y)→edge(h,y,e))。
Children(e,n,f,h):=∀i∀y(edge(f,i,y)→(y∈n∧edge(h,y,e)))。
Good(w,e,n,h)实际存在量化tag,p,l,f四个内部见证，要求Shape和Children。
Step(w,z,e,n,h,y):=(Good(w,e,n,h)∧y=e)∨(¬Good(w,e,n,h)∧y=z)。

在Ω(w)及Shape下，Marks↔Children有实际对象推导：所有H历史查询点的严格界均由字段定理消去。
显式界没有额外排除原完整字段图；每个内部边和任意输出对象都在对应式范围内。
空子字段长度的Shape满足Good，任意历史h均可；Good推出根非空，空根处Step输出z。
这些是具体局部算子的叶/零规律，不将其标为完整树检查的接受/拒绝定理。

算子本身不引用树有效性或宿主判定器。实际零z和单位e满足Empty(z)、Succ(e,z)时，
每个Step输出y属于内部ω，且y=z或y=e。总性和单值性对任意输入索引/历史均实际证明。

## 实际唯一递归图

具体矩阵为Step(0,1,2,3,4,5)，最后三槽严格依次为索引、完整前段图和输出。
以原OrdinalRecursionSyntax.operator及recursor接入原对象超限递归。
每个递推行仍实际量化原完整图的前段限制h；H是对象集合图。

Recursors(w,z,e):=∀a(Ordinal(a)→∃f(Recursor_Step(f,a)∧∀g(Recursor_Step(g,a)→g=f)))。
对任意w,z,e，原ZF正式证明该闭句；算子Total/Deterministic两个义务已实际消去，不保留为额外前件。
原Ω(w)还实际取得∃z∃e((Empty(z)∧Succ(e,z))∧Recursors(w,z,e))。
因此已交付真实内部零/单位标志及全部内部原序数上的完整递归图存在唯一；不是只有算子AST或条件式递归定理。

后续仍需把不同实际前段图上的子码值与统一树求值关系对齐，证明完整递归接受/拒绝双条件及实际解码。
当前图存在唯一不能单独替代这些正确性义务，也不构成专用ProofZF/U或最终Con主句。

| 模块 | 本批已完成职责 |
|---|---|
| StructuralListFieldBoundsSyntax/Step/FieldBounds | 全长度域内字段严格界、完整图边界及父raw节点组合界 |
| ObjectStructuralFieldBounds | 四个完整字段/父码界闭句的源ZF及原nativeZF证书 |
| StructuralTreeOperatorSyntax | 真实四重见证Shape/Good、严格历史查询、二值Step和原递归接口 |
| StructuralTreeOperatorLogic | Shape子码界、Marks↔Children、空子字段叶条件、Good根非空 |
| StructuralTreeOperatorStep | 实际总单值、零根局部规律、实际零/单位输出范围 |
| StructuralTreeRecursors | 消去算子义务，取得全内部序数实际唯一完整图和真实标志见证 |
| ObjectStructuralTreeOperator | 十个完整树局部算子/实际递归图闭句的源ZF及原nativeZF证书 |

四个字段端点为fieldBound、edgeBound、rawFieldBound、rawEdgeBound。
十个树端点为shapeBound、childrenIff、leafGood、positiveGood、range、zero、functional、recursors、ordinalFiber、actualUnits。
每个端点有source_*、*_kernel_certificate和native_*。
CheckStep4核对全字段量词、最终严格界无归纳前提、Shape实际载荷/完整图、严格历史查询、四重见证、
原二值Step、递归句没有Total/Deterministic前件、实际零/单位存在句及全部十四个原核端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成515个任务。
Check、CheckStep2、CheckStep3、CheckStep4及Audit五个入口均以--trust=0通过。
4511项声明审计：203项无公理依赖，4308项允许依赖；0警告。
本批9个模块114项声明全部显式审计；Internal具名覆盖门禁累计2196项。
484份源码SHA256独立复核，差异0；累计199对核心/native证书或模式精确依赖核对通过。
新增十四个核心恰为标准propext/Classical.choice/Quot.sound，native端点恰额外继承原七个ZF闭性证书。
上述是Lean证明证书依赖，未向对象ZF加入AC。
两份可信基JSON、原choice额外证书限域、原19规则/九类源ZF、固定依赖及原核不改；未新增自定义公理。
原OpenAI完整构建及Comparator未运行；未推送。日志/依赖/哈希及独立回读仅保留本地verification/。
独立回读：verification/field-tree-recursors-readback.json。

## 下一最小工程

4b.c.4c.v.b.iii定义树求值，保留实际后继域、完整Recursor图和该索引的真实边。
由已证全序数唯一图实际取得每个内部自然码的唯一求值；证明前段图子码值与该求值一致。
用严格字段界消去历史覆盖前提，证明Good的完整递归子树刻画，再完成接受/拒绝正确性与实际唯一树解码。
树总门禁、专用ProofZF/U、任意内部证明码正确性、内部编译器及最终Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
