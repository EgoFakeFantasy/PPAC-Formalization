# 首槽实际环境表及原数值码对验收

2026-10-23；分支migration/yesmeta-step3；本批基点75f2697fb5536fef57c317424c1bc2f7c555c676。
S3.4a/S3.4b的实际环境表与原码对已验收。原instantiate/abstract操作的数值quotation对应及最终内部Con尚未完成。

## 固定对象合同与边界

语言是原纯等词/成员语言，背景为原nativeZF完整Collection呈现，源完整Replacement经已证对象互导接入。
最终要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target为ZF+PP+ACwo+¬AC。
Con_T的固定规格为¬∃p(p∈ω ∧ Proof_T(p,code(⊥)))，量化全部内部ω证明码，保留原六规则/27模式与完整Separation/Collection。
该Con仍是锁定数学规格；专用ProofZF/U完整纯AST、全内部检查/编译正确性及最终对象主句尚未实现。
本批实际交付原对象推导，不能把环境表、外部标准quotation或编译成功当最终一致性证明。

## 从索引到真实变量项码

索引图的值是内部索引j，项像表的值则是完整bvar/fvar码q，二者不能直接当同一个对象。
明确有限纯矩阵为：

```
VariableImageValue(bound,w,r,c,d,i,q) :=
  ∃j (Edge(r,i,j) ∧ Code(bound,w,j,q) ∧ Term(w,c,d,q)).
```

给定完整IndexMap(w,r,a,limit(bound,c,d))和目标Contexts(w,c,d)，每个域内索引实际有唯一值。
原Replacement构造实际唯一完整项码图f，所有候选满足精确边关系。
给定实际索引边Edge(r,i,j)，Edge(f,i,q)恰等价于Code(bound,w,j,q)。
恒等索引图和后移索引图均实际取得，再转为真实变量项码表；隐藏图见证不影响表的唯一性。
两个变量类别由有限外部Bool模式分别给出闭句实例，未使用宿主数据选择函数。

## InstantiateTop实际环境

输入是Term(w,a,b,t)及Succ(A,a)。输出实际完整表f/g的源范围为(A,b)，目标范围为(a,b)。
对象内部实际取得bound恒等项码尾表u，对它增加给定项码t头槽；free表为完整free变量项码恒等表。
准确字段律为：

- 空索引i：Edge(f,i,q) ↔ q=t；
- j∈a、Succ(i,j)：Edge(f,i,q) ↔ BVarCode(w,j,q)；
- i∈b：Edge(g,i,q) ↔ FVarCode(w,i,q)。

f/g实际存在唯一，隐藏尾表完全在对象存在量词内。
目标项可以属于任一合法变量类别，不强迫其与源bound类别一致。
a=0或b=0保留；若(a,b)都空而纯语言没有合法项t，准确输入谓词会拒绝该输入。

## AbstractFreeTop实际环境

输入是Contexts(w,a,b)、Succ(A,a)、Succ(B,b)。输出实际完整表f/g的源范围为(a,B)，目标范围为(A,b)。
f将旧bound索引后移；g由free恒等尾表增加真实bvar0码头槽。
空集索引与bvar0码均在对象量词内实际取得，任意两份头见证按原空集唯一性及变量码唯一性对齐。
准确字段律为：

- i∈a、Succ(j,i)：Edge(f,i,q) ↔ BVarCode(w,j,q)；
- 空索引i：Edge(g,i,q) ↔ BVarCode(w,i,q)；
- j∈b、Succ(i,j)：Edge(g,i,q) ↔ FVarCode(w,j,q)。

两张实际表共同唯一；空源范围和所有内部非标准自然索引也由同一对象证明覆盖。

## 原自然列表码与实际公式纤维

两张完整表用原Encoding转换成真实原自然列表码R/S，图见证在内部存在量词中。
原数值码对实际存在唯一，具有准确TermLists及自然码守卫。
存在码对、实际唯一码对纤维分别恰与上述准确输入等价。
六条原列表字段双条件保留源域守卫：i∈对应源范围 ∧ Field(w,R或S,i,q)。不能删除域守卫而解释表外字段。

这些具体码对已接入上一批一般混合公式替换：
在InstantiateTop码对及FormulaCode(w,n,A,b)下，实际取得MixedFormulaSubst(w,R,S,A,b,a,b,n,q)的唯一输出纤维。
在AbstractFreeTop码对及FormulaCode(w,n,a,B)下，实际取得MixedFormulaSubst(w,R,S,a,B,A,b,n,q)的唯一输出纤维。
当前是固定真实码对下的对象输出纤维，尚未提供原操作数值quotation对应或完整见证消去后的操作判断。

## 实际原核验收

ObjectTopEnvironment提供52组Source闭句、sourceZF映像原核证书及nativeZF原核证书，返回原FirstOrder.Derives nativeZF []。

992构建任务、11603项审计、0警告；九命令与五个trust=0入口均退出0。
本批24模块381显式声明、52组闭句；累计9288项Internal声明全覆盖，961份源哈希独立一致，1204对核心/native精确足迹。
308项无公理依赖、11295项允许依赖；每组核心足迹精确std3，native精确std3加原七项证书。
七份锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6且工作区干净。
独立回读核对全部源哈希、全部精确证书对、声明覆盖和未完成门。
执行C:/Python314/python.exe -X utf8 scripts/verify.py；原OpenAI完整构建/Comparator未运行；未推送或建PR。
生成器、日志和独立回读仅留本地忽略目录。

## 后续agent流程

| 单元 | 输入/依赖 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S3.3b | 原混合环境码、完整FormulaCode | 全内部ω混合公式实际总唯一、11端点、输入/纤维双条件 | 已验收 |
| S3.4a | 合法目标项、bound后继范围 | InstantiateTop实际完整表/原数值码对、真实唯一纤维、准确输入与零/后继/free字段 | 已验收 |
| S3.4b | 两个内部后继范围 | AbstractFreeTop实际完整表/原码对、真实唯一纤维、准确输入与bound/free0/free后继字段 | 已验收 |
| S3.4c.1 | 本批环境码及一般混合公式替换 | 环境见证无关的首槽公式判断、准确类型、存在唯一与内部递归端点 | 固定码下实际公式纤维已验收；完整操作判断待完成 |
| S3.4c.2 | 原instantiate/abstract与原数值语法 | 原操作quotation对应及嵌套binder保护；两张像表都位移 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 原数值编码对应及规则5/4任意内部证明码检查兼容 | 待完成 |
| 5a | 六规则、27模式及完整ZF/U公理 | 专用有限纯ProofZF/U AST，精确原元数据，0合法且域检查准确 | 待完成 |
| 5b | 原推导转换器和内部语法操作 | 全部内部ω码上的编译/检查正确性，完整Separation/Collection | 待完成 |
| 6 | 内部解释和固定Con规格 | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

一般混合替换的递归端点已经同时提升两张环境表；将此事实与原instantiate/abstract数值操作对接仍须独立证明，不能据表存在唯一直接升级完整捕获规避或Con总门。
