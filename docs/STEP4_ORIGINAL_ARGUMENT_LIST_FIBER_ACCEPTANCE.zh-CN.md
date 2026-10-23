# 原参数列表内部归纳与实际唯一输出验收

基点：62c9491f534c108f940170a27397cc87d2c16226。完成S3.4c.2b.2c.3c.2c.2b.3c：原mode0／3运行在任意内部有类型源列表上实际存在唯一有类型输出，保持准确内部长度。与独立变换的完整逐字段对应仍待3d，不能据本批宣称全部列表变换正确性或最终Con完成。

## 对象合同

语言为原YesMetaZFC纯等词／成员，背景为原nativeZF完整Collection呈现，正式关系为原FirstOrder.Derives。最终目标仍为Derives nativeZF [] (Con_ZF → Con_target)，target为ZF+PP+ACwo+¬AC。内部Con的全部内部ω码、原六规则／27模式、完整Separation／Collection保持不变；该最终推导尚不存在。

本批每组闭句都由Source.Derives实际证明，经TheoryTransport和ZFReplay取得原nativeZF原核推导。不引入对象AC、标准ω、外部良基、模型或新推导核，不使用退役反射。宿主Bool只索引固定两个模式；源／目标列表、长度和所有输出候选均为对象变量。

## 对象输出与归纳属性

```text
Unique₂(w,μ,depth,param,n,q) :=
  ∀v (Run₂(w,μ,depth,param,n,v) → v=q).
Value₂(w,μ,depth,param,k,c,d,n,q) :=
  Run₂(w,μ,depth,param,n,q) ∧
  (TermList(w,k,c,d,q) ∧ Unique₂(w,μ,depth,param,n,q)).
Fiber₂(w,μ,depth,param,k,c,d,n) := ∃q Value₂(...,n,q).
Property(n) := ∀k (TermList(w,k,a,b,n) → Fiber₂(w,μ,depth,param,k,c,d,n)).
Earlier(n) := ∀t (t∈w → t∈n → Property(t)).
```

固定模式／元数据／源目标上下文及上批真实对象头Promise，原Separation／Foundation在集合w上对码n作成员归纳，得到∀n(n∈w→Property(n))。输入码自然性由实际TermList取出，内部长度k仍在属性中量化；没有把内部列表或k转换成宿主List／Nat。对象模型即使外部非标准也未假定其外部良基或标准ω。

一般actual_fiber端点要求Omega、实际Num0／Num3、深度／参数自然守卫、目标上下文及头Promise。其正式闭句不保留Earlier／归纳假设。两个模式特化再用真实恒等／位移／转换列表推导头Promise及目标上下文，因此正式mode0／3端点也不保留未解Promise或agreement前提。所有实际环境前提继续显式保留。

## 实际Nil／Cons证明

Nil分支用源Nil码本身作为实际输出见证；由相同原Nil输入／输出、Empty长度及目标上下文构造准确类型和原Run₂。任意候选运行按原整体方程拆成Nil或Cons；候选Cons与源Nil互斥，候选Nil由原Nil唯一性相等。没有选择外部空列表。

Cons分支由完整类型Cases取得实际自然头尾码、内部前驱长度ell、合法头项及有类型尾列表。原结构编码的严格成员性质给t∈n，因此Earlier(t)正式给尾的实际唯一输出；原项Promise给头的实际唯一输出。所有存在量词均由Source.exE消去，原Cons存在性实际构造父输出，原类型构造保持Succ(k,ell)下准确长度，原整体Run₂方程给真实父运行。

唯一性量化任意内部输出候选v，不预给候选自然性或类型。候选原Run₂拆出四个实际组件及两个真实子运行；组件自然性来自真实子运行，不能单凭ConsCode假定。原Cons输入单射对齐头尾输入，新的原Run输入等词替换传输候选子运行。实际头／尾Value的全候选唯一性对齐输出组件，再由Cons组件等词替换及原Cons唯一性得到v=q。由此关闭全部内部候选，而非仅比较构造出的候选。

## 模块与闭句

| 模块 | 本批对象产物 |
|---|---|
| OriginalRunValueSubstitution | 原任意kind运行输入／输出及Cons头尾的正式等词替换 |
| OriginalArgumentValueSyntax | 全候选Unique₂、准确目标类型Value₂、Fiber₂、内部长度Property和Earlier |
| OriginalArgumentOutputUnique | 实际Nil互斥、Nil唯一性及Cons对子运行对齐后的全候选唯一性 |
| OriginalArgumentValueConstruct | 实际Nil／Cons值和存在纤维构造 |
| OriginalArgumentHeadTailFiber | 头Promise及尾Fiber存在见证正式消去／父Fiber构造 |
| OriginalArgumentValuePoint | 较小实际尾码的归纳步、完整类型Cases处理 |
| OriginalArgumentValueInduction | 原Separation／Foundation关闭全内部码成员归纳，消去Earlier |
| OriginalArgumentModeFiber | mode3替换与mode0弱化实际环境特化，消去头Promise |
| ObjectOriginalArgumentFiber | 10组闭句Source→原核→原nativeZF |

10组模式为originalRunInputSubstitution、originalRunOutputSubstitution、originalListValueTargetType、originalListAllCandidateUnique、originalNilListActualValue、originalConsListActualValue、originalAllInternalTypedListFiber、originalAllInternalListCodeProperties、replaceAllInternalOriginalListFiber、weakenAllInternalOriginalListFiber。源列表长度k及输入码n不受外部有限界限制。

## 实际验收与可信基

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalArgumentFiber和C:/Python314/python.exe -X utf8 scripts/verify.py均实际退出0。全仓1405构建任务、15415项审计（378无公理／15037记录允许依赖）、零警告；九命令及五trust=0入口全部退出0。Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增9模块79显式声明及10组闭句；每组核心依赖精确为标准三项，native精确为标准三项加原七固定句子证书依赖。全仓1712对精确证书足迹、13071项Internal显式声明覆盖。1269份工作区独立哈希无差异，七份锁文件、隔离Choice桥和固定底座039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。既有45项执行／分支直接oracle检查保留；新增Value／Fiber是原执行结果规格，未改写原执行或加入独立执行器。

本地日志：verification/commands.json、verification/audit.log、verification/list-fiber-readback.json。未运行OpenAI全仓构建／Comparator，未推送或创建PR。

## 未完成门

四个精确细门通过：类型码成员归纳已关闭、全内部有类型列表实际唯一输出、输出准确目标长度／类型、两个模式的头Promise已消去。完整列表变换正确性门保持false；其余较宽列表递归／完整数值接口门也不由本批自动通过。下一步3d须证明全部内部索引的逐字段对应及与独立变换的双条件，而不把本批有类型唯一输出当成变换规格已经对应。

全十一公式、量词深度／环境提升、原扩展语言quotation总桥、原规则兼容、ProofZF/U全内部证明检查／编译、内部解释及最终Con仍未完成。
