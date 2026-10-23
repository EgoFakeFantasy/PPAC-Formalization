# 原数值项实际唯一输出及全内部项承诺验收

基点：306539b99a547b14167ece37d6dfd262894ab175。完成S3.4c.2b.2c.3c.2c.2b.3b：原mode0／3纯签名项运行的实际有类型唯一输出及全部内部有类型输入的对象承诺。列表码的内部归纳与列表变换正确性仍未完成。

## 背景与正式接口

保持原纯等词／成员语言、原nativeZF完整Collection及原FirstOrder.Derives。最终仍要求Derives nativeZF [] (Con_ZF → Con_target)，其中target为ZF+PP+ACwo+¬AC；内部Con遍历全部内部ω证明码、原六规则／27模式和完整Separation／Collection。本批没有该最终推导。

每个本批Sentence由实际Source.Derives证明，经TheoryTransport传入原核，再经ZFReplay返回原nativeZF。新增模式不加入对象AC、标准ω、模型或新公理核；没有使用退役反射。宿主Bool／模式名仅索引两个固定原操作，输入、输出及唯一性候选均由对象量词约束。

## 精确对象公式

沿用原完整规则表关系式五字段Run₁，执行定义未改变。令：

```text
Unique(w,μ,depth,param,n,q) :=
  ∀v (Run₁(w,μ,depth,param,n,v) → v=q).
Value(w,μ,depth,param,c,d,n,q) :=
  Run₁(w,μ,depth,param,n,q) ∧
  (Term(w,c,d,q) ∧ (q∈w ∧ Unique(w,μ,depth,param,n,q))).
Fiber(w,μ,depth,param,c,d,n) := ∃q Value(...,n,q).
Promise(w,μ,depth,param,a,b,c,d) :=
  ∀n (Term(w,a,b,n) → Fiber(w,μ,depth,param,c,d,n)).
```

Unique的所有候选v均任意，不要求候选自然性或目标类型；这些性质在真实原运行和正式证明中恢复。Promise不是外部逐个Lean项函数，而是一个实际对象全称公式。存在输出不通过Lean选择抽取。

比较辅助agreement为∀q(Run₁(n,q)↔TermProgram.run(n,q))。一般传输引理显式要求该公式及既有实际程序Value／Fiber；这仅是辅助接口。两个模式的最终Fiber／Promise定理均用真实恒等／位移／转换列表和已证数值项桥推导agreement，正式端点没有未解agreement或程序值前提。

## 两个实际模式

| 模式 | 明确对象前提 | 目标项／承诺 |
|---|---|---|
| mode3替换 | Omega(w)、Num3(μ)、metadata(w,depth,L)、实际identityCode(w,a,I)、converted(true,w,I,R,a,a,c)、TermList(w,b,a,c,L) | Term(w,a,b,n)得到Fiber(w,μ,depth,L,a,c,n)；同前提无源项时得到Promise(w,μ,depth,L,a,b,a,c) |
| mode0弱化 | Omega(w)、Num0(μ)、metadata(w,depth,param)、实际identityCode(w,a,I)、shiftCode(w,b,B,J)、converted(true,w,I,R,a,a,B)、converted(false,w,J,S,b,a,B) | Term(w,a,b,n)得到Fiber(w,μ,depth,param,a,B,n)；同前提无源项时得到Promise(w,μ,depth,param,a,b,a,B) |

mode3使用相同原列表L；mode0参数允许任意内部自然值。所有环境守卫保留在闭句前件，没有声称这些环境的整体存在已由本批另行构造。

从实际程序Value取原Run₁反向桥、目标类型及自然性；对任意原运行候选v，用agreement正向桥构造其程序checked，再正式实例化既有程序唯一性得到v=q。Fiber传输消去程序实际存在见证并重新引入原Value见证。Promise通过对象allI／impI引入全部内部源项，不通过宿主有限输入枚举。

## 源码与验收

| 模块 | 对象成果 |
|---|---|
| OriginalNumericTermValueSyntax | agreement、全候选Unique、Value、Fiber、Promise及实例化／重命名／访问器 |
| OriginalNumericTermValueTransfer | 程序实际Value／Fiber到原Run₁的正式存在及唯一性传输 |
| OriginalNumericTermFiber | 两个模式实际agreement／Fiber／全内部Promise，环境前提精确保持 |
| ObjectOriginalNumericTermFiber | 10组闭句的源推导、原核传输及原nativeZF回放 |

10组闭句为replaceWholeTermAgreement、replaceActualOriginalTermFiber、replaceAllInternalTermPromise、weakenWholeTermAgreement、weakenActualOriginalTermFiber、weakenAllInternalTermPromise、originalTermValueTransfer、originalTermFiberTransfer、originalTermValueTargetType、originalTermAllCandidateUnique。

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalNumericTermFiber及C:/Python314/python.exe -X utf8 scripts/verify.py实际退出0。全仓1396构建任务、15336项审计（378无公理／14958记录允许依赖）、零警告。九命令及五trust=0入口全部退出0；Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增4模块65显式声明，10对新证书精确匹配既有依赖范围：核心标准三项，native标准三项加原七固定证书依赖。全仓1702对精确证书、12992项Internal显式声明覆盖；1260份工作区独立哈希无差异。七份锁文件、隔离Choice桥及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变。既有45项执行／分支直接oracle检查保留。本批Value／Promise是原执行结果的证明规格，不是新增独立执行器。

实际日志位于本地verification/commands.json、verification/audit.log及verification/term-fiber-readback.json；未运行OpenAI全仓构建／Comparator，未推送或创建PR。

## 下一门

在固定原模式、深度／参数、源／目标上下文及Promise下，对内部列表码n作对象成员归纳；属性对任意内部长度k量化。类型Cases给实际前驱长度和头尾类型，头Promise给实际头输出，尾码严格成员界使归纳假设给实际尾输出，实际Cons构造和原Run₂整体方程组装父输出。唯一性需处理任意候选的实际Nil／Cons分支、原Run输入等词替换及实际组件单射，不能只证明构造出的输出满足运行。

本批仅使原项实际唯一输出、全内部项Promise和实际环境下agreement消去三个细门为true。原Run₂全列表归纳、任意内部列表总性／唯一性及逐字段完整对应仍为false；全十一公式、quotation总桥、原规则兼容、ProofZF/U、解释和最终Con仍未完成。
