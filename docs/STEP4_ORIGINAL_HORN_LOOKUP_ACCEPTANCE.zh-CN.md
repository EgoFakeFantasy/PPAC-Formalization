# 原Horn表达式与查找局部矩阵验收

2026-10-23；S3.4c.2b.2c.3c.1b.2a；基点dc3b1dce43c44fe1b367787a62032f2bdcfc2add。

本批直接使用固定底座的ObjectHorn.Expr、ObjectHorn.Rule以及ObjectSyntaxTransform.lookupHead／lookupTail。14模块141显式声明、17组新闭句，先在Source.Derives内证明，再经TheoryTransport与ZFReplay回放到原FirstOrder.Derives nativeZF []。对象语言为纯成员／等词，背景为原nativeZF完整Collection。

最终目标仍为Con_ZF → Con_(ZF+PP+ACwo+¬AC)。Con的全部内部ω证明码、原六规则／27模式及完整Separation/Collection保持不变；本批不通过最终Con总门。

## 原表达式的关系式编译

HornExprSyntax.graph直接递归匹配上游原Expr的literal／var／succ／pair，不另造一份表达式AST，不调用Expr.eval、宿主SyntaxTransform.lookup、已验收的全查找判断充当执行原语。数值常量用原numeral，变量显式自然守卫加等词，后继与配数实际绑定子值并调用已证明的原内部算术图。

对每个固定上游表达式e及有限arity，环境的每个值都是任意内部对象；其自然守卫是有限对象合取。原ZF证明：

```text
Omega(w), EnvNat(w,env) ⊢ ∃y (y∈w ∧ Graph(e,w,env,y))
Omega(w), EnvNat(w,env), Graph(e,w,env,y)
  ⊢ y∈w ∧ ∀z (Graph(e,w,env,z) → z=y)
  ⊢ Graph(e,w,env,z) ↔ z=y.
```

实际存在性使用原Pairing／Union、自然数后继及原Gödel配数；唯一性逐层对齐所有隐藏子值。没有从Lean Prop中抽取Type层的运行值，也没有外部自然数标准性假设。外部固定表达式仅索引一个对象定理模式；这不声称解释任意内部表达式码。

## 与原数值结构精确对应

HornExprStructural、HornExprForest及HornExprConstructor证明原raw节点、Nil／Cons、Expr.list、Expr.node与原精确字段构造器对应；每个内部候选码都在双条件范围内。原列表／节点的实际构造见证用于取得表达式值，求值单值性再对齐任意候选，不以外部树或测试表替代。

OriginalLookupExpr.actual_head_expression／actual_tail_expression／actual_tail_premises以核可检查的等式确认，所使用表达式及前提正是固定上游lookupHead和lookupTail的字段。内部推导给出：

```text
Cons(h,t,n), Empty(z), Env2(h,t)
  ⊢ Graph(lookupHead.head, row) ↔ Constructor(3,0,[n,z,h],row)
Cons(h,t,n), Successor(s,j), Env4(h,t,j,y)
  ⊢ Graph(lookupTail.head, row) ↔ Constructor(3,0,[n,s,y],row)
Env4(h,t,j,y)
  ⊢ Graph(actualTailPremise, child) ↔ Constructor(3,0,[t,j,y],child).
```

这保留原Cons外壳与未访问尾部行为，不额外要求整个尾表有效。

## 原局部矩阵及赋值界

HornRuleSyntax.matrix直接读取原Rule.head／guards／premises，用表达式求值图消去函数项；前提是实际求值行属于轨迹，守卫是两个实际值的成员关系。HornRuleValue证明每个固定真实前提及比较守卫在内部实际值处精确。

OriginalLookupRuleMatrix把两个原规则的关系式局部矩阵分别化为头行Constructor，以及头行Constructor与实际子行属于轨迹的合取。没有省略tail的轨迹前提，也没有把原规则表替换成新的证明核。

HornExprBounds.variable_bound对固定原表达式中每个出现变量，证明其内部值≤实际结果。原lookupHead、lookupTail的所有变量都出现，因此实际取得完整对象合取EnvBound，满足上游有界赋值搜索所需的界。常数／变量／后继／配数的界均由原内部自然序和配数界推导；没有用宿主Nat.variable_le替代。

## 实际验收

1289构建任务、14084项审计（366无公理／13718允许依赖）、零警告；九命令及五trust=0入口全部退出0；1153份工作区独立哈希一致、1528对精确证书足迹、11740项Internal显式声明覆盖。新增17对证书严格等于std3核心／std3加原七证书依赖；Choice桥仍隔离审计。七锁与固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变，依赖工作区干净。新编译核心两个模块有直接宿主／旧查找引用禁用检查，保留此前全部核心检查。

实际执行LEAN_NUM_THREADS=1、lake --wfail build PPAC.Migration.Internal.ObjectOriginalLookupRules，随后C:/Python314/python.exe -X utf8 scripts/verify.py。九条命令见本地verification/commands.json；独立复核见本地verification/horn-lookup-readback.json。没有运行OpenAI原仓完整构建或Comparator。

## 仍需闭合的原接口

本批证明的是直接编译原AST得到的纯关系式局部矩阵；还没有证明原扩展语言Rule.matrix的完整函数消去翻译、量化规则应用与整个ObjectTrace.condition的对应，也没有完成原完整规则表的lookup分派及严格失败分支。因此原数字接口／轨迹总门保持false。不能把局部矩阵、宿主checked_iff或前一批固定描述码当作完整数字接口已完成。

下一步3c.1b.2b：原规则有界赋值量化、全表分派与任意内部ω子集轨迹的可靠性／完备性，再与按表码递归的已验收程序双向对应。原条件允许任意ω子集轨迹，不能仅检查宿主生成的有限运行；可靠性须用实际tail∈table的对象归纳排除循环。

随后仍为模式0／3变量与十一公式、原规则5／4兼容、专用ProofZF/U、全内部检查／编译、完整L／对称扩张内部解释及最终Con，不附加FreeClosed、模型标准性或选择前提。
