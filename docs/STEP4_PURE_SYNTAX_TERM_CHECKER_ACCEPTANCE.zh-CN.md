# 纯成员十五规则与全内部项查询验收

基点：0d4b01ddc9343a77ccabbc34a6e679b6314b32c4。完成3f.2c.3b.2a；新增8模块87项显式声明、8组原核闭句。

## 背景与最终目标

对象语言固定为原YesMetaZFC等词／成员语言；背景nativeZF使用完整Separation／Collection；推导关系为原FirstOrder.Derives。最终仍要求：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con量化全部内部ω证明码，保留原六规则／27模式。本批未证明该主句，未加入对象AC、标准ω或外部良基前提。

## 本批对象证明

PureSyntaxRules保留原两种变量规则、nil／cons参数列及全部十一种纯公式构造，共十五条。关系原子只采用membership；不加入扩展函数应用。CheckStep4逐字展开规则表，以rfl核对。

PureSyntaxTrace分别定义kind0项、kind1参数列、kind4公式的实际Horn行及闭轨迹：存在内部R⊆ω，含根行，且每个成员满足该十五规则的HornStep。定义不引用Term／TermList／FormulaCode类型结论、旧变换检查器或宿主Expr.eval。参数列和公式的AST存在不代表其正确性已证明。

HornNodeFields在对象层恢复实际三／四字段的表达式图。PureSyntaxVariableExpr连接真实变量表达式图和内部编码；PureSyntaxTermMatrix从原有界规则应用恢复元数据、编码与作用域守卫，并以首标签不交排除其他十三规则。

PureSyntaxTermCorrectness.checked_iff得到：

```text
Ω(w) → (PureSyntaxTrace.term(w,b,f,n) ↔ SyntaxTermSyntax.term(w,b,f,n)).
```

b、f、n均为任意内部集合候选；除Ω外没有预给自然性、类型、轨迹、宿主函数或IH。健全方向从真实闭轨迹恢复纯Term；完备方向在对象存在量词内构造实际编码行及单元素闭轨迹，再消去见证。空绑定界进一步推出实际输入落在自由变量分支。

ObjectPureSyntaxTermChecker提供八组Sentence／source／kernel_certificate／native证书，沿既有TheoryTransport和ZFReplay返回原nativeZF。CheckStep4还直接展开Ω→项查询双条件的全称闭句，避免仅核对Sentence别名。

## 实际验收

1526构建任务、16523项审计（386无公理／16137允许依赖）、零警告；九命令及五trust=0入口全部退出0；1388份独立哈希一致、1866对精确证书足迹、14179项Internal显式声明覆盖。

- scripts/verify.py退出0；全仓--wfail及五个--trust=0入口通过。
- 八组新增kernel证书精确保持三项标准依赖；native证书精确继承固定七项上游证书依赖，不误称纯三项基线。
- 新增87项声明显式纳入Audit；独立复核确认检查关系不借用待证类型结论。
- 七锁文件、YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及上游干净状态保持不变。
- 无新增sorry／admit或占位公理；Choice桥保持隔离。
- 首轮完整验收发现CheckStep4的Rule缺少命名空间限定；改为原ObjectHorn.Rule后重跑。以上数值来自成功运行。

证据：verification/pure-term-readback.json、verification/summary.json、verification/commands.json、verification/build.log和verification/audit.log。提交后另外核对源码哈希与Git字节，保留17份既存CRLF-only blob。

## 后续工程流程

| 顺序 | 实现任务 | 对象验收条件 | 状态 |
|---|---|---|---|
| 1 | 专用十五规则与项查询 | Ω下所有内部候选的kind0查询↔纯Term；实际闭轨迹存在 | 完成 |
| 2 | 参数列nil／cons及轨迹合并 | kind1查询↔纯TermList；内部长度和元素，消去IH／预给轨迹 | 待证明 |
| 3 | 全部十一公式构造 | kind4查询↔FormulaCode；对象归纳处理绑定界后继 | 待证明 |
| 4 | 原substitutionShape桥 | 实际纯查询推出空绑定界项列表守卫，接现有mode3 | 待证明 |
| 5 | 原数值quotation、Option、mode0／1／2／3 | 全内部输入输出的成功失败及顶层抽象实例化 | 待证明 |
| 6 | 专用ProofZF／ProofU | 六规则／27模式、完整公理模式、任意内部证明码 | 待证明 |
| 7 | 内部解释与Con传输 | 原nativeZF中Derives [] (Con_ZF→Con_target) | 待证明 |

参数列／公式／完整类型查询桥、最终检查器适用性和Con验收门保持false；总体目标保持active。
