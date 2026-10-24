# 原始外壳投影与全内部get递归验收

基点：b1315c9b81263096e757720606025f27ebdf73e1。单元3f.2c.3b.2d.2a，16模块188项显式声明、18组闭句。

## 对象语言与最终目标

使用原YesMetaZFC等词／成员语言、完整Separation／Collection的nativeZF及原FirstOrder.Derives。所有运行码、分量和索引均为内部集合；两个布尔只选择裸配数／后继节点及左／右分量的有限外部公式模式。

最终主句仍为：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

Con覆盖全部内部ω码、原六规则／27模式和完整公理模式。本批未证明主句，未增加对象选择或新核。

## 保留非规范外壳

上游ObjectCodeProjection先对input-1解配数得到tag／payload，再对payload解裸配数得到head／tail。原ObjectProjection.getHead／getTail忽略原始外层tag，不能用只识别规范Cons(tag1)的StructuralListProjection代替。

PairingProjectionSyntax.encoded(raw)分别使用原GodelPairSyntax.code或原StructuralNodeSyntax.raw。body与selected实际量化两个自然分量；step在有分解时返回选定分量，无分解时由对象否定存在分支返回空集。该全内部集合补值用于满足原自然递归算子的全域总单值前提，没有向对象ω内添加任意新默认行为。

PairingProjection证明全内部集合上的实际值存在、单值和自然值域，并给出真实编码分量构造律。PairingProjectionNatural进一步证明：

- 每个内部自然码都有裸配数分解，故裸配数的补值分支在ω内不会发生。
- 每个正内部自然码都有原始节点分解。
- 原始零码无正节点分解，两个分量均精确为零；对自然码无分解只可能为零。

所有存在见证来自原全内部解码定理，在对象EX中消去，不从宿主Prop选择数据。

## head／tail与任意原始标签

RawCodeProjectionSyntax.step先取得原始节点的右分量payload，再解payload的裸配数，取得所选左／右分量。RawCodeProjection证明实际全域总单值性、自然值域和零码双条件。对任意内部自然tag／p／a／b，已证：

```text
Ω(w) ∧ tag,p,a,b∈w ∧ Raw(w,tag,p,x) ∧ Pair(w,a,b,p) →
  [RawStep(head,w,x,y) ↔ y=(if head then a else b)].
```

tag没有被固定为1，也未预给规范列表或语法合法性。反向实际构造两层投影值；所有候选输出都由双条件覆盖。

## 实际自然递归与get

RawCodeProjectionRecursion从已证总性／单值性得到原对象递归图、每个内部自然索引的唯一末值、自然范围和逐步方程。RawCodeIterationTransport提供实际存在唯一及对象等词替换。

RawCodeShiftSyntax／Step／Induction／Shift在原Separation实例和对象ω归纳中证明两条真实轨迹的迭代移位，消去内部前驱末值见证。RawCodeIterationLaws提供实际零步值与后继推进。

RawCodeGetSyntax.get(w,x,i,y)是对象存在实际tail迭代末值，再对该末值取head。其定义仅使用原对象自然求值图及本批两层投影，未引用宿主ObjectCodeProjection.get、旧规范列表字段或宿主递归求值。

RawCodeGetValues对每个内部自然索引证明实际唯一自然值；种子x可为任意内部集合。最终纤维接口只要求Ω(w)与i∈w，没有正确性IH、历史参数或预设输入类型。

RawCodeGetLaws已证完整双向方程：

```text
Ω(w) ∧ Empty(i) → [Get(w,x,i,y) ↔ RawHead(w,x,y)]
Ω(w) ∧ r∈w ∧ Succ(s,r) ∧ RawTail(w,x,t) →
  [Get(w,x,s,y) ↔ Get(w,t,r,y)].
```

后继关系和tail值为真实对象关系，索引包含全部内部非标准自然数。这里完成的是索引为零的方程；输入码为零时任意索引输出零的统一归纳定理尚待下一批证明，二者未混淆。

## 实际验收

1619构建任务、17255项审计（393无公理／16862允许依赖）、零警告；九命令及五trust=0入口全部退出0；1454份独立哈希一致、1955对精确证书足迹、14911项Internal显式声明覆盖。

- scripts/verify.py退出0，全仓--wfail及五trust=0入口实际通过。
- 188项声明全部显式列入Audit；18组核心证书精确保持标准三项依赖，native证书精确继承固定七项上游语法证书依赖。
- 独立复核全部哈希与1955对证书足迹；核对任意原始标签合同没有规范标签前提，get唯一纤维没有种子合法性前提，移位证明实际使用原Separation与对象ω归纳。
- 定义守卫排除旧StructuralList投影、宿主ObjectCodeProjection／ObjectProjection、Expr.eval、宿主选择和类型预言机；接受定义没有使用比较规格。
- 七锁文件、YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6、既有纯十五规则及接受定义不变，上游工作树干净。新增代码无sorry／admit、占位公理或Type层数据选择。

证据：verification/raw-projection-readback.json、verification/summary.json、verification/commands.json、verification/build.log及verification/audit.log。提交后另复核Git原始字节，保留17份既存CRLF-only blob。生成器、日志和读回探针仅留本地。

## 未完成范围

下一步先完成输入零码的全内部索引get归纳及field组合，再定义原ObjectProjection七规则的独立纯轨迹，证明与完整tag／get／field数值语义全内部双条件。随后才能接入替换节点第2／3项投影及其完整有界赋值／head。

当前没有原七规则轨迹桥或原宿主Bool数值quotation的全内部等价证书；完整替换节点、六规则／27模式、ProofZF/U检查／编译、内部解释及最终Con门保持false。工程目标和全部内部ω量化未缩减。
