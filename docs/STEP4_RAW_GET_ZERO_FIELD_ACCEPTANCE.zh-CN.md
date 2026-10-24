# 输入零码全索引get、原field组合及构造槽位验收

基点：1b493ab8ea9954113167a7d79ac09217c31a8816。单元3f.2c.3b.2d.2b，7模块91项显式声明、13组闭句。

## 对象背景与最终目标

固定原YesMetaZFC等词／成员语言、完整Separation／Collection背景nativeZF及原FirstOrder.Derives。运行值、递归索引和所有候选输出均为内部集合，ω不假定外部标准。

最终对象主句仍为：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con仍覆盖全部内部ω证明码与原六规则／27模式。本批不证明主句，不增加对象选择或新推导核。

## 输入零码的全部内部索引

RawCodeGetZeroSyntax.correct(w,z,i)为实际对象句式：

```text
∀y (Get(w,z,i,y) → Empty(y)).
```

RawCodeGetZero.correct_zero使用原get零索引方程及head零码行为。correct_successor构造实际Tail(z,z)，将后继索引读值退回前驱，并实例化同一对象correct公式。

base／step／all_correct使用原Separation实例和OmegaInduction.induction_on_omega消去归纳前提；all_indices显式得到对象∀i∈ω∀y统一性质。at_index和sound在实际内部候选上实例化；checked_iff的反向使用已证实际get值存在及原Extensionality对齐两个空集，实际消去值见证。

最终合同为：

```text
Ω(w) → Empty(z) → i∈w → [Get(w,z,i,y) ↔ Empty(y)].
```

没有正确性IH、标准索引或候选输出自然性前提。这是输入零码的全部索引定理，覆盖非标准内部自然索引；并非仅复用“索引为零”实例。

## 原field为payload之后的get

RawCodeFieldSyntax.field(w,x,i,y)定义为对象EX载荷p，要求原始节点右分量投影Payload(w,x,p)及Get(w,p,i,y)。它不调用旧规范列表字段、宿主ObjectCodeProjection／ObjectProjection或类型规格。

RawCodeField证明：

- 每个内部自然索引实际存在唯一自然输出；根x可为任意内部集合，最终唯一纤维只有Ω与索引自然性前提。
- 在实际payload投影处，Field(w,x,i,y)与Get(w,p,i,y)对象双向等价，所有载荷见证已消去。
- 对任意内部自然tag／p及实际Raw(w,tag,p,x)，保留相同field／get双条件，不要求规范标签。
- 输入零码时，全部内部自然索引的field与Empty(y)精确等价。

所有唯一性比较都使用实际两条投影／get图，并在对象等词规则中对齐中间载荷，不抽取宿主函数或选择数据。

## 实际有限原构造器槽位

RawCodeProjectionCanonical只在给定实际Cons／ConsAt条件下证明原始head／tail等于该Cons的分量。该文件只提供条件式推导，没有把任意非规范输入的投影定义改成规范列表投影。

RawCodeFieldAtConstructor.forest_at对外部有限字段数和合法槽位归纳，使用实际原森林、内部槽位数码、原get零／后继方程取得准确值。node_at和constructor_at消去实际tag／payload／森林见证，得到：

```text
Ω(w) → Constructor(k,tag,w,xs,n) → Num(j.val,i) →
  [Field(w,n,i,y) ↔ y=xs(j)].
```

k、tag及j是外部有限定理模式索引；候选码、字段值、索引数码和输出均在对象层量化。每个实例都返回原核证书；未把该模式误称为内部任意arity的统一真值断言。原证明节点的有限字段位置可使用此接口，完整投影查询仍待后续轨迹桥。

## 实际验收

1626构建任务、17346项审计（393无公理／16953允许依赖）、零警告；九命令及五trust=0入口全部退出0；1461份独立哈希一致、1968对精确证书足迹、15002项Internal显式声明覆盖。

- scripts/verify.py退出0，全仓--wfail与五trust=0入口实际通过。
- 91项新增声明全列入Audit；13组核心证书精确保持标准三项依赖，native证书精确继承固定七项上游语法证书依赖。
- 独立复核全部哈希及1968对证书足迹；核对统一内部零码归纳实际使用原Separation、最终get零码接口不保留IH、field唯一纤维无输入规范性前提，以及有限槽位模式的真实构造器／数码守卫。
- field定义守卫排除旧规范字段、宿主检查器／求值、类型规格及归纳性质预言机；条件式规范桥没有进入field接受定义。
- 七锁文件、YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6、既有纯十五规则及接受定义均不变，上游工作树干净；新增代码无sorry／admit、占位公理或Type层数据选择。

证据：verification/raw-field-readback.json、verification/summary.json、verification/commands.json、verification/build.log及verification/audit.log。提交后另复核Git原始字节，保留17份既存CRLF-only blob。读回脚本、生成探针及日志留本地。

## 下一步与输入域边界

下一单元定义并证明原ObjectProjection七规则的独立纯闭轨迹，与完整tag／get／field数值关系在全部内部自然码上对应。当前数值关系为原递归需要在ω外有总化补值，但编码行本身要求自然元数据。因此全候选轨迹双条件必须显式保留输入／索引属于ω的守卫，不能无条件把其与ω外也总化的数值关系等同。

原七规则轨迹桥、原数值quotation／Bool／Option接口、替换节点第2／3项投影及完整节点head／赋值界、六规则／27模式、ProofZF/U检查／编译、完整内部解释和最终Con仍未完成；相关门禁保持false。
