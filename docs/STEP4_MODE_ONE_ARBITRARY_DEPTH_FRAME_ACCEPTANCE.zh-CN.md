# 原 mode1 任意内部深度的兼容 frame 与实际绑定提升验收

基点：b98295f1db13cab9f6540d2d0dc36d963c1d702b。单元3f.2c.3b.2d.6f；12模块89项显式声明、13组原核闭句。

## 背景和最终目标

对象签名仍为原纯等词／成员语言，背景为原YesMetaZFC完整ZF经Project.fo_theory的像，推导关系为原FirstOrder.Derives。固定上游提交039c8e132cc19671d73a3933c66b4799d2599dd6及七份锁定文件保持不变；不增加AC、不可达或一致性前提。

内部Con规格仍是 `¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))`。ω由唯一最小归纳集公式消去，Proof_T核验原六规则／27逻辑模式、完整Separation／Collection及目标公理。量化覆盖全部内部ω，不限制外部标准证明码。完整规格及尚未实现的专用检查器边界见[对象目标](OBJECT_TARGET.zh-CN.md)。

最终目标未证明：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批完成任意内部深度的变量数值协变、实际根frame和原完整码表绑定提升的frame闭包。任意深度项／参数列与原运行的完整对应、全11公式、forall节点、专用ProofZF/U、内部解释和最终Con仍待完成。

## 独立兼容 frame

AbstractOperationFrameSyntax.frame包含四项：Num1模式、原自然深度／参数metadata、真实有类型的两张项像码表，以及bound／free两类变量的兼容性。每类兼容性用三个内部全称量词表达：

```text
∀i n q,
  [i∈sourceLimit ∧ VariableCode(kind,w,i,n)] →
    [NumericMode1Value(kind,w,depth,i,n,q) ↔ Field(selectedTable,i,q)].
```

NumericMode1Value是此前独立定义的成员／后继／变量码关系，不引用原运行、历史、列表归纳结论或待证公式程序作为预言机。源／目标绑定界可不同，depth独立于上下文长度；所有深度、索引、项码、码表及候选输出都是内部对象变量。

AbstractOperationFrameRoot.from_actual从真实零深度AbstractFreeTop环境推出根frame。根兼容性实际调用已证全部内部索引／候选上的码表数值对应，不额外假定两表与数值操作一致。

## 实际绑定提升的证明链

1. AbstractBoundOrder证明一般深度外移位分支的精确输出、内部后继阈值双条件，以及阈值和索引同时后继时的移位律。使用原自然序数成员关系、后继唯一性及提升顺序引理，不假设内部自然数外部标准。
2. SyntaxRenameTermAtIndex在真实完整索引图边上证明全部候选输出的重命名双条件。内部源／目标索引EX经解码单射性和图单值性消去；允许非单射索引图，不假定宿主映射。
3. AbstractBinderRename接原bound后继图与free恒等图，得到真实目标项重命名的精确变量码律。AbstractBinderVariablePoint及AbstractBinderVariable合成四个原变量分支：深度内bound保持、深度外bound移位、free0映到当前深度、free后继映到前驱自由变量。旧值中的后继／前驱见证实际在对象EX中消去。
4. AbstractFrameLiftPoint调用原SyntaxCodedMixedBinderFields.zero_iff／bound_iff／free_iff，比较真实新bound0、旧bound后继槽及原free槽。旧字段值通过源frame取得数值性质，通过真实列表类型取得目标项类型。
5. AbstractFrameLiftValues在原核中构造并消去旧变量码及旧字段值；AbstractFrameLiftCompatibility用原Separation和内部ω零／后继分解覆盖全部新bound索引，并用三个内部全称量词合成两类新兼容性。目标列表类型来自原实际提升关系。
6. AbstractOperationFrameBinder.lifted打开原数值提升关系的四个图见证，再打开原图提升关系的四个图／头见证，在它们上面证明新frame，随后全部消去。没有把新生成Top环境当作提升环境。
7. ObjectAbstractOperationFrame的13组闭句经原源传输及ZFReplay，返回原nativeZF内核Derives证书。

最终闭包合同：

```text
Ω(w), Frame(w,mode,depth,P,a,b,c,e,R,S), Succ(D,depth),
ActualCodedBinderLift(w,R,S,a,b,c,e,A,C,K,H)
  ⊢ Frame(w,mode,D,P,A,b,C,e,K,H).
```

这里R/S与K/H是合同中被给定实际提升关联的输入／输出码表参数。最终前提没有额外U/V重命名图、空集／新头部码、旧变量码／字段值、兼容性IH、逐项Promise或模型／一致性假设。前置frame的根实例及提升保持性均已证明，不把“任意深度的所有运行正确”写进frame定义。

## 实际验收

1735构建任务、18610项声明审计（399无公理／18211允许依赖）、零警告；九条命令及五个trust=0入口全部退出0；1570份工作文件独立哈希一致、2145对精确核／native证书足迹、16266项Internal显式声明覆盖。

证据：`verification/abstract-frame-readback.json`、`verification/commands.json`及`scripts/verify.py`。独立复核除全声明审计外，还核查每组核证书恰为三项标准依赖、native证书恰为同三项加既有七项固定依赖；原binder、数值关系、码表定义及旧mode0／3 frame／公式归纳的Git字节均未改变。

复核还展开最终native合同，检查四个对象前提、两次原eliminate_4、三个旧码／字段EX消去、真实Separation／内部ω分解、四数值分支，以及根兼容性调用。新frame定义独立禁止Run／Horn／原字段接受式／Promise／项程序预言机。原raw投影单元的独立性检查仍保持；有类型码表比较模块只开放明确需要的field／field_rename及旧字段实际存在性接口。

## 后续工程表

| 单元 | 实现动作 | 原核对象验收合同 | 状态 |
|---|---|---|---|
| 任意深度变量协变 | 四分支与实际bound后继／free恒等图对应 | 全内部候选输出双条件 | 本批完成 |
| 实际根frame与binder闭包 | 根码表兼容、实际提升三字段律、全部EX消去 | 上述原核frame闭包 | 本批完成 |
| 任意深度项／参数列 | 从frame取变量对应，接原Run1及小模式Run2归纳，实际推出Promise | frame下原运行与实际码表程序双条件 | 下一步 |
| 全11公式 | 对全部内部参数和兼容frame作统一对象归纳，接实际历史及binder闭包 | 全内部合法公式原mode1运行正确性 | 未完成 |
| forall节点 | 原嵌套node9头、四查询、四赋值界和完整公式变换 | 原完整纯关系节点双条件 | 未完成 |
| logical／theory／Proof／Con | 27模式、完整ZF/U、quotation／Bool、内部编译及解释 | 原nativeZF中Con_ZF→Con_target | 未证明 |

验收范围未缩小最终目标；本批闭包不替代任意深度项／公式归纳，也不替代内部Con推导。
