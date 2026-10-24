# 原 mode1 零深度参数列与实际首槽抽象映射验收

基点：bcb8b0160cefefcca4cf1726f179c8d996f948d3。单元3f.2c.3b.2d.6e；13模块89项显式声明、11组原核闭句。

## 背景、内部 Con 与最终目标

对象语言固定为单排序纯等词／成员语言，背景固定为原 YesMetaZFC 的完整 ZF，经 Project.fo_theory 进入原 FirstOrder.Derives。原 Separation／Collection 模式保留，不增加 AC 或 Con 假设。YesMetaZFC 固定提交为039c8e132cc19671d73a3933c66b4799d2599dd6。

内部 Con 仍按锁定规格定义为 `¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))`，ω由唯一最小归纳集的纯成员公式消去；Proof_T核验原六规则、27逻辑模式和完整ZF公理模式。它量化全部内部证明码，不限制外部标准ω。背景、编码和完整规格见[对象目标](OBJECT_TARGET.zh-CN.md)。该规格不等于专用检查器已实现。

最终要求仍为原核对象推导：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

本批完成零绑定深度的参数列实际映射。非零深度的绑定提升、完整mode1公式、forall节点、完整专用ProofZF/U及最终Con仍未证明。

## 证明链

1. SmallModeArgumentValueInduction／FieldInduction从原内部集合归纳、完整分离及正则公理推出真实列表性质。每个固定外部模式编号小于4；列表长度、索引、输入及输出码都是内部对象变量，未给列表长度外部上界。ValueConstruct、HeadTailFiber及OutputUnique完成真实有类型唯一输出；FieldPoint及FieldCompletion把原Run2与有类型逐字段原Run1关系双向对应。通用中间引理含明确的项Promise前提。
2. AbstractTopTermFiber使用此前已证的真实原Run1／独立项程序对应，以及程序的实际有类型唯一纤维，在对象理论中证明全部合法输入项的Promise。没有把这一Promise保留为最终假设。
3. AbstractTopArgumentFields在ALL3内部字段索引／输入／输出上，由真实源列表推出输入项类型，再调用实际码表下的项正确性，证明原字段关系与独立ArgumentProgramFieldSyntax.fields等价。结合已证列表归纳得到 `Run2 ↔ ArgumentProgramFieldSyntax.mapped`；列表IH及项Promise均被消去。
4. AbstractTopArgumentSyntax.abstracted定义为源列表类型与两个内部码表存在量词的合取。量词体恰为真实abstractCoded环境及独立逐字段程序映射，不引用原Run、原字段接受式或Promise作为接受预言机。
5. AbstractTopArgumentOperation从原码表存在性实际取得两表；正向构造抽象操作自身的EX，反向消去该操作给出的任意实际码表，并在它们上面证明对应。两方向都不要求外部选定码表、两对码表相等或预给比较程序一致性。
6. ObjectAbstractTopArguments逐模式关闭对象句子，经已验收源传输和ZFReplay，返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF []` 证书。

最终合同：

```text
Ω(w), Num1(mode), metadata(w,z,P), Empty(z), AbstractInput(w,a,b,A,B)
  ⊢ [TermList(w,k,a,B,n) ∧ Run2(w,mode,z,P,n,q)]
       ↔ ActualAbstractArguments(w,a,b,A,B,n,q,k).
```

AbstractInput包含原操作要求的内部长度与后继约束。输入列表类型位于结论内；最终前提没有R/S码表、归纳IH、逐项Promise、原轨迹、赋值、输出类型或一致性假设。比较目标本身也明确保留源列表类型：单独的逐字段像关系不保证源列表合法，不能删掉此守卫。

## 验收证据

1723构建任务、18521项审计（398无公理／18123允许依赖）、零警告；九命令及五trust=0入口全部退出0；1558份独立哈希一致、2132对精确证书足迹、16177项Internal显式声明覆盖。

脚本入口 `scripts/verify.py`；独立复核 `verification/abstract-top-arguments-readback.json`；逐命令结果 `verification/commands.json`。独立复核核查所有新声明覆盖、每一组原核及native精确依赖、原接受AST与码表／项程序定义Git字节不变、最终前提集合、内部归纳调用和真实两码表EX构造／消去。

旧任意raw投影单元禁止canonical-list辅助设施的检查继续保留；本批比较的是实际有类型码表／参数列表，明确仅允许SmallModeArgumentFieldPoint及AbstractTopArgumentFields引用StructuralListFieldSyntax.field／field_rename。新抽象操作定义仍独立禁止原Run／原字段／Promise等接受预言机。这是检查适用范围的明确划分，没有放宽旧raw投影规格。

## 下一阶段与验收门

| 单元 | 实现动作 | 原核对象验收合同 | 状态 |
|---|---|---|---|
| 零深度参数列 | 内部列表归纳、项Promise证明、实际逐字段对应、EX消去 | 上述带源守卫的Run2双条件 | 本批完成 |
| mode1抽象frame | 用任意内部深度的变量关系定义兼容frame，根环境推出兼容性；真实binder提升保持兼容 | 原核Derives，不能把兼容性或子步骤当作最终Promise | 下一步 |
| 全11公式 | 统一内部参数归纳，实际历史、原量词深度递增及环境提升 | 任意内部合法公式的完整原Run正确性 | 未完成 |
| forall节点 | 原node9嵌套头、四查询、四赋值界及真实mode1变换 | 完整原节点双条件，消去实际见证 | 未完成 |
| logical／theory | 原27模式、完整ZF／U公理判断、quotation／Bool对应 | 任意内部码的检查关系正确性 | 未完成 |
| Proof／内部解释／Con | 内部证明码编译、解释与完整目标理论证明 | 原nativeZF中Con_ZF→Con_target | 未证明 |

不能将零深度Top环境重新生成后直接当作量词下的提升环境；必须证明深度与实际绑定像表的对应。所有表格中的“完成”仅指本批合同，最终相对一致性目标保持未证明。
