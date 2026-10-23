# 原完整公式运行与统一对象归纳验收

基点：506f9082f5a4b4a54bbb7c292cf223de30723831。完成 S3.4c.2b.2c.3c.2c.2b.3f.2c.3a.2：原完整十一情形装配及统一对象归纳消去。

## 背景、对象语言与最终目标

使用 YesMetaZFC 原纯等词／成员语言、原 nativeZF 的完整 Separation／Collection 及原 FirstOrder.Derives。最终目标仍为 Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC。内部 Con 必须涵盖全部内部 ω 证明码、原六规则／27模式及完整公理模式，不能只涵盖外部标准码。

本批没有完成最终 Con，也未增加对象 AC、标准 ω、外部良基假设或新推导核。固定 Bool 索引 three 只区分原模式0／3；运行深度、上下文界、索引表、项像表、源根和输出均为对象变量。

## 已完成的实际对象证明

FormulaTransformBranchSelection.program_iff_selected 把真实完整程序经实际递归图传到原递归 Cases，再以原构造器筛选和分支引入得到已知源标签处的双条件。atomic_program_iff 证明在真实原子源守卫下四分支原子子程序与完整十一分支程序等价，没有把二者直接视为同一程序。

OriginalFullFormulaProgram.program_iff 使用 FormulaCodeRecursive.recursive_iff 的完整源分类，逐一消去原子、否定、四个二元连接词、全称和存在的实际源字段。所有见证保留在对象存在量词内。量词分支使用实际提升后的全参数归纳实例。

OriginalFormulaCorrectnessPoint.execution_iff_from_induction 在对象存在量词中取得实际递归图，并通过已验收的根执行方程得到原 Run₃ 与 executed 的双条件。correct_from_induction 对全部十一项参数执行原 allI，引入 frame 和源 FormulaCode 前提，建立对象归纳步。

OriginalFormulaCorrectnessInduction.progressive、all_correct 调用原 ZF 中已推导的 SetInduction.all_holds：分离使用具体 matrix 的否定，基础公理和传递覆盖也来自原 Source.ZF 推导。由此在对象理论内证明 ∀n correct(three,w,n)，没有使用宿主层良基归纳或把内部自然数当成标准数。

原核端点 ObjectOriginalFormulaCorrectness.native_allInternalWholeRunExecutedIff 的闭句内容为：

```text
Ω(w) → Frame(three,w,mode,depth,P,a,b,c,I,J,R,S) → FormulaCode(w,n,a,b) →
  (OriginalRun₃(w,mode,depth,opParam(three,P,S),n,q)
    ↔ executed(w,R,S,a,b,a,c,n,q)).
```

所有自由对象变量均经 close 全称闭合；frame 本身保留原模式、元数据、绑定恒等表及自由变量像转换合同。端点没有 allFramesIH、prefixIH、历史存在、模型或标准性前提。CheckStep4.lean 另外直接展开上述闭句，按其完整内容检查原核推导类型，避免只检查句子别名。

同时取得不带 IH 的完整程序对应、实际 history agreement 和实际 agreed history 存在性。九组闭句均有实际 Source.ZF 推导、TheoryTransport 核证书和 ZFReplay 原 nativeZF 重放。

## 实际验收

1512构建任务、16383项审计（385无公理／15998允许依赖）、零警告；九命令及五trust=0入口全部退出0；1376份独立哈希一致、1849对精确证书足迹、14039项Internal显式声明覆盖。

- 五个新模块62项声明全部显式进入 Audit。
- 九组新增核心证书仅有标准三项依赖；native 证书精确为标准三项加固定原七项依赖。
- 七份锁文件和 YesMetaZFC 提交039c8e132cc19671d73a3933c66b4799d2599dd6保持不变；上游工作树干净。
- 全仓 --wfail 构建和五个 --trust=0 入口实际退出0；额外展开的无IH运行合同在 CheckStep4 通过。
- 逐文件源码哈希、累计证书精确依赖与Internal显式声明覆盖均独立复核。
- 无新增 sorry／admit／占位公理；Choice桥保持隔离。

证据：verification/full-formula-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另复核本批Git原始字节，保留17份既存CRLF-only blob。

## 下一工程流程

| 顺序 | agent实现任务 | 具体交付与验收 |
|---|---|---|
| 1 | 核查原证明检查器模式3全部调用 | 列出六规则／27模式中每个实际操作位置；在对象推导中证明其输入满足frame自由变量像合同，或完整扩展正确性证明；不得缩小Proof码范围 |
| 2 | 原数值quotation与完整公式操作对应 | 对所有内部有类型输入与候选输出，证明固定原数码／树／公式关系和Run接口双向对应，处理任意嵌套量词 |
| 3 | Option及顶层实例化／抽象 | 实际成功／失败数值关系、作用域和空界边界；取得原对象推导合同 |
| 4 | 专用ProofZF／ProofU检查器 | 原六规则／27模式和完整Separation／Collection识别；全内部证明码正确性与证明变换 |
| 5 | 内部解释及一致性传输 | 由原nativeZF推导精确Con_ZF → Con_target；逐项核查背景、量词范围和附加假设 |

本批正确性范围是有效frame下的全部内部源公式码和全部候选输出。模式3自由变量像合同对最终检查器所有调用的适用性仍为false；本批不声称一般含绑定变量项像的捕获规避替换正确性。最终对象Con与相对一致性门仍为false，目标继续推进。
