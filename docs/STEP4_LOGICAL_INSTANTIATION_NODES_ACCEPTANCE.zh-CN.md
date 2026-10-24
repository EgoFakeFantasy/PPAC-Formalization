# 原逻辑20／23／25完整纯关系节点验收（2026-10-24）

本批将已验收的真实 mode2 InstantiateTop 接入原逻辑公理20、23、25的准确查询，完成全部赋值搜索界与嵌套数值头规范化；15组闭句已经返回 YesMetaZFC 原 FirstOrder.Derives。覆盖内部候选赋值，不要求它们来自宿主标准码。共享原quotation／Bool、其余逻辑／理论节点、专用Proof、内部编译／解释与最终Con仍未证明。

## 对象背景与最终目标

对象语言为纯等号／成员语言；背景是原 nativeZF，保留完整 Separation／Collection，不加入对象 Choice。最终目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

专用Proof_T必须覆盖原六规则／27逻辑模式、完整理论模式及全部内部ω证明码。当前纯关系节点双条件是后续checker正确性的组成部分；既不等于原宿主Bool检查器的报价对应，也不等于最终相对一致性证明。

## 精确节点与推导链

| 原模式 | arity | 原有序查询 | 数值头的内部中间码 |
|---|---|---|---|
| 20 | 4 | Formula(bound=1,free=v0,input=v1)、Term(bound=0,free=v0,input=v2)、transform2(v2,v1,v3) | 3个：标签20、9、7；根标签0 |
| 23 | 4 | 与20逐项相同 | 3个：标签23、10、7；根标签0 |
| 25 | 6 | Term(0,v0,v1)、Term(0,v0,v2)、Formula(1,v0,v3)、transform2(v1,v3,v4)、transform2(v2,v3,v5) | 4个：标签25、3、7、7；根标签0 |

LogicalInstantiateQueries从原grammar／transform表达式取得查询，采用真实模式数值2。Num2见证由原对象数码存在性构造，在对象EX内消去。Formula的界1由empty的实际后继表示，Term的绑定界为0。实际参数项类型与后继条件提供既有InstantiateTop入口，因此不假设变换结果或其正确性。

LogicalInstantiateSyntax保持接受bundle只含实际PureSyntaxExprQuery／OriginalTransformExprQuery，另定义独立数学规格。LogicalInstantiateAllQueries分别证明20／23的三查询与25的五查询双条件；25分别处理两个参数项。后继见证由对象Pairing／Union构造并消去，最终查询接口只有Ω、赋值自然性和empty前提。

三个LogicalRule*Head模块按实际嵌套树逐节点展开为SyntaxNodeSyntax.constructor数值关系，构造并消去全部内部子节点码；normalized规格不再借助Expr.graph作头部正确性前提。原头、arity及有序查询Bool标签均有rfl证书，实际头的所有变量覆盖经原变量界定理推出全部4／6个搜索界，无需前驱证明有效性或额外边界假设。

LogicalInstantiateNode以对象existsMany处理完整4／6赋值块。完整规范化端点是：

```text
Ω(w), empty(z) ⊢ node4(u,w,row) ↔ normalized4(u,w,z,row)
Ω(w), empty(z) ⊢ node6(w,row)   ↔ normalized6(w,z,row)
```

u=true选择原20，u=false选择原23，是外部有限定理模式索引。所有实际赋值、Num2、后继与数值头子码均位于对象量词内；最终没有赋值自然性、类型、搜索界、头部形状、码表、历史、IH、Promise、模型或Proof前提。数学规格仍明确检查所需类型，未声称原变换在任意非法输入上自动拒绝。

ObjectLogicalInstantiate提供15组源／core／native闭句，沿既有TheoryTransport.sentence、ZFReplay.replay传输到原推导核。CheckStep4同时保留生成闭句与展开后的完整规范化端点。既有PPAC证明和所有原接受／程序／类型AST保持Git字节不变；仅4个集成文件、9个新增模块及本批说明变更。

## 实际验收

| 验收项 | 实测结果 |
|---|---|
| 新模块／显式声明／原核闭句 | 9／225／15组 |
| 定向native模块构建 | 1529项，通过、零警告 |
| 全仓构建 | 1824项，通过 |
| 声明审计 | 19606：405无公理、19201允许依赖；0警告 |
| 验收命令 | 9条退出0，含5个trust=0入口 |
| 工作区独立SHA256 | 1659份一致 |
| 全部core/native精确足迹 | 2268对一致 |
| Internal显式声明覆盖 | 17262项 |
| 上游及锁定基线 | 原pin039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

新core证书依赖恰为propext、Classical.choice、Quot.sound；native另含上游既有七项锁定证书依赖。未扩展对象理论或信任基线，审计例外仅逐个列举本批15个native声明，未采用命名空间通配放行。

证据为verification/logical-instantiation-readback.json、summary.json、commands.json与.local/logical-instantiation-full-verify.log；定向成功日志为.local/logical-instantiation-native-directed.log。复验命令：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点bdad5c1c385fd0ba098fa9a2c471907f79f48052，提交后accepted_commit由独立Git字节回读写入本地验收JSON。

## 清理及后续工程

本次清理前实测C盘空余103999909888字节，删除一份已被成功日志替代的失败调试日志1940字节；盘面实测仅增加4096字节，不将逻辑删除字节当作空间增长。未发现失效工作区编译进程。生成／回读脚本、正式证明、验收证据与Lean缓存仍有用途，均保留；此前247份临时垃圾清理有独立收据。本批清理收据为.local/workspace-cleanup-logical-instantiation-result.json。清理确认后已恢复串行全仓编译，无其他项目或应用清理。

| 顺序 | 可执行工作单元 | 必须验收的对象端点 |
|---|---|---|
| 1，下一步 | 原0–19命题模式、21／22／24量词模式及26等式反身性 | 每个原arity／头／有序查询／全部赋值界准确，完整纯关系节点与独立数学规格双条件；量词模式复用真实mode1操作 |
| 2 | 共享原quotation／Bool桥 | 核对纯EqMem语言、参数及上下文，实际语法／操作与原共享checker对应；不限制为外部标准码或有限重放 |
| 3 | ZF/U理论节点与专用内部Proof | 完整Separation／Collection、原六规则／27逻辑模式、全部内部ω；接受式不得包含要证结论 |
| 4 | 内部证书编译与数学解释 | 检查／编译正确性、源推导传输，目标ZF、PP、ACwo、¬AC的实际内部解释 |
| 5 | 最终内部Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，仍未证明 |

不复用已退役反射代码，不以Lean宿主Consistent、任意模型语义或本次构建成功替代最后一步。Agent广场服务此前连接失败，本批状态与经验仅在API成功回执后才算写入。
