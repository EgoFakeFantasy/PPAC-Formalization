# Agent 友好工程流程
每行具有明确输入、产物、验收门。只允许一个 Lean/Lake 构建进程。
完成一行后更新状态与真实日志；未实现目标写在文档，不添加占位定理。
角色是职责划分，不要求并行启动 agent。

| 步骤 | 负责角色与输入 | 产物 | 验收门 | 状态 |
|---|---|---|---|---|
| 0 | 来源审查：OpenAI 244、账号仓库、原 PPAC | SOURCE_LOCK、FEASIBILITY、REPOSITORY_MAP、CLEANUP | 固定 SHA；两条路线分开；备份后清理 | 已完成 |
| 1 | 语言桥接：源语法，原生 ℒ、ZF、Derives | Migration/SourceSyntax、SourceStatements、Translation、Contract | 全8构造器真值保持；末/首 binder；原核接入；build、trust=0、审计 | 已完成 |
| 2 | 句法传输：步骤1、源 Derives | Renaming、Substitution、Derivation | rename/instantiate/generalize/equality 全规则；有限理论支撑；两向 bot 传输 | 待做 |
| 3 | 理论对应：步骤2、原 ZF/源 ZF | ZFEquivalence、ChoiceEquivalence | 全参数全公式 Replacement↔Collection、两种 AC；无新选择公理 | 待做 |
| 4 | 外部基线：原4.34.1环境 | 原 Comparator 复现、依赖闭包 | 两个 comparator 分开；精确公理；只定向编译；记录未验部分 | 待做 |
| 5 | 内部构造：原生集合构造、BMS可选工具 | Names、Pairs、Tuples、Recursion | 内部图与赋值；递归唯一性；覆盖非标准模型 | 待做 |
| 6 | 解释路线评审：论文相对化或元模型 | Background、Constructible（如采用） | 固定背景与 universe；逐实例 Derives；不加不可达 | 待做 |
| 7 | 强迫前端：源 Forcing | Atomic、Truth、Symmetry、ZF | 实际 poset/正规滤子/HS；全部ZF模式；无混合/支持缺口 | 待做 |
| 8 | 构造核心：Algebra+Construction | Monoid、Placement、ConservativeHull | 局部存在给实际构造和不变量；不以字段假定核心结论 | 待做 |
| 9 | 模型应用：Models全部文件 | SVC、ACwo、Quotient、NotAC | 全秩内部集合；商单射属于同一HS模型；非选择见证 | 待做 |
| 10 | 全局装配：步骤7–9 | PP、Consistency/Main | 空集分支；所有满射反单射；原核一致性传输 | 待做 |
| 11 | 终验与发布评审 | 量词/公理/依赖对照、全量验收 | 无缺口；精确命题；外部日志；发布单独范围 | 待做 |

每单元交接：输入固定提交、允许改动模块、目标完整 Lean 类型、依赖、
命令/退出码、剩余义务、禁止的强假设、下一步最小任务。


第一步验收已经完成：严格构建、trust=0 的 Check 与 Audit 均退出0；16个列举声明，
7个无公理依赖，9个依赖已记录的可信基，0警告。
这是第一步合同与语义桥的验收，不是全迁移或原OpenAI库的验收。
当前底座7个 native_decide 证书依赖见 TRUST_BASELINE.json；它们不是新增对象公理。
如后续要求只有标准逻辑公理的完整可信基，应先做独立底座证书修复批次再升级验收标签。
