# PPAC 向 YesMetaZFC 迁移
[English](README.md)

本分支已完成第一步语言桥、第二步正向句法传输，以及第三步中的反向语法/原核规范化呈现。
第二步覆盖19条源规则，直接给出原FirstOrder.Derives，不经过完备性或模型语义；
闭句源证明可带任意有限变量环境，输出仍为空free上下文。原核证书的有限公理支撑已证明。

最终目标固定为对象ZF中的 Derives B [] (Con_ZF → Con_target)，
参见[内部Con及背景规格](docs/OBJECT_TARGET.zh-CN.md)。
内部ZF/U检查器完整AST、任意内部码正确性与对象主句尚未实现。
第三步已完成七条固定公理的双向原核推导，以及任意参数、任意矩阵的全部源分离模式在原ZF中的推导。
分离模式已覆盖两个方向的全部参数和矩阵，包括任意原生Project矩阵的反向回放。
原Collection加分离已实质推出任意源Replacement实例，并取得原核Derives。
源ZF与源目标理论的全部证明现在可正向回放到真正的原生ZF/目标理论。
源Replacement到Collection的反向数学方向、两种AC及反向演绎编译仍待完成。
Presentation中的双向回放两端都是原Derives，不能将它读成完整反向编译。
详见[Replacement及全正向回放验收](docs/STEP3_REPLACEMENT_FORWARD_ACCEPTANCE.zh-CN.md)及[先前阶段验收](docs/STEP3_ACCEPTANCE.zh-CN.md)。

第一步中的目标理论公理推导只检查连线，不表示 ZF 已证明 PP，也不表示目标理论一致。
默认 import PPAC 只导入迁移主线；旧宿主辅助单独 import PPAC.Auxiliary。
旧宿主 PP 不当作对象 PP，旧研究候选与旧验收已移出活动主线。
清理之前保留了完整 Git bundle 和源码备份，未删除 Git 历史。

运行 python scripts/verify.py；Lean 4.33.1，唯一依赖为固定提交的 YesMetaZFC。
脚本串行构建、trust=0 检查、公理与缺口扫描，记录真实退出码和文件哈希。
verification/ 是本地生成结果，不作为远端验收或自动发布材料。

阅读：
- [可行性与完整边界](docs/FEASIBILITY.zh-CN.md)
- [名下13仓库的用途评估](docs/REPOSITORY_MAP.zh-CN.md)
- [工程流程与逐步验收门](docs/AGENT_WORKFLOW.zh-CN.md)
- [清理决定](docs/CLEANUP.zh-CN.md)
- [当前缺口](GAPS.md)


公理审计边界：固定 YesMetaZFC 的 sentence! 宏用 native_decide 生成7个基础句子的 FreeClosed 证书，原生ZF合同继承其7个 native_decide.ax_1 依赖。见 docs/TRUST_BASELINE.json。当前检查精确守住此基线，不标成“仅三项标准公理”；未修改底座，也未添加新的自定义公理。后续若要求纯内核证书，需另行把这些证书改为 kernel-checked decide 并核对原理论不变。
