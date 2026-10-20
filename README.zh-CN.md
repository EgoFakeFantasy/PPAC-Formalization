# PPAC 向 YesMetaZFC 迁移
[English](README.md)

本分支实现第一步：原始有限变量语法 → YesMetaZFC 原生纯集合论语法的翻译，
证明任意关系结构上的全公式真值保持，并固定原 ZF、PP、ACwo、¬AC 与原 Derives 核的合同。
未完成推导传输、ZF 呈现对应、对称模型或相对一致性主定理。

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
