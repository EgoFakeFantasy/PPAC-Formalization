# 当前交付状态
2026-10-22；分支 migration/yesmeta-step3；本批基点 bef6eeb50b9aecb90647584016c8b0fd26bf144b。

F2.3a/F2.3b.1 已验收：原 Replacement 实际构造唯一完整复合图，合法输入实际取得唯一原自然复合码。
全部内部边满足 Edge(g,i,j) ↔ ∃k(Edge(r,i,k) ∧ Edge(t,k,j))；三个作用域显式保留，允许非单射和空域。
任意实际解码恢复同一复合关系；Ω 下，复合码实际存在当且仅当两个 MapCode 具有精确的可复合范围。
项重命名沿实际复合图，精确等价于存在内部中间项码的两阶段重命名；bound/free 和全部六个作用域保持。
此前实际恒等码、提升恒等、全内部公式恒等、全输入实际唯一输出和 11 构造精确律继续有效。

新增 11 模块、171 项显式声明、28 个 Source/sourceZF核/nativeZF核闭句模式。
实际验收退出 0：794 构建任务、8864 项审计、0 警告；九命令退出 0，五个 trust=0 入口通过。
292 项无公理依赖，8572 项允许依赖；763 份源码哈希独立回读差异 0。
Internal 累计 6549 项显式声明全覆盖；累计 843 对核心/native 精确足迹通过。
七份锁未变；YesMetaZFC 固定 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。

见[实际图/码与项复合验收](STEP4_COMPOSITION_MAP_TERM_ACCEPTANCE.zh-CN.md)。
原六规则/27 模式、19 源规则、九类 ZF 和 choice 额外证书限域保持；未推送。
原 OpenAI 完整构建/Comparator 未运行；日志和生成辅助留在忽略目录。

下一步 F2.3b.2：实际 binder 提升与图/码复合相容，处理零/后继边、实际中间后继及任意后继对齐。
然后完成 F2.3c 的全内部公式复合归纳及两阶段精确双条件。
提升相容、公式复合、恒等/复合联合总门禁、完整 FormulaRename、捕获规避替换、ProofZF/U、内部编译与解释仍未完成。
最终仍要求原 FirstOrder.Derives nativeZF [] (Formula.imp Con_ZF Con_target)，内部 Con 遍历全部内部 ω 证明码。
