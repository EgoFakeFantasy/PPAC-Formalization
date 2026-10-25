# PPAC → YesMetaZFC

本工程迁移重构 OpenAI 的 PPAC 证明到 YesMetaZFC 原基础；不是另起一条独立证明路线。

**2026-10-26 重审：最初阶段 1–3 已完成；阶段 4 的原环境 Comparator 未验收；阶段 5–6 部分完成；阶段 7–10 的主数学证明链尚未完成迁移，阶段 11 未到。此前“四步收尾／接近完成”的判断撤回。**

最终目标是纯等词／成员语言、完整 nativeZF、原 FirstOrder.Derives 中的对象闭句：

```text
Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

源的全参数 Separation／Replacement、原生 Separation／Collection 及两种 AC 的推导对应已经完成；不得重新列为未做。其他 L 工程也已有全模式 ZF 和 ZFC 模型定理，当前须适配其精确背景／量词／语言接口，不能把已有构造说成没有证明。

- [原 1–11 阶段、实际状态与下一门槛](docs/AGENT_WORKFLOW.zh-CN.md)
- [源数学链、已接入与尚待接入的区分](docs/MATH_REDUCTION_ROUTE.zh-CN.md)
- [精确对象目标和内部 Con 规格](docs/OBJECT_TARGET.zh-CN.md)
- [其他仓库的实际接口与复用证据](docs/REUSE_CONTRACTS.zh-CN.md)
- [源码固定提交及哈希](docs/SOURCE_LOCK.json)
- [清理范围与恢复点](docs/CLEANUP.zh-CN.md)

入口：`import PPAC`。旧宿主辅助单独为 `PPAC.Auxiliary`，不是对象 PP 证明。
Lean 4.33.1，唯一 Lake 依赖为 YesMetaZFC `039c8e132cc19671d73a3933c66b4799d2599dd6`。
运行 `python scripts/verify.py`；一次只运行一个 Lean/Lake 构建。实际结果保存在忽略的 `verification/`。
该验证针对本仓，不是原 OpenAI Lean 4.34.1 Comparator 的验证。

字节／NatPacket／LEB128 兼容退出迁移主线；不再开发。已验收的历史证明暂保留其审计，未完成依赖裁剪前不把它们说成已全部删除。当前状态不再由旧辅助验收的条目数推动。

旧的重复进度文字可从 Git `7dbb1c1` 的 README 和目标规格恢复；逐批验收报告仍保留各自历史范围，不作为当前阶段指令。
OpenAI 语法及公式按 Apache-2.0 适配，见 NOTICE；既有代码作者信息保留。
