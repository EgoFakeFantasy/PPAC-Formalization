# PPAC → YesMetaZFC

迁移对象是固定 OpenAI PPAC 证明，目标底座是 YesMetaZFC 原推导核。最终要求：

```text
FirstOrder.Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

**尚未完成，也未进入收尾。** 按最初 1–11 阶段，连续完整验收到 1–3；4 的原 Main／端点已过、完整 Comparator 未验；5 基础包已过；6 的已有 L 接口待适配；7 的强迫 ZF 前端待具体系统实例化；当前主开发在 8，9–11 未闭合。实际 Word 左消去单子、oldHom、整除反映及 conical 已验收；generator 实际图及关系已验收；本批沿固定 ProbeWords 完成 evalHom 与任意内部目标单子上的实际 liftHom 原核证书；hom_ext、呈现与大小界及完整扩张仍待迁移；最终对象 Con 未证明。

完整 ZF 模式、内部递归、Proof/Sat、原核完备性及新版任意 ZF 模型中的 L→ZF/ZFC 已存在。剩余的是具体版本／语言／背景适配及源 PPAC 主链，不能把已有数学重新列为待证。

- [原 1–11 阶段与真实验收门](docs/AGENT_WORKFLOW.zh-CN.md)
- [本次实际验收与未完成项](docs/STATUS.zh-CN.md)
- [内部 Con 固定规格](docs/OBJECT_TARGET.zh-CN.md)
- [已有仓库接口及复用边界](docs/REUSE_CONTRACTS.zh-CN.md)
- [OpenAI 源证明对应和依赖](docs/MATH_REDUCTION_ROUTE.zh-CN.md)
- [固定源码与逐声明依赖](docs/SOURCE_LOCK.json)
- [清理与恢复依据](docs/CLEANUP.zh-CN.md)

入口 `import PPAC`；宿主辅助独立为 `PPAC.Auxiliary`。Lean 4.33.1，YesMetaZFC 固定 `039c8e132cc19671d73a3933c66b4799d2599dd6`。执行 `python scripts/verify.py`，Lean/Lake 串行；原 OpenAI 4.34.1 验收与本仓分开记录。

NatPacket／字节兼容、泛滤真值分支及独立 L 重建均不再开发。旧批次记录从 Git 恢复，不再放首页作为当前阶段。历史证明尚有结构模块依赖，未声称全部裁剪完成。没有上传或发布本轮改动。
