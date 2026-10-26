# 清理决定
只清理本轮独立迁移分支；原始提交为 721d331a4ddd3c1d759a719a55f09388ade4fa30。
清理前已生成外部 git bundle 与源码 tar.gz；原来没有用户未提交改动。
保留 Pullback、StageCapture、Choice/Basic、Splice、Splitting 作为条件辅助。
从 Repair/Forcing 精确提取 jrelOf、jrelOf_fun、jrelOf_sec、jrelOf_inj、jrelOf_injDir、jrelOf_total。
其余 Repair、ClassObstruction、Cohen、Random、FuchsPrikry 删除，因为不服务选定的新模型路线。
辅助模块统一由 PPAC.Auxiliary 导入，不再让宿主 PP 与对象 PP 共享主入口。
README、GAPS、THEOREM_COVERAGE、Audit、verify 重写以符合新范围；不删除 Git 历史。
逐文件理由见 CLEANUP.json。未因此证明旧引理有错，也不判断其在其他项目中无用。

## 当前清理裁决（2026-10-27 复审）

重复逐批叙述已从本文件删去；历史明细可从 Git `1af856e` 的本路径恢复。当前保留依据是对选定原源码迁移路线的实际生产者／消费者依赖，不把“已证明”自动等同“本路线需要”，也不把退役结论说成旧定理不成立。

| 对象 | 当前裁决与证据 |
|---|---|
| 已退役的 135 个孤立 Packet/ObjectPacket 模块 | 已删除；精确清单、哈希和恢复提交见 RETIRED_PACKET.json。历史验收保留，不再次计作本轮删除。 |
| 剩余 291 个 Packet 模块与 67 个冻结内部消费者 | 精确反向闭包共 358 项，没有其他保留证明模块引用；唯一 umbrella 入口拟同步去除。逐份源码哈希及恢复 ZIP 已再次核对。verification/retired-packet-closure-review.{json,zip,patch} 是提案，尚未执行。 |
| 上述支线的检查 | 拟同步退役 14 个专用函数、263 个 fixture、3219 个声明审计和 19 个过时状态项；通用保留代码编译、全部保留声明、trust=0 和最终 Con 门均保留。不是任意删测试以取得通过。 |
| 大规模退役审批 | 本轮提交同一精确补丁，自动审批再次拒绝，理由为需要用户明确批准具体 358 模块／配套检查删除范围；已发确认。源码、检查和缓存均仍在，不绕过。 |
| scripts/check_source_rules.py、check_source_theory.py、verify.py | 三者都在实际验收命令链中，不是无用脚本，保留。 |
| 供体、工具链和其他仓库 | 保留；本轮未修改或清理。固定源 75 份哈希匹配；两个 YesMetaZFC checkout 干净。 |
| 本轮 6 模块／25 声明 | 直接服务 ProbeMargins 的 height_bounds、cost_le_scale、cost_old_factor；保留并纳入全部声明审计。没有新增持久生成脚本。 |
| 预审输入／进程 | 只在完整 Audit 覆盖且全量验收成功后，按本仓绝对路径、无重解析点和 SHA 白名单删除本轮 ProbeWeightBoundsAudit.lean。保留成功构建、预审及全验收日志；不终止正在验收的进程或其他项目进程。已全量验收并删除该唯一探针（2188 字节），清单见 verification/cleanup-probe-weight-bounds-20261027.json。没有残留 Lean/Lake，未终止任何其他进程。 |

停止开发 NatPacket／字节兼容、泛滤 truth、独立 L 重建、重复 Sat 及无当前原消费者的完整实数域。现行 STATUS、AGENT_WORKFLOW、GAPS 和 THEOREM_COVERAGE 已移除“已有完整模式／L 数学／Word 权重界尚未做”的误报；对旧兼容支线的历史 False 不再当作本项目基础数学待办。
