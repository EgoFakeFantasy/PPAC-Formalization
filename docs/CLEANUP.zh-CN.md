# 清理决定
只清理本轮独立迁移分支；原始提交为 721d331a4ddd3c1d759a719a55f09388ade4fa30。
清理前已生成外部 git bundle 与源码 tar.gz；原来没有用户未提交改动。
保留 Pullback、StageCapture、Choice/Basic、Splice、Splitting 作为条件辅助。
从 Repair/Forcing 精确提取 jrelOf、jrelOf_fun、jrelOf_sec、jrelOf_inj、jrelOf_injDir、jrelOf_total。
其余 Repair、ClassObstruction、Cohen、Random、FuchsPrikry 删除，因为不服务选定的新模型路线。
辅助模块统一由 PPAC.Auxiliary 导入，不再让宿主 PP 与对象 PP 共享主入口。
README、GAPS、THEOREM_COVERAGE、Audit、verify 重写以符合新范围；不删除 Git 历史。
逐文件理由见 CLEANUP.json。未因此证明旧引理有错，也不判断其在其他项目中无用。

## 已批准的精确退役（2026-10-27）

用户已明确批准 verification/retired-packet-closure-review.json 中的 358 模块闭包及专属入口／测试／审计删除。本轮已执行；此前自动审批阻拦已由这次明确授权解决，不再等待确认。原归档／补丁哈希不变，执行及修复证据见 verification/retired-packet-closure-execution-20261027.json。

| 对象 | 实际处理与边界 |
|---|---|
| 135 个先前孤立模块 | 先前已退役，不计入本轮删除；旧归档及恢复提交保留。 |
| 本轮 358 个模块 | 291 个 Packet/reader 与 67 个专属冻结消费者全部删除；逐文件 SHA 与 ZIP 一致，无保留证明导入；17 个 umbrella 入口同步移除。源码逻辑大小 1,993,851 字节。 |
| 退休检查 | 14 个专用检查函数、263 条专属测试、3219 项声明审计、263 对已退役端点的精确足迹检查和 19 个过时状态项已清除。仅限批准退休模块。 |
| 保留检查修复 | 旧提案跨相邻 example 边界误带 compilerInvalidSourceRejected 测试，已恢复；又补清旧提案漏掉的 14 组退休端点预期。原主线静态检查、通用构建、全部保留声明审计、五次 trust=0 和最终 Con 门未降低。 |
| 直接生成缓存 | 仅按已退役源模块路径白名单删除 2864 个 .lake/build 直接生成文件；无递归目录删除，无重解析目标。逻辑大小 225,677,746 字节；缓存清理时段实测可用空间增加 227,020,800 字节，二者分别记录。见 verification/cleanup-approved-packet-artifacts-20261027.json。 |
| 剩余主线 | 27,050 项保留声明的全部依赖足迹已与清理前逐项一致；正式完整验收已通过：2612 项构建、27050 项声明、九命令／五次 trust=0 均退出 0，零警告，2175 份当前指纹及 75 份源哈希匹配；不据此宣称最终数学完成。 |
| 必需脚本／外部仓库 | check_source_rules.py、check_source_theory.py、verify.py 均保留；不清理供体、工具链或其他项目。一次一个本项目 Lean/Lake，不终止其他进程。 |

累计退役 493 个模块的逐文件归档位置／恢复提交见 RETIRED_PACKET.json，两个 ZIP 均保留。退役理由是它们不服务当前选定的源迁移路线，不是旧定理无效。旧过程记录由 Git 和清理清单保留，不再反复写成当前任务。

主开发仍为原第 8 阶段；本轮清理不算数学阶段完成。后续继续固定 OpenAI MergerCones 的有限平均／乘积权重，最终目标仍为原核对象内部 Con 蕴含。
