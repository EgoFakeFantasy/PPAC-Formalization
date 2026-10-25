# 清理决定
只清理本轮独立迁移分支；原始提交为 721d331a4ddd3c1d759a719a55f09388ade4fa30。
清理前已生成外部 git bundle 与源码 tar.gz；原来没有用户未提交改动。
保留 Pullback、StageCapture、Choice/Basic、Splice、Splitting 作为条件辅助。
从 Repair/Forcing 精确提取 jrelOf、jrelOf_fun、jrelOf_sec、jrelOf_inj、jrelOf_injDir、jrelOf_total。
其余 Repair、ClassObstruction、Cohen、Random、FuchsPrikry 删除，因为不服务选定的新模型路线。
辅助模块统一由 PPAC.Auxiliary 导入，不再让宿主 PP 与对象 PP 共享主入口。
README、GAPS、THEOREM_COVERAGE、Audit、verify 重写以符合新范围；不删除 Git 历史。
逐文件理由见 CLEANUP.json。未因此证明旧引理有错，也不判断其在其他项目中无用。

## 2026-10-26 重审清理

恢复点：清理前受 Git 管理的文件均可从 `7dbb1c1` 恢复。README、OBJECT_TARGET、STATUS、GAPS 去掉重复或过时的调度，恢复原 1–11 阶段；历史单批验收报告保留。

已按绝对路径白名单删除本项目 `.local` 顶层过期 `.py`、`.log`、审计／预审 `.lean` 及旧复用探针，共 1,276 文件，逻辑大小 5,694,498 字节；当次实测可用空间增加 4,837,376 字节。逐文件 SHA-256 清单位于忽略的 `verification/cleanup-20261026.json`。已先确认 `.local` 没有 Git 跟踪文件，跳过 reparse 项，不递归触及其他项目。

没有残留 Lean/Lake 编译进程需要终止；两个本轮沙箱初始化会话已退出。此后仅启动串行正式验收。

本次没有删除已验收的 Packet/Varint 证明：静态进口图显示直接按名称删除会连带列表拼接、反转等其他模块。它们退出开发主线，但尚未完成独立依赖裁剪，仍纳入历史证明审计；不能宣称这部分已全部删除。冻结候选子目录及原清单暂保留，不重新激活。不因历史辅助数量大就批量丢弃依赖。
