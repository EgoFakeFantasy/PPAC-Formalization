# 清理决定
只清理本轮独立迁移分支；原始提交为 721d331a4ddd3c1d759a719a55f09388ade4fa30。
清理前已生成外部 git bundle 与源码 tar.gz；原来没有用户未提交改动。
保留 Pullback、StageCapture、Choice/Basic、Splice、Splitting 作为条件辅助。
从 Repair/Forcing 精确提取 jrelOf、jrelOf_fun、jrelOf_sec、jrelOf_inj、jrelOf_injDir、jrelOf_total。
其余 Repair、ClassObstruction、Cohen、Random、FuchsPrikry 删除，因为不服务选定的新模型路线。
辅助模块统一由 PPAC.Auxiliary 导入，不再让宿主 PP 与对象 PP 共享主入口。
README、GAPS、THEOREM_COVERAGE、Audit、verify 重写以符合新范围；不删除 Git 历史。
逐文件理由见 CLEANUP.json。未因此证明旧引理有错，也不判断其在其他项目中无用。
