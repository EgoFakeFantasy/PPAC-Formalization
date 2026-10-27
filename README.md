# PPAC → YesMetaZFC

迁移对象是固定 OpenAI PPAC 证明，目标底座是 YesMetaZFC 原推导核。最终要求：

```text
FirstOrder.Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

**当前主开发在原第 8 阶段，尚未进入收尾。** 第 1–3 阶段的原范围已验收；第 4 阶段原 Main／端点已验收，完整 Comparator 未验；第 5 阶段基础包已有；第 6 阶段缺已有 L 定理的版本／语言接口；第 7 阶段已有条件式强迫 ZF 前端，待同一具体系统实例化。第 9–11 阶段未闭合。

第 8 阶段已有 Base、实际 Path/Alphabet/Word、呈现、保守性、条件并、profile 和 pushout，以及实际 interval 和权重图。本批接通原 same-head margin 和覆盖所有内部长度的统一归纳，并构造完整 Word HeightCost 的对象证书：实际高度／cap／成本图、全部上下界、每个严格比较的实际遗漏成本上确界及严格高度间隙、图唯一性、旧成本上确界保持。全部现成基础和缩放／递归／上确界设施直接复用。

本批已在同一实际载体上组合加权新对象、inclusion、实际请求 probe／完整 profile／新颖性／基数界／旧 profile 保持，取得原核对象证书。本批又从原 ProbeData 父输入调用全部现成生产者，消去字母表／floor／interval 数据前提。本批已构造 Merger 的实际 prescribed copies、投影和右自由作用对象核证书。本批又构造全内部 Merger Word 载体、右作用及实际乘法图，原 old/snoc 方程已有。本批已在同一图上证明完整 Word 左消去单子和 conical。本批已证明原指定 copies 条件并；下一缺口是 Word 条件并、权重、Placement／ConservativeHull 和最终单子；已有 Probe 数学不重做。**最终对象 Con 未证明；ZF/U 专用内部公式和全部内部码传输仍未闭合。**

完整 ZF 模式、内部递归、Proof/Sat、原核完备性及新版任意 ZF 模型中的 L→ZF/ZFC 已存在。剩余的是具体版本／语言／背景适配及源 PPAC 主链，不能把已有数学重新列为待证。

- [原 1–11 阶段与真实验收门](docs/AGENT_WORKFLOW.zh-CN.md)
- [本次实际验收与未完成项](docs/STATUS.zh-CN.md)
- [内部 Con 固定规格](docs/OBJECT_TARGET.zh-CN.md)
- [已有仓库接口及复用边界](docs/REUSE_CONTRACTS.zh-CN.md)
- [OpenAI 源证明对应和依赖](docs/MATH_REDUCTION_ROUTE.zh-CN.md)
- [固定源码与逐声明依赖](docs/SOURCE_LOCK.json)
- [清理与恢复依据](docs/CLEANUP.zh-CN.md)

入口 `import PPAC`；宿主辅助独立为 `PPAC.Auxiliary`。Lean 4.33.1，YesMetaZFC 固定 `039c8e132cc19671d73a3933c66b4799d2599dd6`。执行 `python scripts/verify.py`，Lean/Lake 串行；原 OpenAI 4.34.1 验收与本仓分开记录。

NatPacket／字节兼容、泛滤真值分支及独立 L 重建均不再开发。旧批次记录从 Git 恢复，不再放首页作为当前阶段。新增清理复审已定位 358 个独立冻结兼容模块；精确清单、归档和拟议差异已备好，批量删除因自动审批拦截尚未执行。没有上传或发布本轮改动。
