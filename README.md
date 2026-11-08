# PPAC → YesMetaZFC

迁移固定 OpenAI PPAC 证明到 YesMetaZFC 原推导核。最终目标始终是：

```text
FirstOrder.Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

当前处于原第 9 阶段。第 8 阶段的同一具体系统已完成；完整 L/ZFC、全公理模式、名字／图／内部递归及强迫前端已经存在并被复用。第 9 阶段已完成实际 ACwo、¬AC、完整 ordinal_presentation、子集像满射、检查名指标最小索引图、完整 indexedImage／wellorderable_image，全内部集合指标的统一最大值家族，以及统一截面／良序目标反向单射。切片B／Ypart／Spart名字及先于全内部指标的共同支撑现已实际构造；切片图完整满射、Spart互斥、occurrence及实际Ypart名字覆盖现也已有普通nativeZF原核端点。空域注入／稠密成员及实际双名字参数的全域唯一／HS／固定性现也已取得原核端点。已有UniformMaximum可直接消费该参数关系，无需另造参数族图；实际slice_candidate、四项输入及全内部指标候选函数族现已取得普通nativeZF原核端点；完整assemble现也已取得普通nativeZF原核端点，保留实际Graph／HS／支撑／完整injection；实际候选族—支撑交集—assemble现已接成presentation_reverse_injection原核端点；下一是Main.reverse_injection_dense的全集合归约。第 10 的 PP/Main／全部内部及非标准证明码传输、第 11 终验和原第 4 Comparator 尚未完成。**最终对象 Con 未证明。** 当前精确验收以以下文档为准：

- [原 1–11 阶段与验收门](docs/AGENT_WORKFLOW.zh-CN.md)
- [当前已验收／未完成项](docs/STATUS.zh-CN.md)
- [内部 Con 固定规格](docs/OBJECT_TARGET.zh-CN.md)
- [已有接口及复用边界](docs/REUSE_CONTRACTS.zh-CN.md)
- [固定源码、哈希及逐声明依赖](docs/SOURCE_LOCK.json)

## 从干净检出复现

本仓使用 Lean 4.33.1；由 elan 按 lean-toolchain 安装。YesMetaZFC 依赖固定于 039c8e132cc19671d73a3933c66b4799d2599dd6。验证器还会核对固定供体的原始证明正文，不能仅依赖本机缓存。

在本仓父目录中准备两个相邻的源仓库，然后进入本仓：

```text
git clone https://github.com/EgoFakeFantasy/YesMetaZFC.git yesmetazfc-analytic-comprehension
git -C yesmetazfc-analytic-comprehension checkout --detach 79793365c2145c53db37eaf8ab23a64826bd9738
git clone https://github.com/openai/math.git openai-math-ppac-source
git -C openai-math-ppac-source checkout --detach 1581d4cbdd69a0faf34b2089614fe2a814316a6a
cd ppac-yesmeta-migration
lake update
python scripts/check_ci_inputs.py
python -m unittest discover -s scripts -p test_ci_compatibility.py
python scripts/verify.py
```

GitHub Actions 执行同样的固定检出和依赖引导，再运行完整构建与五项 trust=0 检查。入口为 import PPAC；宿主辅助独立为 PPAC.Auxiliary。Lean/Lake 串行；原 OpenAI 4.34.1 的 Comparator 验收另行记录。

文本源码锁采用 sha256/text-crlf-to-lf/v1：仅将 CRLF 转为 LF，保留正文、其它空白、孤立 CR、BOM 及其它全部字节。二进制归档保持原始字节哈希。此规则消除 Windows Git 与 Linux Git 的检出换行差异，不放宽证明正文或公理依赖检查。

```text
python scripts/verify.py --source-check-only
```

上述命令只运行源码／依赖预检，不进行 Lean 构建或声明公理审计，不能当成完整验收。完整验收使用不带该选项的命令；本地通过和远端 CI 通过分开记录。

NatPacket／字节兼容、泛滤真值支线及独立 L 重建均已退出开发。已批准的 358 模块冻结闭包已退役，恢复依据见 [清理记录](docs/CLEANUP.zh-CN.md)；不按旧历史待办重建现成基础。
