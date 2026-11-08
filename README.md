# PPAC → YesMetaZFC

迁移固定 OpenAI PPAC 证明到 YesMetaZFC 原推导核。最终目标始终是：

```text
FirstOrder.Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

当前为原第10阶段。同一实际系统的源数学应用、全集合PP及完整目标理论逐实例装配已接通。原公理行和全部原模式码流水线的存在、闭类型、独立见证唯一性均已证明。

本批已接通原正文到完整原生Separation/Collection句的准确quotation双条件：实际编译、三个原重命名出口、两个不同Collection矩阵、原模板及整个闭包均由对象推导消费，不再给定中间quotation。五个普通nativeZF原核端点已验收。正文／参数数目仍为外部模式索引，原始有效输入guard保留。

真正剩余为统一内部ZF/U公理正确性／强迫、全部内部／非标准六规则Proof/Con传输及第11终验。原第4官方Comparator已实际接受，证据见`verification/original-comparator-acceptance.json`。**最终对象Con未证明。** 最新对象代码报告为`verification/forcing-exist-guards-code-acceptance.json`；完整否定码分支亦已验收，仍需存在子码绑定重排和完整递归。

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
