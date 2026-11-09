# PPAC → YesMetaZFC

迁移固定 OpenAI PPAC 证明到 YesMetaZFC 原推导核。最终目标始终是：

```text
FirstOrder.Derives nativeZF [] (Con_ZF → Con_(ZF+PP+ACwo+¬AC))
```

当前为原第10阶段；第1–9阶段已完成，第11终验未开始。**最终对象Con未证明。**

本批完成任意条件的实际正文相消：ForcingConditionOpening.normalize不再要求代入条件等于外层条件；在对象量词内部使用原Replacement／列表编码构造S[j:=r]，用现成全内部mixed公式总性构造直接输出，并经原四路径公式归纳证明它与实际重绑定／opening／原mode2输出相等。原六个compiler见证内部消去，运行范围及公式／项码允许内部非标准值；不以更新表、输出或相等答案为前提。

两类真实guard的同背景证明、完整否定实例双前件消去及同背景全称引入已经完成；任意条件下的完整正文相消本批已接通。下一实际消费者仍是原force_mono负／存在分支与force_of_dense／exists_force_neg／forceFormula_imp的联合全内部码归纳，随后为规范化强迫MP、全部内部ZF/U公理与六规则Proof保真、精确reduction及最终Con。最终根节点条件背景由已有具体系统消去；不重建L、完整模式、mode3、原forall核或递归。 最新本地完整验收见`verification/forcing-condition-opening-acceptance.json`；Linux远端验收单独记录。

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

其余原生逻辑的局部操作现由ForcingLogicalCode接通，复用原NEG／EX并保持固定源的规范化。完整原始递归解释及最终对象Con仍未证明；验收见`verification/forcing-logical-code-acceptance.json`。

全11构造子的原始码单步调度现由ForcingCodeStep接通，原单步闭包的对象层历史可用性前提现已由ForcingCodeTotal对实际历史消去；全局公式输出唯一性及最终内部Con仍未证明。实际验收见`verification/forcing-code-step-acceptance.json`。

实际forcing码历史现由ForcingCodeRecursion调用原内部序数递归产生，并证明父历史读取与真实递归解释的对应；合法行的带类型输出存在性现已由ForcingCodeTotal证明；全局公式输出唯一性及最终Con仍未证明。实际验收见`verification/forcing-code-recursion-acceptance.json`。

原第10全内部码实际总性：ForcingCodeTotal复用原成员归纳，在同一ForcingCodeRecursion.compiled关系上为每个合法源码构造带类型输出，并为实际父历史消去ForcingCodeStep.available前提。历史／值集合、三个后继作用域、状态及输出均在对象EX内生成，没有给定输出或外部标准性。源free范围为内部空零，任意内部／非标准绑定范围及码均覆盖；目标f/j为固定R/H的对象numeral。两个普通nativeZF原核端点及完整九项验收均已通过，五项trust=0、零警告；旧证明正文和全部38381项既有足迹不变。此项不再列为缺口；公式输出唯一性、统一内部公理／Proof正确性、全部开放六规则证明与最终Con仍未完成。完整验收见verification/forcing-code-total-acceptance.json。
