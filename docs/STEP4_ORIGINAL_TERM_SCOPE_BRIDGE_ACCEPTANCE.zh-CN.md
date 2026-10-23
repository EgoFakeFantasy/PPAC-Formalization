# 原mode0／3纯签名项作用域桥验收

基点：eacd504fa4995cad1e703cc76019020fb02c2960。完成S3.4c.2b.2c.3c.2c.1：原kind1项轨迹与独立项程序、数值混合替换之间的对象桥。完整原参数列表／公式变换、规则检查器及最终Con仍未完成。

## 对象合同

背景保持原nativeZF的完整Collection呈现；语言只有等词和成员；证书返回原FirstOrder.Derives。最终目标仍为Derives nativeZF [] (Con_ZF → Con_target)，目标理论是ZF+PP+ACwo+¬AC。内部Con必须量化全部内部ω证明码，保留原六规则／27模式及全Separation／Collection。

本批深度、参数、上下文长度、索引、输入、输出、列表、图与轨迹均为对象变量。外部Bool仅索引固定的mode0／3及bound／free两个分支；没有宿主自然数值抽取、模型标准性、选择前提或新推导核。

## 原执行定义及精确双条件

```text
M(w,d,p) := d∈w ∧ p∈w
Root_t(w,d,p,n,q,r) := ∃mode (Num(mode(t),mode) ∧ Constructor_5,1(w,[mode,d,p,n,q],r))
Run_t(w,d,p,n,q) := ∃r (Root_t(w,d,p,n,q,r) ∧ OriginalFullTrace(w,r))
Checked_t(w,d,p,a,b,n,q) := (M(w,d,p) ∧ Term(w,a,b,n)) ∧ Run_t(w,d,p,n,q).
```

OriginalTermTraceSyntax直接采用原五字段kind1行及完整原表闭轨迹；不以valueSpec、旧替换关系或独立项程序定义执行。Num及原行码是实际内部存在见证。全部六个执行定义接受独立的直接oracle引用检查，连同既有29项共35项。

在Omega(w)、实际IdentityCode(w,a,I)、Converted_bound(w,I,R,a,a,c)、TermList(w,b,a,c,L)下，对所有内部d,n,q证明：

```text
Checked_3(w,d,L,a,b,n,q)
 ↔ M(w,d,L) ∧ TermProgram.checked(w,R,L,a,b,a,c,n,q)
 ↔ M(w,d,L) ∧ CodedMixedTerm.substituted(w,R,L,a,b,a,c,n,q).
```

在Omega(w)、实际IdentityCode(w,a,I)、ShiftCode(w,b,B,J)、Converted_bound(w,I,R,a,a,B)、Converted_free(w,J,S,b,a,B)下，对所有内部d,p,n,q证明：

```text
Checked_0(w,d,p,a,b,n,q)
 ↔ M(w,d,p) ∧ TermProgram.checked(w,R,S,a,b,a,B,n,q)
 ↔ M(w,d,p) ∧ CodedMixedTerm.substituted(w,R,S,a,b,a,B,n,q).
```

p在mode0中虽不参与结果，仍保留原行要求的p∈ω；没有删除这个守卫。候选q不预设自然性或项合法性；Term在checked公式内部，因此不是仅对预先给定外部项的模式证明。恒等／位移／转换环境假设均明确列在闭句前件，已有环境构造库仍承担其存在性。

## 实际推导链

| 模块 | 对象推导职责 |
|---|---|
| OriginalTermTraceSyntax | 原执行／守卫定义、重命名及真实轨迹装配 |
| OriginalTermTraceVariable | 原行存在、四变量全候选Run↔valueSpec |
| OriginalTermImageFields | 实际恒等图／位移图及转换列表字段的精确对应 |
| OriginalTermProgramPoint | 任意内部合法变量索引处，原轨迹↔独立项程序 |
| OriginalTermScopeElimination | 正式消去Term内两个内部变量存在分支 |
| OriginalTermProgramBridge | 全项作用域桥及四个checked／coded双条件 |
| ObjectOriginalTermProgram | 四组闭句的Source.Derives、TheoryTransport及ZFReplay原核证书 |

纯签名Term只含bound／free变量分支。application 1不是凭名称忽略：每个真实内部变量码进入已验收的完整原表变量精确分派，排除不兼容的原application分支，再以对象析取消去和存在消去覆盖整个Term守卫。没有声称无守卫的原扩展函数项也被覆盖。

## 实际验收

1360构建任务、14967项审计（376无公理／14591允许依赖）、零警告；九命令及五trust=0入口全部退出0；1224份工作区独立哈希一致、1651对精确证书足迹、12623项Internal显式声明覆盖。

新增7模块47声明、4组闭句及4对精确证书；核心严格为std3（propext、Classical.choice、Quot.sound），native严格为std3加原七固定证书依赖。七个理论／规则／工具链锁、隔离Choice桥和固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。

严格串行执行，LEAN_NUM_THREADS=1。定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalTermProgram退出0；C:/Python314/python.exe -X utf8 scripts/verify.py退出0。五个入口均使用--trust=0。独立回读见本地verification/original-term-readback.json，实际命令见verification/commands.json。没有运行OpenAI原仓完整构建、Comparator、推送或PR。

此前工具链读取失败发生在C盘空间不足时；本次空间恢复后七模块均实际编译通过，不将此前未验收草稿计入历史完成数。

## 后续门

下一步对原kind2参数列表建立完整原表分派及nil／cons轨迹方程，在对象内部列表归纳中接入本批项桥，再推进kind3的全十一公式分支和量词深度后继。纯成员关系的二参数列表须保持实际原list编码，不能用新二元简写跳过原参数列表。

原扩展语言函数图消去／quotation总桥、原严格数值Option接口总对应、全mode0／3公式、原规则5／4且无FreeClosed、专用ProofZF/U、全部内部码检查／编译、完整内部解释及最终Con均仍未完成。此次四个细门为true，其余总门保持false。
