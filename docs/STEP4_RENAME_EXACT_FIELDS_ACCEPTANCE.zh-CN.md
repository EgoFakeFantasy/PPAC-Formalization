# 原11构造精确端点律验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 c6c73bcbf83d0c9c7249ccf6a98ff5feaa8e86c6。
F1e.4b已完成：给定原源/目标构造字段，正式RenameFormula精确等价于规范子判断。
此前全内部实际输出存在唯一、类型保持和成员归纳关闭继续有效。
映射恒等/复合、捕获规避替换、ProofZF/U与最终内部Con仍未完成。

## 对象合同及实际范围

对象语言仍为原YesMetaZFC纯等词/成员语言，背景仍为原nativeZF的Collection呈现。
最终要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，目标理论为ZF+PP+ACwo+¬AC。
内部Con遍历全部内部ω证明码，保留原六规则、27逻辑模式和完整Separation/Collection。
不加入对象AC、不可达、Con(nativeZF)或外部标准模型前提。

记R、S为内部自然映射码，r、s为实际完整解码图；a,b和c,d分别为源/目标bound、free作用域。
Encoded(w,r,a,c,R)及Encoded(w,s,b,d,S)保留原长度、完整图和独立目标范围。
本批码、字段、图及作用域均为任意内部对象，允许非单射和非标准码，不限外部标准深度。
所有闭句均有源ZF、经TheoryTransport的sourceZF原核及经ZFReplay的nativeZF原核Derives。

## 从筛选升级为正式双条件

每个原固定标签分支均有向完整Cases的原析取引入。
分支在所有内部候选上给出目标FormulaCode：原子正式消去四/五个字段见证；
逻辑分支使用MapCode的目标作用域、真实普通/提升子判断的目标类型及原单构造类型双条件。
已知源标签时，完整筛选的逆向由目标类型和Cases反向接回正式RenameFormula。
关键证书：native_introBranch、native_branchTarget、native_sourceCaseIff。
该中间接口仍可带Input；最终端点律已经消去此额外前提。

## 两端字段的精确恢复

源和目标原构造可各自绑定不同候选字段。
原同码字段单射分别恢复两个端点的字段相等，再用原等词替换规则传输子判断。
不存在从宿主Prop提取字段数组或使用外部样本比较。
原分支本身于是精确等价于：

- 等式：TermRename(w,r,s,a,b,c,d,x,X) ∧ TermRename(w,r,s,a,b,c,d,y,Y)。
- 成员式：ZeroScalar(w,z) ∧ (z=Z ∧ (TermRename(x,X) ∧ TermRename(y,Y)))。
- 单子式：Check(advance,w,x,R,S,a,b,c,d,X)。
- 二元式：RenameFormula(w,R,S,a,b,c,d,x,X) ∧ RenameFormula(w,R,S,a,b,c,d,y,Y)。

成员式源码字段为[z,x,y]，目标为[Z,X,Y]；ZeroScalar和两端符号相等均显式保留。
并未把原零符号码替换为新的见证，也未省略错误目标符号的拒绝条件。
普通Check是原RenameFormula；提升Check是实际绑定两个后继和提升码的AdvancedRename。
原分支双条件证书：native_equalityRawIff、native_membershipRawIff、native_singleRawIff、native_binaryRawIff。

## 无额外Input的正式端点律

规范子判断恢复真实源类型：项关系给源Term；普通子判断给源FormulaCode；
提升子判断实际取得CodedLift，从真实源后继和体类型构造原AdvancedCode。
再经给定源原构造的类型双条件得到源FormulaCode；实际Encoded图给两个MapCode。
因此规范子判断本身推出Input，最终端点律不额外假定合法源码。
关键证书：native_checkSource及equality/membership/negation/forall/exists/binary的native_*Input。

在Ω及给定实际Encoded图下，给定两端相应原构造得到：

| 原模式 | 正式RenameFormula的精确右侧 |
|---|---|
| 假、真 | n=q；只需给定源空构造，无需目标构造前提 |
| 等式 | 两项分别从x到X、y到Y的实际TermRename |
| 成员式 | 原ZeroScalar(z)、z=Z及两项实际TermRename |
| 否定 | 同一R,S及作用域下的子RenameFormula(x,X) |
| 四种二元 | 同一R,S及作用域下的两个子RenameFormula |
| 两个量词 | 原AdvancedRename(x,X)，实际保留后继作用域、提升码及原free参数 |

相应原核闭句：native_nullaryIff（Bool覆盖两个原空模式）、native_equalityIff、native_membershipIff、
native_negationIff、native_forallIff、native_existsIff、native_binaryIff（Fin 4覆盖四个原二元模式）。
全部11模式均无Earlier、载体、历史或额外Input前提。
原子端点律给定完整实际图，因为其规范项关系的参数正是这些图；候选解码图仍由既有完整图唯一性对齐。

## 仅映射码的逻辑律和指定实际提升

逻辑右侧只使用R,S，不依赖选定解码图r,s。
本批正式消去两个MapCode图见证，取得仅MapCode前提的否定、四二元和两个量词端点双条件。
关键证书：native_negationCodeIff、native_forallCodeIff、native_existsCodeIff、native_binaryCodeIff。

再给任意实际CodedLift(w,a,c,R,u,v,L)，两个量词均满足精确式：
RenameFormula(w,R,S,a,b,c,d,n,q) ↔ RenameFormula(w,L,S,u,b,v,d,x,X)。
其前提为Ω、原free MapCode、实际CodedLift及两端同种原量词构造。
原bound MapCode由CodedLift恢复，无需另加；free码S及作用域b,d保持不变。
关键证书：native_quantifiedAtLift（Bool覆盖原forall/exists）。
这不是固定宿主后继或标准binder深度；u,v,L均为实际内部候选。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0。
原源19规则及九类ZF构造锁、版本、全仓wfail构建及五个trust=0入口共九条命令全部退出0。

| 检查项 | 实际结果 |
|---|---|
| 完整构建 | 773 jobs，退出0 |
| 声明审计 | 8562项；284项无公理依赖，8278项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 10模块、139项，全覆盖 |
| Internal累计显式声明 | 6247项，无漏审 |
| 新增闭句模式 | 26对核心/native精确足迹 |
| 累计闭句模式 | 799对核心/native精确足迹 |
| 源码SHA256独立回读 | 742份，差异0 |
| 九命令/五trust=0 | 全部通过 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

核心证书精确依赖propext、Classical.choice、Quot.sound；native另含原七个固定ZF定义证书的既有依赖。
没有新增自定义公理，没有扩大原choice额外闭性证书的隔离范围。
Classical.choice是宿主证明证书依赖，没有据此加入对象AC或抽取内部集合选择函数。
CheckStep4逐一检查26类native闭句，并以rfl固定两项端点及原ZeroScalar/符号相等的规范AST。
独立复核留在忽略目录verification/rename-fields-readback.json。
本批未运行原OpenAI完整构建/Comparator；生成辅助和日志留本地；未推送。

## 下一工程单元

| 顺序 | 实现输入 | 必须交付的对象证据 |
|---|---|---|
| F2.1 | 复用完整图构造、实际MapCode及已有项恒等 | 实际恒等映射码及其提升恒等，保留真实后继和独立范围 |
| F2.2 | 精确11构造律、恒等码及内部归纳 | 所有合法内部公式的实际自重命名和唯一输出恒等律 |
| F2.3 | 完整图复合及编码、项关系、真实binder提升 | 图/码复合的存在与全边式；项和公式复合及提升兼容，允许非单射 |
| S/5/6 | 任意内部替换序列、原规则/全模式 | 捕获规避替换；专用ProofZF/U；全内部码编译/解释；最终原核内部Con蕴含 |

精确单构造律提升为True。映射恒等/复合、完整FormulaRename总门禁、捕获规避替换、ProofZF/U和最终内部Con保持False。
存在唯一、完整递归判据及精确端点接口已齐备；不能把这些成果替代最终相对一致性对象主句。
