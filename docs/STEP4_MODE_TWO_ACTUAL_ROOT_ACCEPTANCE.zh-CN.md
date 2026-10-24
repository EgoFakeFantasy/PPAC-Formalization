# mode2 实际根框架及闭参数提升保持验收（2026-10-24）

本批从原实际 instantiateCoded 环境推出 mode2 零深度根框架，消去其元数据及变量兼容性前提，并完成根上的全部内部合法纯项运行对应。另已证明空绑定参数经实际 binder 的 bound 后移／free 恒等重命名后保持原码。真实 binder 框架闭包、mode2 完整公式与最终内部 Con 蕴含尚未证明。

## 对象背景与最终目标

对象语言是纯等号／成员语言；背景为原 nativeZF，完整 Separation／Collection，不添加对象 Choice。最终目标保持：

```text
FirstOrder.Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

要求覆盖全部内部 ω 证明码、原六规则与 27 逻辑模式。编译和宿主语义结果均不替代该原核推导。

## 完成的实际对象接口

InstantiateVariableSpecialization 在原独立数值规格上证明阈值点输出等于 P、阈值以内输出原变量。阈值点排除另外两个分支使用对象 Foundation 的非自成员性；深度以内排除反向成员使用原内部自然顺序。前驱见证在对象 EX 内消去。

InstantiateClosedParameterRename 从真实 free 分支取得内部索引，使用实际 bound 后继图、free 恒等图及原项重命名，证明 renamed(P,q) ↔ q=P。closedParameter 的内部空绑定界先消去，随后实际索引 EX 消去，没有抽取宿主变量或假设任意参数均提升不变。

InstantiateOperationFrameRoot 从实际 instantiateCoded(w,z,b,A,P,R,S) 读取原参数类型及 A=succ(z)。empty(z) 下任意 i∈A 推出 i=z；原 instantiate_zero 字段律与阈值点规格对应，自由分支通过原 instantiate_free 字段律及变量码唯一性对应。对全部内部索引、输入变量码、候选输出作对象 ALL3，得到两类兼容关系。真实 termLists 和闭参数均由原环境推出。

from_actual_input 的对象前提仅有 Ω、Num2、empty(z) 和实际 instantiateCoded。z∈ω 由空集属于 ω 推出，P∈ω 由实际参数项类型推出，因此不要求额外元数据。结论是原兼容 frame(w,mode,z,P,A,b,z,b,R,S)。

InstantiateTopTermOperation 的 program_iff、coded_iff 与 guarded_coded_iff 将实际根接上此前全内部纯项定理。guarded 最终接口为：

```text
Ω(w), Num2(mode), empty(z), instantiateCoded(w,z,b,A,P,R,S)
  ⊢ [Term(w,A,b,n) ∧ Run1(w,mode,z,P,n,q)]
       ↔ CodedMixedSubst(w,R,S,A,b,z,b,n,q)
```

该端点不要求 frame、元数据、变量兼容性、候选输出自然性、历史、IH 或 Promise；源类型在结论内部。实际两张码表仍为明确的实际环境前提。本批尚未在最终根操作中构造并消去该码表对，也未完成全公式递归；不能将该项定理称为完整 InstantiateTop 正确性。

ObjectInstantiateRoot 的9组源闭句经 TheoryTransport.sentence、ZFReplay.replay 返回原 FirstOrder.Derives nativeZF []。CheckStep4 含各组闭句及展开的 guarded 根接口。原接受定义、原规格 AST 与此前全部 PPAC 证明文件保持 Git 字节一致，仅新增证明模块与四个接入文件。

## 实际验收与空间处理

| 验收项 | 结果 |
|---|---|
| 新模块／显式声明／闭句 | 5／49／9组 |
| 定向原核模块构建 | 1328项任务，通过 |
| 全仓构建 | 1789项任务，通过 |
| 声明审计 | 19155：400无公理、18755允许依赖；零警告 |
| 检查命令 | 9条全部退出0，含5个trust=0入口 |
| 独立哈希 | 1624份一致 |
| 精确core/native足迹 | 2218对一致 |
| Internal显式覆盖 | 16811项 |
| 上游及锁文件 | 固定039c8e132cc19671d73a3933c66b4799d2599dd6，上游干净，7锁不变 |

core证书依赖恰为propext、Classical.choice、Quot.sound；native侧另含上游锁定的7项证书依赖。未新增对象公理或改变信任基线。

前批已按用户要求清理247个确认无用的未跟踪临时文件，未发现失效进程，逻辑删除1091989字节；源码、证据和编译缓存保留。本批开始时C盘为零可用，首次Lake写缓存失败；改用不输出缓存的直接trust=0检查完成源推导修复。随后实测约26MiB可用，再串行生成缓存、完成9组原核闭句与全仓验收。compact显示压缩标记及退出0仍不代表节省空间；实测没有收益，不计入清理成果。未清理其他项目或应用。

证据：verification/mode2-root-readback.json、summary.json、commands.json；定向日志.local/mode2-root-native-directed.log。复验：`C:/Python314/python.exe -X utf8 scripts/verify.py`。验收前基点eb6dea65fe71c18cb3a1ea00a83c8cd7938ddc7a；提交后独立回读记录accepted_commit。

## 后续实现顺序

| 顺序 | 实现 | 必须达到的对象接口 |
|---|---|---|
| 1 | mode2真实binder框架闭包 | 真实提升表；独立源／目标后继及深度几何；新零／旧bound后继／free逐点兼容；原两层各4个EX全部消去 |
| 2 | 任意深度项纤维、列表和完整公式 | 真实内部历史、全部构造子及原ZF集合归纳消去IH；不是假设递归正确性 |
| 3 | 实际InstantiateTop完整操作 | 真实根、两码表对构造和消去、源类型位于结论内部 |
| 4 | 原逻辑／理论模式与Proof_ZF/U | 六规则／27模式、完整Separation／Collection、全部内部ω检查／编译与传输 |
| 5 | 内部解释及最终Con | 原核内ZF、PP、ACwo、¬AC解释和Derives nativeZF [] (Con_ZF→Con_target)；仍未证明 |

binder下一步可利用本批参数保持引理，结合源长度succ(depth)排除越过阈值的合法变量。真实source/target后继必须由对象唯一性对齐，不假设它们预先相同。
