# 原 1–11 阶段迁移流程（2026-11-08）

当前为原第10阶段。最终目标是普通 nativeZF 原推导核中的对象句
`Con_ZF → Con_(ZF+PP+ACwo+¬AC)`；Con覆盖全部内部及非标准证明码。
本流程不新增阶段；历史批次及旧状态由Git和逐批验收报告保留。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 已完成：42492087042／128788060157的官方Comparator实际接受，78输入不变、默认核通过，仅标准三项；真实Linux/landrun守卫也通过。原4.34.1与目标4.33.1继续隔离；见verification/original-comparator-acceptance.json |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。第 8 的具体单子已实际构造；剩余消费者为 9–10 的模型应用与全局目标装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 的原核存在句现已提供实际具体构造；第 9 消费这些父输入。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、完整实际饱和历史／转移／最终行、理想／基数、纤维／粘合、标签／传输、完整选择器／轨道／记录族和 Assigned 图已验收；具体商双射及完整 nonwellorderable_quotient_bijection 已验收；ForcingConcreteSystem 的无参数原核存在句实际构造全部 37 原始条件／40 内部集合，并在同一见证上消费全称商结论 | 本阶段所列全局装配门已完成；第 9 阶段消费同一具体系统，不重建原基础 |
| 9 | 源模型应用 | 同一实际Core、ACwo、¬AC、ordinal_presentation、完整切片／候选族／assemble及presentation_reverse_injection均已接通；全集合reverse_injection_dense及实际forces_PP有普通nativeZF原核L相对化端点 | 本阶段模型应用链完成；PP前没有给定稠密性、满射或HS名字前提；保留全部内部量词 |
| 10 | 原 Main 全局装配与对象内部化 | 同一实际系统的源目标理论及reverse_injection_dense→forces_PP→forces_target已接通；原公理行和完整模式流水线的存在、闭类型、独立见证唯一性已证明；实际ZF/U完整公理表的统一闭类型现由原六规则theoryShape有界查询消费；本批原正文→实际编译／三个原重命名矩阵→原模板→整个闭包→准确原生Separation/Collection句的quotation对象双条件已全部接通，五个普通nativeZF原核端点通过。正文／次数仍为外部模式索引，原始有效输入guard保留；同一实际内部Con及精确reduction现已组装，原核reduction→goal逻辑封闭门已验收；实际完整公理查询到同一理论原node/root证明的内部生产基例已构造 | 统一内部／非标准ZF/U公理正确性／强迫、全部内部六规则Proof及矛盾码归约、最终内部Con蕴含。标准quotation模式不替代此门 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## 当前 agent 执行入口

| 已有输入 | 当前消费者 | 真正的验收门 |
|---|---|---|
| 原完整raw模式码流水线及准确原生模式句quotation，已有原核双条件 | ZF/U统一内部公理正确性／强迫 | 覆盖任意内部／非标准正文和参数；原完整标准quotation、三个矩阵、模板、整个闭包及存在／类型／唯一性均已完成，不重做 |
| 现有六节点、27逻辑模式、语法操作、证明树和Proof/Sat配套 | 全内部及非标准证明码归约 | 不限外部标准码；不另建通用核、编码器或满足关系 |
| 全部源数学应用和上述内部传输 | 最终对象Con蕴含 | `FirstOrder.Derives nativeZF []`的原核闭句；最终主句仍未证明 |
| 原4.34.1 Main、五端点与官方Comparator均已通过 | 原第11最终源对应复核 | 原第4已完成，不再列作缺口；当前最终对象Con仍未证明 |

当前只推进统一内部／非标准ZF/U公理正确性与全内部Proof/Con。原Project翻译／重命名交换、三个实际编译矩阵及原正文到完整模式句的标准quotation链本批均已接通。复用现成ObjectProofNode、ReducedProofPresentation、PureProvability/PureSourceLocalTests和同一原强迫解释；不重建L、数学公理模式、满足关系或证明核。

## 工程执行约定

- 权威当前状态见STATUS；最新本批报告为`verification/internal-axiom-proof-acceptance.json`。
- 对象语言、背景和内部Con规格见OBJECT_TARGET；不得把外部模式索引误当统一内部真值断言。
- 固定源和供体哈希见SOURCE_LOCK；原4.34.1与目标4.33.1隔离。Lean/Lake串行。
- 每批先完成源码／跨平台检查及九条完整验收命令，保留五条trust=0门；再统一提交；等待上一批远端CI终态成功并读实际日志后才推送下一批。本地完整通过不冒充Linux干净环境通过。
- 不重启退役Packet／reader或反射实现，不重造L、全公理模式、通用算术、递归、Proof/Sat；不以行数、构建或审计数量代替最终证明。

原第10当前执行点：ForcingAtomicCode已构造原子分支的全部内部编码见证和准确类型，输入绑定范围可内部非标准、源自由范围为零、R为固定外部模板。下一消费者为原完整强迫解释的递归公式代码编译，不得把此分支当作全公式／全部Proof或Con已完成；继续复用现有内部递归、原11构造子与混合替换，不能另建通用语法核。

原子分支现在还提供独立实际见证下的对象单值性及带类型唯一输出，满足后续集合值递归的该项确定性要求；原总性输入范围不变。继续原第10的全公式／内部Proof归约，不新增阶段或语法后端。

原第10新消费者：ForcingAtomCode直接解析实际四种原子公式码，取得准确类型及独立见证下的唯一输出；真常量的原toBasic规范化有单列原核证书。下一门仍是逻辑／binder递归及全部内部Proof归约，不把原子入口当作全公式解释。

CI故障先定位再修复：42483548594主线成功，Comparator尚未开始就被ABI要求拦截。修复后的快速Linux守卫预检先于长构建。上一轮失败时，先读日志并修复，经本地完整验收后只推送包含修复的合并批次；不得重跑同一未修复错误或连续推送其他批次。正常批次继续等待上一轮成功终态和实际日志。

原第10当前新增操作：ForcingConditionRebind在普通nativeZF内为任意内部合法公式码／范围构造准确的条件变量重绑定，全部实际head／表／编码列表／替换见证均在对象EX内消去，结果有类型且不依赖执行见证。它对应原Force否定／存在分支；下一消费者仍为逻辑／binder完整递归，不是最终Con。验收见verification/forcing-condition-rebind-acceptance.json。

原第10的字面守卫代码：ForcingGuardCode已构造q∈P／R(q,p)模板的内部带类型唯一输出，允许内部非标准绑定范围和候选；自由范围为固定R参数数目加P/p的对象numeral。bound_guards_total在同一对象EX内构造bvar0和两个守卫，negative_inputs_kernel_certificate实际消费ForcingConditionRebind的子码重绑定。旧原子证明正文不变，仅新增八个直接调用旧证明的复用端口。守卫模块本身不提供外层公式；否定分支的完整码构造现由ForcingNegCode接通。完整存在分支现由ForcingExistCode接通；全递归、统一公理强迫及Proof/Con归约仍未完成。验收见verification/forcing-guard-code-acceptance.json。

原第10的完整否定码分支：ForcingNegCode实际构造子码重绑定、同一新条件的两守卫、falsum、三次imp和forall，取得普通nativeZF原核带类型唯一输出及独立执行唯一性。子码与绑定范围可内部非标准；R和参数数目为固定外部模式，条件free槽严格为对象numeral(n+1)。本项不再列为待做；完整存在分支现由ForcingExistCode接通；原始全构造递归、统一内部公理强迫及全部Proof/Con归约仍未完成。验收见verification/forcing-neg-code-acceptance.json。

原第10存在分支的守卫复用：ForcingExistGuardsCode用已有守卫编译器构造域谓词H(x)，原AST等式证明它是关系模板的特例；用逆序关系守卫加实际重绑定构造方向准确的R(r0,q1)，取得内部带类型唯一输出。没有第二套模板后端。新名字head也在对象EX内构造。子码binder重排现已由ForcingExistChildCode接通；完整外层exists码现已由ForcingExistCode接通；全递归／Proof／Con归约仍未完成；不再把H模板或内部守卫方向列作缺口。验收见verification/forcing-exist-guards-code-acceptance.json。

原第4最终接受证据已于2026-11-09读回：官方日志含“Lean default kernel accepts the solution”和“Your solution is okay!”；退出码0，78输入哈希不变，固定工具／三项公理／nanoda=false均与原锁一致。五份原始工件及哈希清单已归档并纳入源码预检；不再重跑此未修改的已完成基线。对象Con终点仍未完成。

原第10存在子码重排：ForcingExistChildCode从已解释子码的A=a+1作用域实际构造到C=a+3的完整混合替换，复用两次位移、项像推送、指定free槽图、原binder提升及编码列表。名字0保持方程和条件槽后继重命名方程均在同一对象EX记录中实际证明；12见证独立执行唯一性和准确类型已有普通nativeZF端点。全部范围／候选允许内部非标准，未给定任何输出或执行。完整外层exists现已由ForcingExistCode接通；全递归／统一公理强迫／Proof／Con仍未完成。验收见verification/forcing-exist-child-code-acceptance.json。

原第10完整存在码分支：ForcingExistCode实际消费上述既有head／守卫／子码搬移，构造三次AND、两次EX、两次IMP和最外层ALL。源子码在A=a+1，输出在a；内层顺序严格为R(r,q)，新名字0、条件r1与q2保留。所有执行在对象EX内产生，独立执行的带类型输出唯一；R/H为固定外部模板，子码和绑定范围允许内部非标准。普通nativeZF原核端点及完整九项验收均已通过；五项trust=0、零警告，旧证明正文和全部38270项足迹不变，见verification/forcing-exist-code-acceptance.json。完整原始递归、统一内部公理强迫及全部Proof/Con归约仍是未完成门。

原第10的其余原生逻辑操作：ForcingLogicalCode按固定源toBasic规范化接通AND／OR／IMP／IFF及ALL；OR=NEG(AND(NEG左,NEG右))，IMP=NEG(AND(左,NEG右))，IFF为两方向IMP的AND，ALL=NEG(EX(NEG子式))。全部中间码在对象EX内实际生成，输出有准确类型且独立执行唯一；四个普通nativeZF原核端点及完整九项验收均已通过，五项trust=0、零警告；旧证明正文和全部38283项既有足迹不变。已有原子／NEG／EX与本项共同提供全部11种原生构造所需的局部操作；完整原始递归、统一内部公理强迫、全六规则Proof和最终Con仍未完成。实际验收见verification/forcing-logical-code-acceptance.json。

原第10完整原始码单步调度：ForcingCodeStep用原FormulaCodeRecursive／CaseLogic对全部11种原生构造分类，实际消去源码字段，读取同一历史图内编码的(scope,output)状态，并调用已验收原子／NEG／EX／逻辑操作。源／目标准确类型、真实状态码存在、历史读取引入及同状态字段恢复均已证明。闭包端点明确保留对象available前提：对所有严格较小的合法子码及所有内部绑定范围，历史提供结果；该单步端点本身保留前提，ForcingCodeTotal现已用内部归纳为实际历史消去此项。源free范围为内部空零，绑定范围及码允许非标准；全部开放六规则证明仍需现成混合替换／闭包路径接入。两个原核端点与九项完整验收均已通过，五项trust=0、零警告；旧证明正文和全部38303项既有足迹不变，见verification/forcing-code-step-acceptance.json。实际递归的带类型结果存在性现已由ForcingCodeTotal接通；结果唯一性、统一内部公理强迫和最终Con仍未完成。

原第10实际forcing码递归：ForcingCodeRecursion以同一ForcingCodeStep、实际(scope,output)状态及内部后继链定义具体行，调用原Separation取得准确状态集合，再直接消费原ObjectTransfiniteRecursion及Compatibility／Restriction取得全部内部序数上的实际唯一历史。父图真边／历史读取与子索引自己的递归求值／解释已双向对应，输出FormulaCode类型已证明；五个普通nativeZF原核端点及完整九项验收均已通过，五项trust=0、零警告；旧证明正文及全部38339项既有足迹不变。表存在唯一不代表合法行非空或公式输出唯一；合法行非空的内部码归纳现已由ForcingCodeTotal完成；公式输出唯一性、全部开放六规则Proof及最终Con仍未完成。完整验收见verification/forcing-code-recursion-acceptance.json。

原第10全内部码实际总性：ForcingCodeTotal复用原成员归纳，在同一ForcingCodeRecursion.compiled关系上为每个合法源码构造带类型输出，并为实际父历史消去ForcingCodeStep.available前提。历史／值集合、三个后继作用域、状态及输出均在对象EX内生成，没有给定输出或外部标准性。源free范围为内部空零，任意内部／非标准绑定范围及码均覆盖；目标f/j为固定R/H的对象numeral。两个普通nativeZF原核端点及完整九项验收均已通过，五项trust=0、零警告；旧证明正文和全部38381项既有足迹不变。此项不再列为缺口；公式输出唯一性、统一内部公理／Proof正确性、全部开放六规则证明与最终Con仍未完成。完整验收见verification/forcing-code-total-acceptance.json。

原第10实际解释器唯一性：ForcingCodeStepUnique用原字段注入及标签排斥接通全11构造的一步确定性；ForcingCodeUnique由实际历史／状态／后继唯一性恢复同一步，再用原BoundedInduction对全部内部ω消去更小子码读取功能性。同一现有compiled关系中的两个独立输出相等，且与已有总性／类型合成对象存在唯一带类型输出；没有给定历史、输出、执行或标准性。九项完整验收和五项trust=0全部通过，38410项声明、零警告，全部38392项既有足迹及旧证明正文不变；见verification/forcing-code-unique-acceptance.json。公式输出唯一性不再列为缺口；统一内部公理／Proof正确性、开放六规则传输、同一reduction及最终Con仍未证明。

原第10开放节点代码生产：ForcingOpenCode复用原变量表与混合替换，把fvar i送到bvar i，再消费原内部forallClosure和已验收的实际解释器。任意内部／非标准自由范围b及开放源码均有唯一、准确类型的闭包强迫码；两张变量图、两份列表码、重命名公式、整个闭包和最终输出全部在对象量词内生成，无给定环境或执行。未修改既有替换、闭包、解释器或证明核。此项仅完成六规则消费者所需的代码生产；统一六规则保真、公理／语义正确性、reduction与最终Con仍未证明。九项完整验收和五项trust=0均通过，38434项审计零警告，全部38410项既有足迹及旧证明正文不变；验收见verification/forcing-open-code-acceptance.json。

原第10实际MP证明码生产：InternalMPProof直接消费两个实际子Node、原free／结论字段、完整两公式类型和原tag7蕴含码，构造原tag2四字段父载荷，接通原六项MP查询、两个实际递归子证明及原Node轨迹。任意内部／非标准free范围和证明码均覆盖；输出保留可组合头字段，自由范围为空时实际构造同一Root轨迹；相同输入的父载荷唯一。原泛型证明树、局部表与根构造全部复用，未建立新核。这是目标证明码MP构造器，不是强迫解释的MP保真桥；该桥、其他解释规则、统一公理正确性、reduction及最终Con仍未证明。九项完整验收和五项trust=0通过，38446项审计零警告，全部38434项既有足迹及旧证明正文不变；见verification/internal-mp-proof-acceptance.json。

原第10目标证明码操作：InternalProofOperations复用原完整27类逻辑查询、AbstractFreeTop、WeakenFree及任意参数列表mode3替换，实际构造逻辑／forall／strengthening／substitution四类父载荷、完整局部查询、实际Node与原头字段，并在free为空时构造Root。全部内部／非标准范围和证明码均保留；没有给定父证明或新增检查器／推导核。结合既有axiom和MP，六类目标证明码构造器齐备，但强迫解释六规则保真、统一公理正确性、reduction及最终Con仍未证明。九项完整验收和五项trust=0通过，38473项审计零警告；全部38446项既有足迹及旧证明正文不变，12项兼容回归和三库来源预检通过。见verification/internal-proof-operations-acceptance.json；等待前一整轮远端CI成功后再上传。

原第10内部合取证明组合：InternalProofConjunction以原rule11完整头、两项实际语法查询及27模式表生成逻辑证明，再调用两次真实MP。从任意内部／非标准A、B及其实际证明出发，合取公式、两个蕴含公式、证书／查询行和全部父证明均在对象EX内构造，不给定逻辑测试或中间结果。原free字段和空free时Root保留；已直接消费ForcingLogicalCode.binary 0的实际AND编译输出，子式类型从同一输出的完整FormulaCode内取得；原forceFormula_conj的这一代码级合取证明组合已接通。单调性／稠密性归纳仍须完成其余分支。强迫规则保真、统一内部公理正确性、reduction及最终Con仍未完成。九项完整验收及五项trust=0通过，零警告；全部38473项既有声明足迹和旧证明正文不变。12项兼容回归和三库来源预检通过。验收见verification/internal-proof-conjunction-acceptance.json。
