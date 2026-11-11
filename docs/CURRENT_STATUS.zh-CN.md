# 当前工作入口（2026-11-12）

当前为原1–11规划的第10阶段；第11阶段未开始。阶段表见[AGENT_WORKFLOW](AGENT_WORKFLOW.zh-CN.md)，对象规格见[OBJECT_TARGET](OBJECT_TARGET.zh-CN.md)。历史逐批验收保存在Git和不可改写的验收报告；旧报告中的待办不代表当前缺口。

最终目标仍是纯集合语言／普通nativeZF中原推导核的 `FirstOrder.Derives nativeZF [] InternalConsistency.goal`。`goal`准确为 `nativeCon false → nativeCon true`，目标理论为ZF+PP+ACwo+¬AC；Con覆盖全部内部／非标准ω证明码、完整公理测试及原六规则Root。最终主句与reduction尚未证明，`closing_kernel_certificate`只证明`reduction → goal`。

## 最新实际验收

原 `exists_force_neg` 的内层反证已从配对的实际开式推出三项字段等式。同一条件 `r` 的成员守卫读取同一载体字段，顺序守卫归到原关系 `r ≤ q`，强迫查询通过原绑定前缀和条件替换归到同一输入。`paired_density_openings_kernel_certificate` 在普通 nativeZF 原核中从密度尾式的反面导出否定强迫全称式。外层仍需产生配对开式和所选 `q` 更新，构造并闭合反强迫见证。[整仓验收](../verification/forcing-paired-density-openings-acceptance.json)

原 `exists_force_neg` 的内层反证已接到真实开式。`negative_from_density_openings` 消费同一个新鲜条件处的原密度尾式、原否定编译和三项字段等式。它把旧背景下对密度尾式的反证提升到同一开式，再闭合出否定强迫全称式。已有普通 nativeZF 原核证书。三项字段等式仍需从共同运行记录产生，外层反强迫见证仍待闭合。[整仓验收](../verification/forcing-rejected-density-openings-acceptance.json)

OpenAI 原 `exists_force_neg` 所需的密度蕴含已在对象层取得。`ForcingSourceDensity.dense_implies_force` 对实际编译与替换所得的查询生成 `Dense → Force` 的 Root 证明码，使用同一偏序与替换表，并回到原共同背景。`density_implication_kernel_certificate` 给出普通 nativeZF 原核闭句。原定理的反强迫条件见证尚待接入。[整仓验收](../verification/forcing-density-implication-acceptance.json)

OpenAI 原 `force_of_dense` 的完整对象层归纳已闭合。`ForcingSourceDensity.at_code` 在现有共同强迫运行条件下覆盖任意内部合法公式码及其实际编译输出，原编译器中析取、蕴含、双条件及全称式的规范化记录已接入同一归纳。`density_kernel_certificate` 在 `FirstOrder.Derives nativeZF []` 中给出对应闭句。接下来消费该结论迁移原 `exists_force_neg`、`forceFormula_imp` 和强迫 MP。[整仓验收](../verification/forcing-source-density-induction-acceptance.json)

OpenAI 的 `force_of_dense.ex` 已接入原密度归纳谓词。`ForcingSourceDensity.existential_at_condition` 用同一见证 `s` 重组 `q` 处的目标存在式，并消去两次源存在量词。`existential_step_from_runtime` 从实际编译记录闭合原外层守卫和全称式。`existential_kernel_certificate` 在 `FirstOrder.Derives nativeZF []` 中给出对应闭句。完整密度归纳和最终内部 Con 仍待完成。[整仓验收](../verification/forcing-existential-density-branch-acceptance.json)

`ForcingSourceDensity.with_existential_witnesses` 已在实际第二次开式的局部背景中推导 `s ≤ q`。同一背景下取得原名字存在子式的证明。`q` 处目标尾式保留原代码的弱化和同一实际替换查询。原 `force_of_dense.ex` 仍需将该名字存在子式接到 `q` 处的目标构造，并闭合原量词。[整仓验收](../verification/forcing-existential-density-local-transitive-acceptance.json)

`ForcingSourceDensity.with_existential_witnesses` 已将实际第二次开式的成员守卫与 `s ≤ r` 查询对齐到同一偏序行。开式直接复用行的弱化映射和选中列，保留原名字存在子式。原 `force_of_dense.ex` 仍需将传递性推导放入实际见证背景，再保留同一名字见证闭合原量词。[整仓验收](../verification/forcing-existential-density-actual-guards-acceptance.json)

`ForcingSourceDensity.with_existential_witnesses` 已在同一偏序行的 `s` 处打开第二个存在式。其开式保留实际成员、顺序及名字存在子式。原核传递性从该行的背景得到 `s ≤ q` 的代码化推导。原 `force_of_dense.ex` 仍需把开式守卫对齐到该行，传回实际局部背景，再保留同一名字见证闭合原量词。[整仓验收](../verification/forcing-existential-density-second-open-acceptance.json)

`ForcingSourceDensity.with_existential_witnesses` 已把原密度前提的见证 `r` 接到原存在式的反身实例。同一提升偏序提供第二次查询的实际存在尾式，以及包含 `s`、`r`、`q` 的下一层偏序行。原 `force_of_dense.ex` 仍需用开式中的顺序守卫推导 `s ≤ q`，保留同一名字见证并闭合原量词。[整仓验收](../verification/forcing-existential-density-joint-acceptance.json)

`ForcingDensityGuards.with_existential_at_reflexive` 用同一偏序把 `r` 处的原存在强迫式实例化于 `r ≤ r`，保留实际存在尾式的推导及条件、名字两层绑定器的开式记录。原否定分支复用提取出的见证偏序行和局部证明背景。原 `force_of_dense.ex` 仍需将两次见证查询接到同一运行记录，证明 `s ≤ q` 并闭合原量词。[整仓验收](../verification/forcing-existential-density-reflexive-acceptance.json)

`ForcingDensityInstantiation.with_existential_density_witness` 已在 nativeZF 推导中从原密度存在式取得实际见证 `r`、`r ≤ q` 和 `r` 处的原存在强迫式查询。反身实例化与见证消去复用原否定分支的证明。原 `force_of_dense.ex` 仍需在 `r ≤ r` 处取第二个见证，证明其到 `q` 的顺序并闭合原存在式。[整仓验收](../verification/forcing-existential-density-witness-acceptance.json)

`ForcingSourceDensity.negative_kernel_certificate` 已在普通 nativeZF 原核关闭 OpenAI 原 `force_of_dense.neg` 的分支句。它从统一运行记录投影继承的偏序证明，保持实际选中条件和密度见证的查询，量化原编译器的全部对应输出。第 10 阶段还需接完原 `ex`，再关闭完整密度归纳。[整仓验收](../verification/forcing-negative-density-runtime-acceptance.json)

`ForcingSourceDensity.negative_step_from_parent_opening` 接收原否定编译器和实际父式开式，逐一读取三个蕴含的查询。它用同一开式构造外层背景，在对象层反向消去三个假设并全称化，得到背景到原父式码的推导。第 10 阶段还需从统一运行记录提供外层选中条件的偏序证明，再接入原密度归纳谓词。[整仓验收](../verification/forcing-negative-density-outer-closure-acceptance.json)

`ForcingSourceDensity.with_negative_density_transfer` 已消去实际见证的存在量词。由见证背景下的假式，原 Curry 和全称规则生成同一正文的全称蕴含，再用原存在消去规则及实际密度前提，在原作用域推出 `H → ⊥`。仍需从原运行记录构造 `H` 的外层前提并闭合原全称式。[整仓验收](../verification/forcing-negative-density-existential-discharge-acceptance.json)

`ForcingSourceDensity.with_negative_density_transfer` 已消费同一见证处的正、负两条对象推导。它把实际全称否定在 `r` 处实例化，用同一偏序行证明成员守卫和 `r ≤ r`，再由 `ForcingRawNegTail.canonical_code` 确定否定实例中的操作数正是此前得到的 `r` 处正子式，最后以原 Root MP 得到局部背景下的假式。外层前提和量词闭合仍待完成。[整仓验收](../verification/forcing-negative-density-reflexive-contradiction-acceptance.json)

`ForcingSourceDensity.with_negative_density_transfer` 已从原密度开式接通实际见证的单调性回放。它保留同一自由名字表，仅重建偏序的空绑定列，用原 Root 替换规则弱化给定的外层偏序和 `q` 处正子式推导。在实际见证的同一个局部背景下，现可推出 `r` 处原编译的正、负子式。外层局部前提仍需从原运行记录装配，否定分支还需用 `r ≤ r` 消去守卫并完成量词闭合。[整仓验收](../verification/forcing-negative-density-actual-transfer-acceptance.json)

`ForcingDensityInstantiation.with_negative_witness_queries` 从原否定记录取得 `q` 的成员查询，并用实际见证表的重命名弱化查询和原 Root 推导。它生成 `Extra ∧ 见证正文` 的实际对象码，在同一局部背景下推出 `Extra`、`q` 和 `r` 的成员守卫、`r ≤ q` 及 `r` 处的否定子式。接通原单调性还需传递继承偏序和 `q` 处的正子式，随后用 `r ≤ r` 得出矛盾。[整仓验收](../verification/forcing-negative-density-actual-local-acceptance.json)

`ForcingSourceDensity.with_witness_monotonicity` 现在接收见证局部背景下的五条对象推导。它把同一实际偏序行的成员叶 `H1`、`H2` 和顺序叶 `H4` 对应到实际守卫，将继承的偏序查询归约为同一内部替换，并用原四个合取构造得到局部背景到单调性背景的推导。由此在局部背景下得到正子式在 `r` 处的证明。还需从实际打开的见证生成这五条推导，并以 `r ≤ r` 闭合否定分支。[整仓验收](../verification/forcing-negative-density-local-background-acceptance.json)

`ForcingSourceDensity.with_witness_monotonicity` 用原偏序生成器在见证作用域内产生两组实际行，再由原证明上下文构造器生成共同背景。它实际调用原任意内部码单调性归纳，消费给定的正子式证明及其在 `q`、`r` 处的查询，在生成的共同背景下推出 `r` 处的正子式。同一偏序行的 `H4` 已与实际 `r ≤ q` 守卫接通。仍需将见证分支的局部假设接入该背景并闭合自反矛盾。[整仓验收](../verification/forcing-negative-density-witness-monotonicity-acceptance.json)

`ForcingDensityGuards.witness_order_from_row` 消费实际密度见证的顺序守卫和单调性使用的原偏序行。两个查询通过现有内部替换分别归约到同一个裸关系查询，其中左参数为 `r`，右参数为 `q`，得到见证守卫与偏序行 `H4` 的对象码相等。仍需生成见证处的完整运行记录并将该守卫的证明放入共同背景，再传递正子式并以自反性闭合否定分支。[整仓验收](../verification/forcing-negative-density-preorder-leaf-acceptance.json)

`ForcingDensityInstantiation.with_negative_witness_queries` 现在同时交付实际见证的两个守卫。成员守卫在 `r` 处读取。顺序守卫使用实际前缀留下的 `q` 和已供强迫查询使用的 `r` 条件替换表，消去原重绑定后得到同一码的 `r ≤ q` 查询。仍需将这两个守卫与原单调性使用的偏序证明行接通，再完成同背景传递与自反矛盾。[整仓验收](../verification/forcing-negative-density-witness-guards-acceptance.json)

`ForcingDensityInstantiation.with_negative_witness_queries` 串联原否定分支与实际稠密存在式的两次打开，保留见证的成员、顺序守卫和原抽象。实际表头重命名确定弱化后的条件仍是 q。它在同一名字表上提供 q、r 两处的正子式查询及 r 处的否定公式查询，其中 r 处的正子式由现有对象层替换存在性定理生成。仍需在同一背景下用单调性传递证明并以自反性推出矛盾。[整仓验收](../verification/forcing-negative-density-witness-pair-acceptance.json)

`ForcingDensityInstantiation.with_same_name_queries` 从原稠密性记录取得实际见证 `r` 的否定正文查询，并把 `q` 处的正子式弱化到同一名字表。两个查询共享实际自由项基表，各自替换所选条件。该步骤复用原存在开式的重绑定查询及对象层弱化唯一性，后续需用原单调性和 `r≤r` 的原推导推出矛盾并闭合否定分支。[整仓验收](../verification/forcing-negative-density-direct-acceptance.json)

`ForcingDensityInstantiation.with_negative_density_tail` 在同一个新鲜条件下打开原否定正文和原稠密性前提，证明两条实际守卫码相等，并在给定当前背景中的守卫推导时消去它们，得到同一密度存在式的内部推导。`with_fresh_witness_records` 从该存在式的实际查询生成下一层自由作用域和见证项，保留两条内层守卫、重绑定正文及其原抽象。否定分支还需用原单调性和自反性在这个见证处推出矛盾，再闭合原否定公式。[整仓验收](../verification/forcing-negative-density-opening-acceptance.json)

`ForcingSourceDensity.atomic_step_from_runtime` 将成员和相等两条分支接入原 `atSource`。它从实际运行记录和原编译历史取得名字项、载体字段与现行查询，以完整前提码的等式传递同一背景下的内部推导。任意内部实际编译输出均受该归纳谓词量化，闭句由 `atomic_kernel_certificate` 在普通 nativeZF 原推导核重放。原否定与存在量化分支及最终内部 Con 仍需完成。[整仓验收](../verification/forcing-atomic-density-source-acceptance.json)

`ForcingAtomicDenseTemplate.compare_opened_density` 比较原编译前提与共同表上的两份实际展开查询。原子见证体的两个名字像来自同一原绑定表，所选条件由实际内层重绑定给出。两条成员守卫、两条顺序守卫和见证体的码等式经构造器唯一性合成整个稠密性前提的码等式。运行记录现已提供这些查询，前提码等式已用于原子稠密性证书。[整仓验收](../verification/forcing-atomic-density-witness-equality-acceptance.json)

`ForcingAtomicDenseTemplate.with_atomic_witness_query` 从原 `force_of_dense.mem/equal` 的实际密度记录取得见证体查询。在两次作用域提升后，它消去原弱化和条件重绑定，把同一输出码还原为对原强迫原子码的直接查询，保留原名字项和实际的内层条件。该查询已用于 `compare_shell_atomic_witness`。

`ForcingAtomicDenseTemplate.with_inner_order_query` 从原稠密性编译记录和两次实际提升得到内层顺序守卫的直接替换推导。外层条件对应绑定索引 1，内层条件对应绑定索引 0。内层守卫已与共同表上的实际输出得到码等式。[内层守卫码等式验收](../verification/forcing-atomic-density-inner-equality-acceptance.json) [本地验收](../verification/forcing-atomic-density-inner-order-acceptance.json)

`ForcingAtomicDenseTemplate.outer_order_query` 从原稠密性编译和实际外层提升表，导出同一顺序守卫输出的直接替换推导。该推导保留外层提升后的自由项表，并从同一次提升读取绑定的零号条件项。该直接推导已用于比较共同表上的外层顺序守卫，码等式由同一个零号绑定项和两张提升表上的自由项对应推出。[外层顺序守卫码等式验收](../verification/forcing-atomic-density-outer-equality-acceptance.json) [本地验收](../verification/forcing-atomic-density-outer-order-acceptance.json)

`ForcingAtomicDenseTemplate.compare_shell_members` 比较两份实际查询中的两个成员守卫。原条件表的载体项经共同表路由保留。两个绑定各自从实际提升表读取零号条件项，构造器唯一性给出同一对象码。[本地验收](../verification/forcing-atomic-density-members-acceptance.json)

`ForcingDensityInstantiation.with_mixed_shell` 从原密度前提的实际替换中读取两层提升表及五个子查询。`ForcingAtomicDenseTemplate.with_quoted_shell` 从原子稠密性证明的实际模板码取得同样的六个构造步骤。`raw_shell_eq` 用五个实际叶码的对象相等式推出完整前提码相等。两个成员守卫的结果见上文。[本地验收](../verification/forcing-atomic-density-shell-acceptance.json)

`ForcingDensityCode.with_atomic_rebound` 消费统一密度编译的实际见证体记录。在第一层绑定替换中，用实际名字项像和恒等自由项表重组原子编译。在第二层用同一运行记录的条件替换表，把最终见证体码读成对原成员／相等模板的直接查询。下一步是证明统一密度查询与已有原子稠密性证明在共同表上的完整前提码相等。[本地验收](../verification/forcing-atomic-density-rebound-acceptance.json)

`ForcingDensityGuards.kernel_certificate` 将当前条件实例的两个实际守卫码与同一条件、同一张表上的原守卫查询对齐。在给定两条守卫的内部证明时，它用原规则消去两层蕴含，得到同一个存在式尾部的证明。`member_from_proof` 已能将同一条件和载体的成员性证明传输到这个实例的成员守卫。新验收的 ForcingDensityGuards.tail_from_row 从同一背景 G 提取预序和所选条件成员性，沿原表更新保留载体字段。给定原自反性正文及两个原生子查询，它构造实际自反性实例，消去两个守卫并得到 G → 同一个存在式尾部。ForcingDensityGuards.with_reflexive_instances 已从原预序的实际编译记录取出同一自反性正文及两个子查询，并在所选条件处生成两项原生实例。ForcingDensityGuards.reflexive_member_agrees 已证明成员性实例码与实际密度成员守卫码相等。两者使用同一所选条件，且原条件槽更新保留载体字段。ForcingDensityGuards.reflexive_order_agrees 也已证明顺序实例码与实际密度顺序守卫码相等。ForcingDensityGuards.tail_from_compilers 从原编译记录构造两个守卫的证明并消去它们，得到 G → 同一个存在式尾部的内部证明。ForcingDensityGuards.falsum_from_density_records 从同一选定条件的编译及实例记录，把 G → 同一存在式尾部的内部证明变换成 G → 原 ⊥ 码的内部证明。该证明复用原绑定转换、全称化、第 24 条逻辑公理与 MP。整条原密度归纳及最终 Con 尚待装配。见[假常元见证消去验收](../verification/forcing-falsum-acceptance.json)。合取分支中，ForcingDensityCode.with_conjunct_compiler 从同一父代入记录取得两个子码，用原载体和顺序守卫构造所选子公式的密度编译记录。ForcingDensityGuards.conjunction_exists_from_witness 用实际开绑定和子式实例，将父存在式的见证传给左或右子公式。ForcingDensityGuards.conjunction_exists_from_compiler_shells 已从父、子实际编译记录的存在式尾部生成开绑定，用同一张弱化代入表证明两份前缀代入表相等，再用原见证和两个相同守卫构造父存在式到所选子存在式的内部证明。ForcingDensityGuards.with_conjunct_density_proof 已将外层全称稠密性前提传至任一实际子式，同时产生子式的原编译记录、同表代入结果和同一背景下的内部证明。ForcingSourceDensity.conjunction_step 从真实编译历史读取两个较小的源码，实例化两条对象归纳假设并用原合取规则生成同一背景下的结论。封闭推导已在 nativeZF 原核重放。见[源码合取归纳步验收](../verification/forcing-source-density-conjunction-acceptance.json)。见[外层全称传输验收](../verification/forcing-conjunction-outer-acceptance.json)、[实际存在式开绑定验收](../verification/forcing-conjunction-openings-acceptance.json)和[合取见证验收](../verification/forcing-conjunction-witness-acceptance.json)。见[顺序守卫及消去验收](../verification/forcing-reflexive-order-acceptance.json)。见[成员守卫验收](../verification/forcing-reflexive-member-acceptance.json)。见[自反性实例验收](../verification/forcing-reflexive-instances-acceptance.json)。见[本批验收](../verification/forcing-density-tail-acceptance.json)。见[守卫验收](../verification/forcing-density-guards-acceptance.json)。

`ForcingDensityInstantiation.kernel_certificate` 读取原稠密性公式的实际全称码，用同一张替换表的指定条件槽作为实例项。它生成 `G → 实例` 的原内部证明，并保留该实例中两个守卫和存在式尾部的精确查询。Windows 整仓验收已通过。两个守卫的原查询对应见上述证书。见[当前条件实例验收](../verification/forcing-density-instantiation-acceptance.json)。

`ForcingSourceDensityConstant.truth_kernel_certificate` 在普通 nativeZF 原核内，从原编译及实际混合查询取得真常元的内部 `G → 输出` 证明，允许任意内部自由作用域。`false_from_compiler` 在实际假常元查询上保留同一 `⊥` 码和原稠密性见证记录。ForcingSourceDensity.falsum_step 现已从同一原稠密性编译查询生成并接入这些记录。ForcingSourceDensity.falsum_step_from_runtime 已从现有运行记录读取同一预序的自反性查询和原表的载体字段，在实际条件消去两条守卫和存在式并推出准确的 ⊥ 输出。封闭推导已在 nativeZF 原核重放。见[假常元运行记录验收](../verification/forcing-source-density-falsum-runtime-acceptance.json)。ForcingSourceDensity.truth_step 也已接入同一对象归纳谓词。见[源码常元归纳步验收](../verification/forcing-source-density-constants-acceptance.json)。两项已通过 Windows 整仓验收。见[常元验收](../verification/forcing-constant-density-acceptance.json)。

`ForcingDensityCode.kernel_certificate` 在 nativeZF 原核中为任意内部强迫公式码构造原 `force_of_dense` 的稠密性前提。它插入两层条件绑定，只在见证正文中替换指定条件槽。`ForcingDensityCode.from_tables` 使用同一份实际替换表生成该前提的查询码。两项已随主入口通过 Windows 整仓验收。全内部公式码的稠密性推导尚未闭合。见[稠密性前提验收](../verification/forcing-density-code-acceptance.json)。

`ForcingSourceMonoInduction.kernel_certificate` 已通过模块级 `--trust=0`。它在原运行记录下，用对象 ω 成员归纳覆盖全部内部公式码，沿用原编译器各分支和两份实际替换。`ForcingAtomicDenseTemplate.kernel_certificate` 也已通过同一检查，覆盖成员与相等的稠密性分支，在对象层生成较旧条件查询和实际稠密性码，并推出当前条件的原子结果。两项均已通过 Windows 整仓验收，共 3,375 项构建任务、40,030 项声明，零警告。见[本批验收](../verification/forcing-source-mono-and-atomic-density-acceptance.json)。

`ForcingSourceMono.atomic_kernel_certificate` 在 nativeZF 原推导核中覆盖成员与相等分支。原递归编译器的同一实际输出分别在两张条件覆写表上查询。证明从原预序行读出 `Pre`、`q ∈ P`、`q ≤ p`，与两份原子查询共用一张项像表，再在 `oldCtx 3` 下消去四层蕴含。见[原子分支验收](../verification/forcing-atomic-source-induction-acceptance.json)。

`NativeProofQuotation.from_derives` 已把固定的 nativeZF 原推导按六条 Hilbert 规则回放到原证明码。成员和相等的单调性复用 `ForcingAtomicBasic` 的既有证明。实际混合替换给出同一内部项像表与输出码时，`atomic_monotone_kernel_certificate` 在 nativeZF 中产生该输出的原证明节点，并在自由作用域为空时给出 `Root`。见[验收报告](../verification/native-proof-quotation-acceptance.json)。

负式与存在式的原构造码已推出 `ForcingSourceMono.atSource`。两支调用原编译总性和 `ForcingCodeUnary.unary`，并从同一 `ForcingGlobalWeakening` 输入生成弱化布局和两份覆写记录。预序行保留其空绑定表，父式在任意内部作用域生成绑定列，两者共用原来的自由底表。源条件的两份替换判断仍是输入。见[源构造分支验收](../verification/forcing-modal-source-induction-acceptance.json)。

## 已完成，必须复用

`InternalAxiomProof.from_native_quotation` 已覆盖七条固定公理及每个标准外部索引的分离和收集实例。`InternalProofTemplates.from_logical_quotation` 已覆盖 27 类逻辑公理。`ForcingAtomCode.member_output/equal_output` 已从原分派记录恢复同一字段的实际原子编译记录。

- 原第1–9阶段已验收资产依原阶段表保留；包括原L于ZF解释及全公理模式、实际具体系统、Assigned商与第9阶段模型应用，不重新迁移或重建。
- 原完整negative/existential compiler、同一预序三次native实例／五IMP行、bare-R／member／domain／child查询对应、完整raw尾部两层EX及跨条件比较均已完成；ForcingExistTailComparison.from_queries/raw_kernel_certificate生成消去两次全部trace和canonical见证。
- ForcingProofContext生成六个实际上下文合取码，完成重排、只对r-local的Curry及实际raw尾部证明传输；ForcingProofUniversal生成同一Curry正文及实际原mode3抽象并消费guarded forall。
- ForcingScopeIdentity完成全内部独立作用域恒等与同一闭G提升；ForcingFreshBackground.derive从实际weakening产生消去十三见证并证明abstracted(W,G)，已消去全局抽象答案／类型前提。
- ForcingReindexedImages复用原TermImagePushBoth／图解码／编码，产生六个实际图及列表见证，复用已有完整公式相消；ForcingWeakenedImages进一步产生原首槽弱化码／真实索引图，推导两次实际源查询的原weakened对应并消费全称化。不得再把项像图、index realization、弱化／抽象相消或完整公式归纳列为待实现。

## 当前真正缺口与依赖顺序

1. 将已验收的成员与相等分支接到统一实际密度查询，接完原 `ForcingTruth.force_of_dense` 的负式和存在式分支，并在全部内部公式码上闭合归纳。复用已通过原核检查的原子稠密性证书和单调性归纳。
2. 按原源依赖完成 neg／imp 内部证明生成和实际规范化强迫MP；已有固定公式数学与模式证书继续复用，不能用宿主实例代替全部内部码。
3. 接通全部内部／非标准ZF/U公理实例与完整六规则Proof保真，证明同一矛盾码的InternalConsistency.reduction，再取得goal。外部固定正文quotation模式不能替代此门。
4. 所有最终对象主句、量词、依赖及固定源对应验收满足后进入原第11阶段终验。

## 当前可核验材料

- [已验收裸R／完整canonical Global与实际forall消费](../verification/forcing-global-weakening-acceptance.json)：39719项声明，零警告，九命令及五项trust=0通过。
- [上一批全内部项像／公式比较](../verification/forcing-reindexed-images-acceptance.json)及[首槽相消](../verification/forcing-fresh-background-acceptance.json)。
- [Linux CI实际完成回执](../verification/ci-proof-universal-remote-acceptance.json)：远端613a6f0，39573项声明、零警告；后续提交CI以实际作业终态为准。

- [原源码合取单调性归纳分支](../verification/forcing-conjunction-mono-acceptance.json)：39728项声明，零警告；子公式归纳假设未消去，整体mono／Con未证明。

- [源公式码常元基例及合取步骤](../verification/forcing-source-mono-acceptance.json)：39739项声明，零警告；指定运行框架上的源子归纳假设保留，整体mono／Con未证明。

- [原字面双守卫与实际mode3／forall消费](../verification/forcing-nested-guard-acceptance.json)：39751项声明，零警告；完整新父公式查询匹配仍未证明。

- [新鲜三操作逆向及实际嵌套Root消费](../verification/forcing-fresh-opening-inverse-acceptance.json)：39774项声明，零警告；完整raw父查询到所需实例化记录仍未完成。
