# 原纯语法编码桥与 quotation 模式验收

2026-10-23；分支 migration/yesmeta-step3；本批基点 1de7eb0a1dcfbfd28bc54bb6ddd71e270f9a8cfa。
完成 S3.4c.2a.1：显式纯签名编码桥、原树操作的严格 AST 交换，以及紧凑 quotation 模式的实际内部码总唯一。
这些是后续内部编码对应的前置；全内部公式码上的原操作正确性及最终 Con 推导仍未完成。

## 固定目标与层次

对象语言仍为原单排序纯等词/成员语言 ℒ，背景为原 nativeZF 完整 Collection 呈现。
完整源 Replacement 已经对象互导接入。目标仍是 ZF+PP+ACwo+¬AC。
最终要求原 FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，
其中 Con_T := ¬∃p(p∈ω ∧ Proof_T(p,code(⊥)))，遍历全部内部 ω 证明码，保留原六规则、27模式和完整 Separation/Collection。
专用 ProofZF/U 有限纯 AST、全内部检查/编译正确性、完整内部解释和最终主句仍待实现；不能由本批审计数或编译成功推断完成。

## 显式编码桥：宿主语法中间引理

PureSyntaxQuotation 明确定义纯 SetSort 到扩展 BasicSetTheory.SetSort 的上下文映射和变量嵌入。
变量 here 的索引严格为0，there严格递增；纯语言的函数符号分支由 Empty 消去，未增加常元或应用项。
termTree、argumentTrees、formulaTree 与未修改原 SyntaxEncode 在显式嵌入后的结果逐项严格相等。
成员关系编号保持0；两个常量、原子、否定、四种二元联结词及两类量词完整保留。
这只是在代码中证明两个语法表示的相等，并未把扩展 BasicSetTheory 当作对象背景理论。

PureSyntaxOperations 直接调用固定原 SyntaxSubstitution.term/formula/shift/lift，证明：

- 原树的项和公式统一替换与类型安全纯语法的 substituteMapped 严格交换。
- shift 对应纯项 weakenBound；量词下同时更新 bound/free 两类像。
- instantiateTree 是原通用 formula 操作的首 bound 槽特化，严格对应原 instantiateTop。
- 原 abstractTop 严格对应纯语法 abstractFreeTop。
- 既有源 Fin.last/native 列表头的 instantiate 与 fresh_abstract 桥，进一步与该原树编码严格交换。

这些等式覆盖任意外部有限语法及任意嵌套深度，是宿主语法中间成果；它们不等于对任意内部非标准公式码的对象操作正确性。

## 紧凑纯 quotation：实际对象推导

OriginalTreeQuotationSyntax 以原 NatPacket.Tree 的树形作为外部有限公式索引，而非采用其字节传输码。
所有标签对象、子码、森林码和根码均在纯成员公式的存在量词内构造。
用 R 表示已证明的原 raw_node 关系、Nil/Cons 表示已证明的原 structural_list_code 关系，其有限模式为：

```text
TreeQ(node(k,children),w,n) :=
  ∃p∃t (Numeral(k,t) ∧ (ForestQ(children,w,p) ∧ R(w,t,p,n))).
ForestQ([],w,n) := Nil(w,n).
ForestQ(head::tail,w,n) :=
  ∃h∃t (TreeQ(head,w,h) ∧ (ForestQ(tail,w,t) ∧ Cons(w,h,t,n))).
```

R 精确保留后继 Gödel 配数；Nil/Cons 保留原结构列表的两层配数次序。
因此使用的是固定 IntrinsicQuotation.treeValue/forestValue 的递归编码约定，无需展开巨大根码的宿主一元 numeral。
本批没有加入新的对象编码谓词公理。

实际证明每个外部树/森林模式的内部自然码存在、输出自然范围、任意两候选相等、唯一输出公式及实际唯一码纤维。
存在证明在对象逻辑中逐层取得并消去子码、标签及根码；唯一性先用对象等词对齐子码，再使用原配数及结构节点唯一性。
没有从 Lean 中选择实际集合见证，也没有要求调用者提供待证的递归总性。
PureQuotationSyntax 把这一对象模式接到纯项/公式，并严格对齐显式嵌入后的原 SyntaxEncode 树形。

18组闭句模式均给出 Source.Derives、原 sourceZF 像核证书及原 nativeZF 核证书。
最终证书实际返回 FirstOrder.Derives nativeZF []；外部树/语法只索引有限对象句子，每个实例内部量化所有候选码。
**这不是一条量化所有内部树/公式码的统一真值或操作正确性定理。**
尚需证明 quotation 字段与现有 constructor/Term/FormulaCode 作用域的对应，再将原数值操作与 MixedSubst/首槽判断连接。

## 真实验收

执行 `C:/Python314/python.exe -X utf8 scripts/verify.py`，随后独立回读全部源哈希、公理依赖、闭句模式对及锁文件。

- 1082个构建任务；12021项审计，325项无公理依赖、11696项仅记录内允许依赖；0警告。
- 九条验收命令全部退出0，五个 `--trust=0` 入口全部退出0。
- 本批9模块144显式声明，其中115项Internal、29项宿主语法；18组新闭句。
- 累计9677项Internal显式声明全覆盖；980份独立源哈希一致，1262对核心/native精确证书足迹匹配。
- 每组核心精确std3，native精确std3加原七项固定句子证书；选择桥隔离边界不变。
- 两条 source_instantiate/source_fresh_abstract 的Prop等式桥继承既有 Syntax 桥的std3足迹，按具体名称分类并独立核对；另外27项新宿主声明不含Classical.choice。
- 七份可信基/规则/理论/工具链锁不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。

未推送、未建PR；辅助生成器、失败排错日志及独立回读留在本地忽略目录。
原 OpenAI 全构建与 Comparator 未运行。原操作全内部数值对应、ProofZF/U及Con总门均保持未完成。

## 后续工程流程

| 单元 | 输入/依赖 | 必须交付与验收 | 状态 |
|---|---|---|---|
| S3.4c.1 | 实际混合环境及首槽表 | 全内部首槽公式判断实际总唯一、准确输入/纤维双条件、11端点 | 已验收 |
| S3.4c.2a.1 | 原SyntaxEncode/SyntaxSubstitution、原结构码 | 显式纯签名桥、严格宿主AST交换；每个有限quotation模式的实际内部唯一自然码及原核闭句 | 本批已验收 |
| S3.4c.2a.2 | 本批TreeQ/ForestQ、原constructor字段 | 给定子quotation码时的准确森林/构造器双条件；纯项/公式quotation的Term/FormulaCode及实际作用域证书 | 下一步 |
| S3.4c.2b | 字段/作用域接口、实际双表binder | 原操作数值quotation与MixedSubst/首槽判断对应，嵌套binder保护；原任意内部码正确性不能由宿主等式替代 | 待完成 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree | 原数值对应及规则5/4的任意内部码检查兼容 | 待完成 |
| 5a | 原六规则、27模式和完整ZF/U公理 | 专用ProofZF/U有限纯AST；精确原标量/列表元数据，0合法和域检查准确 | 待完成 |
| 5b | 内部语法操作和内部编译器 | 全内部ω码上的检查/编译正确性，完整Separation/Collection | 待完成 |
| 6a | 原迁移数学路线、内部递归及完整ZF | 完整内部解释，包括所需可构造/对称强迫设施及目标公理、PP、ACwo、¬AC的原核证书 | 待完成 |
| 6b | 完整内部解释、证明检查和锁定Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

本路线固定原内在11构造树的结构数值格式；NatPacket字节传输、旧quote_hilbert六结构/末自由槽是分开的接口，本路线未消费它们的对象理论定理。
只在实际使用另一接口时才需要相应转换证明，不另行强迫实现未使用的编码转换。
对象Con仍为最终验收终点，当前前置不代表迁移已完成。
