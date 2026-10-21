# 原语法标签、精确字段与内部变量构造验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点2e70976177ce8a75f712ad886f9a863a3590b1ee。
本批完成4c.a.i，提供语法类型检查所需的实际原码构造及严格子码界。
变量索引解码、纯项作用域、全部公式类型、内部替换、ProofZF/U和最终Con仍未完成。

## 对象合同

纯等词/成员语言及原ZF背景保持。全部数学结果为Source.Derives，
经TheoryTransport及ZFReplay取得原FirstOrder.Derives nativeZF []完整闭句证书。
不加对象AC、Con、外部标准ω假设或新推导核；固定底座和原公理/规则不改。
原编码严格保持treeValue(node(tag,children))=Pair(tag,forestValue(children))+1、原Nil/Cons及scalar叶封装。

外部有限k/tag索引生成有限对象公式，每个实例返回实际Derives证书。
这不是把外部索引变成内部统一真值谓词；数码候选、字段、原码及变量索引均为对象量词。
尤其Scalar和变量构造量化全部内部ω成员，涵盖内部非标准索引。

## 数码和精确字段

Num_0(x):=Empty(x)；Num_{k+1}(x):=∃p(Num_k(p)∧Succ(x,p))。
每个有限k实际存在唯一内部自然数码；外部i<j的两个数码满足实际严格成员关系。
不同有限数码不相等，证明使用实际后继、原Extensionality和Foundation，而非宿主数值测试代替对象证明。

Forest_0(w,xs,n)为原Nil；Forest_{k+1}实际存在尾码，
要求头字段属于ω、尾满足Forest_k及原Cons关系，保留给定有限字段顺序和准确的Nil终端。
任意给定的k个内部自然字段实际产生唯一原森林码；原码属于ω。
Num_k(l)下，真实HasLength(w,n,l)由原指定长度Nil/Cons构造正式推出。
每个给定字段严格属于原森林码；后续包装为raw节点后，每个字段严格属于父节点码。
这些定理不假设字段已经是有效公式或有效子树。

## 节点、scalar与标签构造器

Node_k(w,t,xs,n)实际存在原森林payload p，要求t∈w、Forest_k(w,xs,p)及原Raw(w,t,p,n)。
该节点实际存在唯一自然码。任何两个同码Node（字段数可不同）有相等标签。
Constructor_{k,tag}另实际存在Num_tag标签见证；每个给定有限tag/k和全部内部输入字段有唯一实际原码。
不同有限标签的构造器同码条件导出矛盾；各字段的严格子码界均已证明。

Scalar(w,i,n):=Node_0(w,i,[],n)。
对每个内部i∈ω，原ZF实际构造唯一scalar码；同一scalar码必有相同内部索引i。
scalar必须是零字段节点，索引值不是直接用作其父节点的字段码。

原变量模式为：
Var_bound(w,i,n):=∃s(Scalar(w,i,s)∧Constructor_{1,0}(w,[s],n))；
Var_free(w,i,n):=∃s(Scalar(w,i,s)∧Constructor_{1,1}(w,[s],n))。
两个模式对全部内部自然索引实际存在唯一原码，且bound/free两类在同一码处互斥。
当前变量唯一性方向是同一索引得到唯一编码；同一变量码反推出索引相等仍需字段反向解码证明。
scalar的反向单射已经完成，不能直接越过变量节点的单字段封装。

## 全部11种公式构造实例

固定标签/字段数沿用原SyntaxEncode公式构造顺序；CheckStep4逐一实例化实际构造唯一纤维。
下表最后一列为后续类型/作用域义务，当前未计作通过。

| 构造 | 标签 | 字段数 | 后续类型/作用域义务 |
|---|---:|---:|---|
| falsum | 0 | 0 | 公式空分支及原矛盾句码对应 |
| truth | 1 | 0 | 公式真分支 |
| membership relation | 2 | 3 | 首字段为编号0的scalar；后二字段为当前上下文中的纯项 |
| equal | 3 | 2 | 两个当前上下文纯项 |
| neg | 4 | 1 | 一个同上下文公式 |
| conj | 5 | 2 | 两个同上下文公式 |
| disj | 6 | 2 | 两个同上下文公式 |
| imp | 7 | 2 | 两个同上下文公式 |
| iff | 8 | 2 | 两个同上下文公式 |
| forall | 9 | 1 | 子公式在真实后继bound长度检查 |
| exists | 10 | 1 | 子公式在真实后继bound长度检查 |

纯签名无函数符号。bvar/fvar采用各自的标签0/1和单scalar字段；它们的编码与公式构造的标签复用，
完整类型检查还必须保留构造类别、字段类型与作用域，不能仅凭标签数值接受。
一般构造存在唯一也不等于未知标签或错字段已被类型检查器拒绝。

| 新模块 | 职责 |
|---|---|
| SyntaxNumeralSyntax/Numerals | 实际数码AST、存在唯一、自然范围、严格顺序和异数码互斥 |
| SyntaxForestSyntax/Forests/ForestLength | 精确有限字段、实际原码存在唯一、字段自然性/严格界及真实数码长度 |
| SyntaxNodeSyntax/Nodes/Constructors | 精确节点、scalar及有限标签的实际唯一纤维、标签和scalar单射、构造器互斥、父码严格界 |
| SyntaxVariableSyntax/Variables | 内部索引scalar包装、原bvar/fvar实际存在唯一和两类互斥 |
| ObjectSyntaxConstructors | 18个完整源ZF及原nativeZF闭句模式 |

18个端点为numeralExists、numeralUnique、numeralRange、numeralLess、numeralDifferent、
forestExists、forestUnique、forestMember、forestLength、nodeFiber、nodeMember、constructorFiber、
constructorDisjoint、constructorMember、scalarFiber、scalarInjective、variableFiber、variableDisjoint。
每个有source_*、*_kernel_certificate及native_*；有限顺序/不同标签的前提是外部公式模式索引的已证关系。
每个对象闭句中的候选数值和字段仍在全部内部集合上量化。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成545个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit五个入口以--trust=0通过。
4916项声明审计：211项无公理依赖，4705项允许依赖；0警告。
本批11个新模块149项显式声明全部审计；Internal具名覆盖累计2601项。
514份源码SHA256独立复核，差异0；累计245对核心/native证书或模式精确依赖通过。
新增18组核心恰依赖propext/Classical.choice/Quot.sound；native恰额外继承原七项ZF闭性证书。
对象ZF没有新增选择公理；原choice额外证书继续限域。
两份可信基JSON、原19规则/九类ZF锁、固定依赖和原核未改；锁文件Git复核仅规范化检出的CRLF。
独立回读verification/syntax-constructors-readback.json，包含全部11标签/字段数实例清单。
未推送；日志、哈希和完整足迹仅本地verification/；原OpenAI完整构建及Comparator未运行。

## 下一最小工程

4c.a.ii先补同码字段反向单射、变量实际索引解码，再构造纯项检查。
纯项只允许bvar/fvar，索引必须严格属于相应内部bound/free上下文长度；空上下文和错域需实际排除。
4c.a.iii补membership编号0的scalar及全部11种局部类型分支。
4c.b须构造真实内部上下文类型状态，处理量词子式的bound后继；固定bound的单个二值递归不足。
4c.c继续非单射捕获规避替换。随后仍需完整ProofZF/U、内部编译器及最终Derives nativeZF [] (Con_ZF→Con_target)。
上述类型/作用域/内部替换和最终Con标志均保持False。
