# 任意内部序列的唯一树构造及精确恢复验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点448e3d0ec1070fcc7b93e23ed2943c9aa8a7296a。
本批完成4b.c.4c.vi，为下一步全部原生语法构造提供实际的原树码构造接口。
全部11种公式类型/作用域、内部替换、ProofZF/U及最终Con仍未完成。

## 固定对象合同与实际构造

语言仍为纯等词/成员，背景原ZF；Source.Derives经TheoryTransport/ZFReplay返回
原FirstOrder.Derives nativeZF []闭句证书。没有新增对象AC、Con、标准ω或新推导核。
本批沿用原treeValue(node(tag,children))=Pair(tag,forestValue(children))+1及原结构列表数值。

TreeEncoding(w,tag,l,f,n):=∃p Shape(w,n,tag,p,l,f)。
Shape保留tag∈w、原Raw(w,tag,p,n)、实际HasLength(w,p,l)和原完整Fields(w,p,l,f)。
只存在量化实际payload；tag、长度和完整字段图是精确的给定对象参数。

原ZF证明：Ω(w)、tag∈w、l∈w、Sequence(f,l,w)下，实际存在唯一自然码n满足TreeEncoding。
Sequence是原完整functionOn和全部图边的ω值域约束；长度和字段覆盖全部内部有限序列。
存在性先调用已验收任意内部序列的真实列表逆编码，取得实际payload p及给定Fields图；
再按原raw节点构造实际n。没有“假设存在编码”前件，也没有把外部标准列表递归当作内部构造。
唯一性先用原列表的同长度/同字段图码单射性对齐payload，再由原raw同输入唯一性取得n相等。
唯一纤维含n∈w、实际TreeEncoding及∀r(TreeEncoding(...,r)→r=n)。

## 任意实际解码的精确恢复

同一原节点码的Shape四分量唯一，独立于全部子树是否有效。
证明先由原raw输入单射性取得tag、payload相等；通过对象等词替换对齐payload，
再用原列表实际长度及完整字段图联合唯一性取得长度和整个图相等。
因此，已构造TreeEncoding(w,tag,l,f,n)及任何Shape(w,n,other,p,k,g)下，
正式推出(other=tag∧k=l)∧g=f。
实际完整字段图等于原输入图，不只是在一组外部标准位置上匹配，也不允许额外图元素。

反向：给定任何实际解码Shape(w,n,tag,p,l,f)，任何TreeEncoding(w,tag,l,f,r)都满足r=n。
存在定理使重编码不为空；原码本身也满足同一个构造关系。
以上给出两个关系式编解码方向的精确恢复；没有诉诸宿主解码器或Option计算。

## 构造与子树有效性的双条件

在Ω(w)及TreeEncoding(w,tag,l,f,n)下，原核证明：
Valid(w,n)↔∀i∀y(edge(f,i,y)→Valid(w,y))。
反向将给定Shape和全部输入子字段Valid组成真实Recursive，使用上批已证Recursive↔Valid。
正向先实际解码有效树得到完整NodeData，Shape四分量唯一性对齐字段图，
再通过对象等词替换把其全部子字段Valid传回原输入图f。
没有把原输入字段的有效性预设到TreeEncoding定义或Shape唯一性里。
该结果处理全部内部图边；一般结构树Valid仍不能替代11种公式构造的类型/作用域正确性。

| 新模块 | 职责 |
|---|---|
| StructuralTreeEncodeSyntax | 单个真实payload见证、存在/唯一纤维和严格重命名 |
| StructuralTreeShapeUnique | 不预设递归有效性的Shape四分量唯一和payload等词替换 |
| StructuralTreeEncode | 任意完整内部字段序列实际构造唯一自然树码、真实唯一纤维 |
| StructuralTreeEncodeReadback | 构造有效性反射、任意实际解码的精确回读、重编码原码恢复 |
| ObjectStructuralTreeEncode | 八个完整源ZF及原nativeZF闭句证书 |

八个端点为exists、fiber、range、unique、shapeUnique、validity、readback、codeRecovery。
每个有source_*、*_kernel_certificate和native_*；CheckStep4检查给定参数未被丢弃及全部八个原核端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成534个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit五个入口均以--trust=0通过。
4767项声明审计：203项无公理依赖，4564项允许依赖；0警告。
本批5个新模块60项显式声明全部审计；Internal具名覆盖累计2452项。
503份源码SHA256独立复核，差异0；累计227对核心/native证书或模式精确依赖通过。
新增八个核心恰依赖propext/Classical.choice/Quot.sound；native端点恰额外继承原七项ZF闭性证书。
对象ZF没有新增选择公理；原choice额外证书继续限域。
两份可信基JSON、原19规则/九类源ZF锁、固定依赖及原核不改。
锁文件用git diff及Git内容独立核对，仅规范化Windows检出的CRLF。
独立回读verification/tree-encode-readback.json；原OpenAI完整构建与Comparator未运行。
未推送；日志/哈希/公理细节仅保留本地verification/。

## 下一关

4c.a接入原bvar/fvar及11种公式构造的精确标签、字段数、scalar叶和内部索引界。
纯签名无函数符号，membership编号为0；量词体必须在真实后继bound长度检查。
4c.b实际构造并证明全部内部上下文的类型状态/检查；4c.c完成非单射捕获规避替换的内部关系与正确性。
随后仍需专用全6规则/27逻辑模式的ProofZF/U、内部编译器和最终Derives nativeZF [] (Con_ZF→Con_target)。
