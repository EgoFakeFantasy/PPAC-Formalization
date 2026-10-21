# 持续目标批次：完整双向分离与Collection呈现
日期：2026-10-21。基点：edc61e6f1c65593df80a73df53597593ca622173。
分支migration/yesmeta-step3；上游固定提交未变。完整内部Con对象形式化目标仍active。

## 已关闭的分离模式缺口
SeparationReverse.native_separation：
对任意n和s : Project.UnarySchema n，返回
FirstOrder.Derives ZFEquivalence.sourceZF [] (Project.fo_sentence (Axioms.Schema.separation s))。
其中sourceZF仍是OpenAI全Replacement版ZF的句子像。
结合既有SeparationSyntax.source_separation，两个方向均覆盖全部参数数目与全部矩阵复杂度。
没有把原生模式限制成ProjectSyntax.unary p；子集定义原子、truth/neg/iff均在完整回译范围内。

## 具体证明链
1. ProjectDecode将任意自由闭合Project公式编码成源8构造器语法。
   子集原子展开为内部全称成员蕴含；等词保持原生等词。
2. 任意参数重命名在Project侧和Source侧分别严格交换；证明显式保留原闭合证书。
   没有放宽原不可约闭合谓词或引入额外可约性选项。
3. 参数反序与全称闭合严格交换；闭句往返等于原核连接词规范化。
4. 整个原生分离句回译恰好是源分离句，不只比较其矩阵。
5. 使用源ZF实际分离公理，加原核规范化等价，得到上述原Derives证书。

## Collection的实际范围
CollectionSyntax.collection将任意源二元矩阵写成：
∀A ((∀x∈A ∃y φ(x,y)) → ∃W ∀x∈A ∃y∈W φ(x,y))，并闭合全部参数。
source_collection对任意n及p : Source.Formula (n+2)，返回原nativeZF中的该句Derives。
原生任意Project.BinarySchema矩阵的Collection句也完整回译，且有原核对象逻辑等价。
这是原Collection公理的精确呈现；没有从源Replacement版ZF推出Collection。
W只是见证界，可能包含多余元素。不能把它直接当作Replacement要求的精确像集。

## 实际验收
C:/Python314/python.exe scripts/verify.py：退出0，8条实际命令全部退出0。
Lean4.33.1；LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，77个任务。
19源规则和9源ZF公理/SHA核对通过；Check、CheckStep2、CheckStep3及Audit均以--trust=0通过。
165个列举声明：14个无公理依赖，151个有已记录依赖；本批新增33个审计声明；0条Lean警告。
新增ProjectDecode、SeparationReverse的审计只允许标准依赖。
Collection桥涉及原nativeZF时仍继承底座既有7个native_decide闭合证书；没有新增自定义公理。
CheckStep3包含任意原生模式的通用推导类型，另含双参数、子集原子、混合量词与独立连接词的回放实例。
验收文件哈希与命令输出保存在忽略的verification/；未推送远端。

## 下一实质工作
- Collection→源Replacement：由功能性前提取得收集界；用全分离构造精确像；
  证明唯一性如何把任意关系输出纳入该界，不能漏掉此方向。
- 源Replacement→Collection：在对象ZF内构造最小见证秩及统一秩界；
  不从Lean的选择函数抽取内部见证，不把语义秩引理当作对象推导。
- 此后仍需两种AC、反向演绎、内部ProofZF/U、内部码转换正确性、解释/强迫及内部Con对象主句。
没有完成完整ZF等价，也没有完成目标主定理；先前验收中的原生分离反向缺口现已关闭。
