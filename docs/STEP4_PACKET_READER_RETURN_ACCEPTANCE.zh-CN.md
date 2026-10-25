# reader实际EOF与完整真实运行返回对象验收（2026-10-25）

reader实际EOF返回及整段真实运行返回已验收：原Nil／单格forest呈现None／Some，EOF通过构造真实acc逆序载荷和实际Some码，EOF失败／字节拒绝准确返回None。每个实际状态carrier均有唯一真实运行返回，域准确等于carrier；任意真实停止历史和实际末字段上的Some／None双条件已证明。12模块188声明、27组原nativeZF闭句；2503构建、27334审计、零警告，九命令／五trust=0通过；仅9个旧EOF原语子门false→true。原初始化／varint分段、完整readTokens／Bytes／Canonical／Tok程序桥、Basic AST、内部Proof／解释及最终Con仍未完成。

## 对象语言、背景与最终主句

纯EqMem、完整ZF以及完整Separation／Collection不变。所有新增模式最终返回原 `YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ`，经 `TheoryTransport.sentence` 和 `ZFReplay.replay` 传输，未另建推导核。参数都是对象变量槽位；外部模式索引仅负责构造闭句。量词覆盖全部内部ω，包括非标准位置及任意无效候选；不使用外部良基或标准ω假设，不增加对象Choice或不可达。

```text
Derives nativeZF [] (.imp Con_ZF Con_target)
target = ZF + PP + ACwo + ¬AC
Con_T = ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))
```

上述最终主句仍未证明。内部Proof及其完整公理测试、原Basic AST、原数学解释仍有缺口，不能用本批程序原语结果替代。YesMetaZFC固定 `039c8e132cc19671d73a3933c66b4799d2599dd6`，依赖工作树及七个理论／信任／构建锁文件保持。

## 实际Option呈现与局部返回

```text
None(w,q) = Nil(w,q)
Some(w,u,q) = Forest₁(w,[u],q)
Success(w,z,o,L,v,s,a,q)
  = EOFSuccess(w,z,o,L,v,s,a) ∧ ∃u (Reverses(w,a,u) ∧ Some(w,u,q))
Rejection = EOFFailure ∨ (State ∧ Blocked)
Return = Success ∨ (Rejection ∧ None)
```

None／Some采用既有原列表码的零格／一格forest呈现，证明实际编码存在、唯一、载荷注入、自然性及互斥。这是明确的对象Option表示；尚未证明它与宿主Option或完整上游程序编译表示的对应，不把这个表示本身当成原程序桥。

EOF成功中的真实State给有效累加器；应用上一批全内部有效列表实际逆序存在性，在对象存在量词内取得真正逆序列表码，再构造Some码。失败或实际字节拒绝则构造None。通过三类原终止守卫互斥、实际逆序码唯一和原forest唯一性，得到全候选局部返回码唯一。

对任意实际Some(w,u,q)有精确双条件：Return(q)当且仅当原EOF成功且Reverses(a,u)。对任意实际None(w,q)，Return(q)当且仅当原拒绝。载荷是实际完整逆序关系，覆盖全部内部字段，不只检查成功标签。局部返回存在域恰为原三类停止观察；不能返回的候选没有被默认为None。

## 实际状态码与真实历史上的完整返回

```text
Coded(w,B,z,o,n,q)
  = ∃L,v,s,a (StateCode(w,L,v,s,a,n) ∧ Return(w,B,z,o,L,v,s,a,q))
Run(w,B,z,o,n,q)
  = ∃r,l,d,f (History(w,B,z,o,n,r,l,d,f) ∧ Coded(w,B,z,o,r,q))
Fiber(n) = ∃q ((q∈ω ∧ Run(n,q)) ∧ ∀s (Run(n,s) → s=q))
```

History保留既有真实序列图、实际首末值、全部内部索引上的真实带码步。Run不把终止性或预期答案放入历史定义，而从实际末返回域推导原停止观察与无后继。原真实状态码字段注入性消去任意四字段解码，Coded在每个实际源码上恰好归一成局部Return；其存在域准确等于原终止观察，覆盖任意候选码。

原带分类完整停止历史的对象存在性直接给每个实际carrier的Run返回；相反，任意Run的真实历史推出源carrier。因此在Ω、B∈ω、Empty(z)、o∈ω下，存在返回恰当且仅当源carrier成立。这里参数o只是自然守卫参数；原程序具体初值及常数实例和分段正确性留到下一单元。

两条实际Run各自给真实停止历史。原停止末状态唯一性对齐末码，再由Coded唯一性对齐返回码。对象EX／ALL纤维只保留Ω、B∈ω、Empty(z)、o∈ω与源carrier；没有残留的历史存在、终止、长度界、归纳假设或返回唯一性前提。

任意给定真实停止历史上，Run(n,q)精确等价于Coded(r,q)；在实际末状态码上再次归一为Return。由此整段Run的Some／None精确双条件包含真实EOF守卫、实际逆序载荷或原拒绝。不会因换一段历史而产生不同返回。

## 实际验收

| 项目 | 结果 |
|---|---|
| 新模块／显式声明／闭句模式 | 12／188／27 |
| 定向native构建 | 2238 jobs通过 |
| 全仓构建 | 2503 jobs通过 |
| 声明审计 | 27334；无公理485；允许足迹26849 |
| 警告／SHA256不一致 | 0／0 |
| 验收命令／trust=0 | 9条退出0／其中5条 |
| 全部核心／native精确证书对 | 3098 |
| Internal显式声明覆盖 | 24990 |
| 全部哈希独立回读 | 2283项一致 |
| 原数学源码、AST、锁与固定依赖 | 保持 |

27组核心证书的足迹准确为propext、Classical.choice、Quot.sound；native证书准确为前三项加既有锁定七项。188个新增显式声明在扩展允许清单前已逐项独立预审计；没有放宽其他声明。宿主证明证书中的Classical.choice不作为对象AC假设。

仅9个原EOF原语子门false→true（八处actual_EOF_accumulator_reverse及实际逆序guard的EOF连接字段）；其他旧布尔叶逐项保持。新增object_actual_EOF_reverse_option_and_real_run_return_exists_unique_proved=true。完整程序桥、Basic AST、内部Proof及最终Con均保持false。

## 清理与证据

按已校验的工程.local精确白名单删除11个临时脚本、驱动、检查片段及被替代日志，总逻辑45243字节；逐文件路径／大小／SHA256保留。编译前Lean／Lake为0，终止0。实测C盘空闲由102443098112至102443151360字节，单独记录系统即时变化，不把逻辑大小冒充可用空间收益。正式代码、审计证据、依赖及其他工程保持。

本地证据不自动发布：verification/packet-reader-return-readback.json、summary.json、commands.json、build.log、audit.log；.local/packet-reader-return-preaudit.json与preaudit.log；.local/packet-reader-return-precompile-cleanup.json。提交后进一步检查全部工作文件哈希、Git blob原始字节及干净状态。

## 后续agent工程流程

| 单元 | 实现职责 | 原核验收要求 | 状态 |
|---|---|---|---|
| R1／R2 | 原无界状态、真实输入Cons、完整单步 | 准确域、实际状态字段及带码后继唯一 | 已验收 |
| R3 | 实际历史、内部长度守恒与停止 | 所有内部步、停止历史存在及末码／长度／域／图联合唯一 | 已验收 |
| R4a／R4b.1 | 三类实际停止观察及实际逆序 | 分类互斥穷尽；原内部列表逆序存在唯一、全字段及Nil／Cons律 | 已验收 |
| R4b.2 | 原EOF返回与整段实际运行返回 | 实际Some逆序载荷／None双条件，真实运行域及对象EX／ALL唯一纤维 | 本批已验收 |
| R4b.3 | 原初始化与规范varint分段 | 实际初值value／scale／acc，全部内部输入上的分段及输出顺序不变量 | 下一单元 |
| R5 | 原reader与Bytes／Canonical／Tok程序桥 | 原程序与独立规格双条件，覆盖非标准及所有无效内部候选码 | 待完成 |
| A／P | 原Basic AST及内部Proof检查器 | 六规则／27模式、完整Separation／Collection及全部内部码 | 待完成 |
| I／C | 原数学解释及内部Con | 背景假设核对、对象证明变换、原nativeZF中的Con蕴含 | 待完成 |


下一单元先明确原初始化实际常数与State编码、构造真实空累加器和初始输入，再以内部全量词证明value／scale、已完成token及当前varint片段不变量。把实际acc逆序与输出顺序连接到独立Canonical／Bytes／Tok规格后，才可宣布完整reader程序桥成立。随后按原六规则／27模式和完整公理模式实现内部Proof及解释，最终交付原nativeZF中的内部Con蕴含。
