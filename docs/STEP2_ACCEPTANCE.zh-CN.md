# 第二步验收
日期：2026-10-21。分支：migration/yesmeta-step2。上一基点：f28b0334a740108057adf18a24dc11abd866efbe。
固定OpenAI及YesMetaZFC提交保持SOURCE_LOCK不变；输入19规则逐字校验见SOURCE_RULES_LOCK。

## 对象层最终合同
背景B固定原对象ZF，签名ℒ，最终要求原FirstOrder.Derives B [] (Con_ZF→Con_target)。
Con量化模型内部全部自然数证明码，检查原六规则Hilbert证书。
完整定义、编码与未实现边界见OBJECT_TARGET；它不等于Lean的Consistent函数类型。
已废除Contract中容易误当终点的RelativeConsistencyGoal名称，中间任务改名ExternalConsistencyGoal。

## 本批真正完成的内容
1. 源rename（可非单射）、instantiate与原生bound/free任意替换的严格AST等式。
2. binder提升、fresh自由变量抽象、forall/exists封闭及与第一步闭句的精确对应。
3. 全19源自然演绎规则的原核Derives传输，覆盖无限源假设谓词。
4. 任意源理论、任意有限变量环境中的闭句推导到空free原核推导。
5. 任意原Hilbert证书的有限公理支撑，以及编译结果的有限支撑。
6. 实际回放：全称恒等、存在消去、源n=1的闭存在句、等词替换、经典规则；捕获敏感AST实例。

核心接口：
TheoryTransport.closed_at
  (d : Source.Derives (T.at n) (Source.Formula.rename Fin.elim0 φ)) :
  FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence φ)

此处theory T是源理论句子像，不直接断言它等于原Collection版ZF。
该传输是外部归纳产生原对象推导的定理；它尚不是“所有内部证明码转换正确”的对象统一定理。

## 实际验收结果
- python scripts/check_source_rules.py：退出0，19条规则与固定摘录一致。
- lake --no-cache --wfail build：退出0，65个构建任务，0警告。
- lake env lean --trust=0 Check.lean：退出0。
- lake env lean --trust=0 CheckStep2.lean：退出0。
- lake env lean --trust=0 Audit.lean：退出0。
- python scripts/verify.py：退出0，38个列举声明；8个无公理依赖，30个有已记录依赖；0警告。
新增22个关键声明均仅依赖标准propext/Classical.choice/Quot.sound。
原合同继承的7个底座native_decide证书没有被隐藏或扩增；详见TRUST_BASELINE。
完整命令/退出码、源码哈希和原始输出保存在忽略的本地verification/。

## 尚未完成
反向推导传输；源Replacement/原Collection及两种AC的对象等价；
ZF/U专用内部Proof检查器的完整AST及任意内部码正确性；
转换器的内部表示与对象推导；强迫/模型主构造；最终内部Con蕴含对象主句。
本批不声称OpenAI原库已重新编译，不声称PP/AC分离已在YesMetaZFC完成。

下一步：步骤3，先给出源/目标ZF公理和模式的精确推导对应，再做专用内部检查器。
