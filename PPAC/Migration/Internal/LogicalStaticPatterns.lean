import PPAC.Migration.Internal.LogicalStaticQueryList
import PPAC.Migration.Internal.LogicalStaticNode
import PPAC.Migration.Internal.LogicalRule0Head
import PPAC.Migration.Internal.LogicalRule1Head
import PPAC.Migration.Internal.LogicalRule2Head
import PPAC.Migration.Internal.LogicalRule3Head
import PPAC.Migration.Internal.LogicalRule4Head
import PPAC.Migration.Internal.LogicalRule5Head
import PPAC.Migration.Internal.LogicalRule6Head
import PPAC.Migration.Internal.LogicalRule7Head
import PPAC.Migration.Internal.LogicalRule8Head
import PPAC.Migration.Internal.LogicalRule9Head
import PPAC.Migration.Internal.LogicalRule10Head
import PPAC.Migration.Internal.LogicalRule11Head
import PPAC.Migration.Internal.LogicalRule12Head
import PPAC.Migration.Internal.LogicalRule13Head
import PPAC.Migration.Internal.LogicalRule14Head
import PPAC.Migration.Internal.LogicalRule15Head
import PPAC.Migration.Internal.LogicalRule16Head
import PPAC.Migration.Internal.LogicalRule17Head
import PPAC.Migration.Internal.LogicalRule18Head
import PPAC.Migration.Internal.LogicalRule19Head
import PPAC.Migration.Internal.LogicalRule22Head
import PPAC.Migration.Internal.LogicalRule26Head

/-! 每个固定原模式的arity、有序查询及head变量覆盖；独立rfl／decide证书。 -/
namespace PPAC.Migration.Internal.LogicalStaticPatterns
open YesMetaZFC.Automation

theorem rule0_arity : ObjectLogicalAxiom.rule0.arity = 4 := rfl

theorem rule0_queries : ObjectLogicalAxiom.rule0.queries = LogicalStaticQueries.originalQueries 3 false := rfl

theorem rule0_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule0.head.variables := by decide

theorem rule1_arity : ObjectLogicalAxiom.rule1.arity = 2 := rfl

theorem rule1_queries : ObjectLogicalAxiom.rule1.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule1_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule1.head.variables := by decide

theorem rule2_arity : ObjectLogicalAxiom.rule2.arity = 3 := rfl

theorem rule2_queries : ObjectLogicalAxiom.rule2.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule2_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule2.head.variables := by decide

theorem rule3_arity : ObjectLogicalAxiom.rule3.arity = 3 := rfl

theorem rule3_queries : ObjectLogicalAxiom.rule3.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule3_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule3.head.variables := by decide

theorem rule4_arity : ObjectLogicalAxiom.rule4.arity = 2 := rfl

theorem rule4_queries : ObjectLogicalAxiom.rule4.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule4_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule4.head.variables := by decide

theorem rule5_arity : ObjectLogicalAxiom.rule5.arity = 3 := rfl

theorem rule5_queries : ObjectLogicalAxiom.rule5.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule5_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule5.head.variables := by decide

theorem rule6_arity : ObjectLogicalAxiom.rule6.arity = 3 := rfl

theorem rule6_queries : ObjectLogicalAxiom.rule6.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule6_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule6.head.variables := by decide

theorem rule7_arity : ObjectLogicalAxiom.rule7.arity = 1 := rfl

theorem rule7_queries : ObjectLogicalAxiom.rule7.queries = LogicalStaticQueries.originalQueries 0 false := rfl

theorem rule7_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule7.head.variables := by decide

theorem rule8_arity : ObjectLogicalAxiom.rule8.arity = 2 := rfl

theorem rule8_queries : ObjectLogicalAxiom.rule8.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule8_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule8.head.variables := by decide

theorem rule9_arity : ObjectLogicalAxiom.rule9.arity = 2 := rfl

theorem rule9_queries : ObjectLogicalAxiom.rule9.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule9_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule9.head.variables := by decide

theorem rule10_arity : ObjectLogicalAxiom.rule10.arity = 2 := rfl

theorem rule10_queries : ObjectLogicalAxiom.rule10.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule10_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule10.head.variables := by decide

theorem rule11_arity : ObjectLogicalAxiom.rule11.arity = 3 := rfl

theorem rule11_queries : ObjectLogicalAxiom.rule11.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule11_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule11.head.variables := by decide

theorem rule12_arity : ObjectLogicalAxiom.rule12.arity = 3 := rfl

theorem rule12_queries : ObjectLogicalAxiom.rule12.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule12_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule12.head.variables := by decide

theorem rule13_arity : ObjectLogicalAxiom.rule13.arity = 3 := rfl

theorem rule13_queries : ObjectLogicalAxiom.rule13.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule13_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule13.head.variables := by decide

theorem rule14_arity : ObjectLogicalAxiom.rule14.arity = 3 := rfl

theorem rule14_queries : ObjectLogicalAxiom.rule14.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule14_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule14.head.variables := by decide

theorem rule15_arity : ObjectLogicalAxiom.rule15.arity = 3 := rfl

theorem rule15_queries : ObjectLogicalAxiom.rule15.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule15_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule15.head.variables := by decide

theorem rule16_arity : ObjectLogicalAxiom.rule16.arity = 4 := rfl

theorem rule16_queries : ObjectLogicalAxiom.rule16.queries = LogicalStaticQueries.originalQueries 3 false := rfl

theorem rule16_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule16.head.variables := by decide

theorem rule17_arity : ObjectLogicalAxiom.rule17.arity = 3 := rfl

theorem rule17_queries : ObjectLogicalAxiom.rule17.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule17_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule17.head.variables := by decide

theorem rule18_arity : ObjectLogicalAxiom.rule18.arity = 3 := rfl

theorem rule18_queries : ObjectLogicalAxiom.rule18.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule18_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule18.head.variables := by decide

theorem rule19_arity : ObjectLogicalAxiom.rule19.arity = 3 := rfl

theorem rule19_queries : ObjectLogicalAxiom.rule19.queries = LogicalStaticQueries.originalQueries 2 false := rfl

theorem rule19_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule19.head.variables := by decide

theorem rule22_arity : ObjectLogicalAxiom.rule22.arity = 2 := rfl

theorem rule22_queries : ObjectLogicalAxiom.rule22.queries = LogicalStaticQueries.originalQueries 1 false := rfl

theorem rule22_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule22.head.variables := by decide

theorem rule26_arity : ObjectLogicalAxiom.rule26.arity = 2 := rfl

theorem rule26_queries : ObjectLogicalAxiom.rule26.queries = LogicalStaticQueries.originalQueries 1 true := rfl

theorem rule26_head_variables : ∀ i, i ∈ ObjectLogicalAxiom.rule26.head.variables := by decide

theorem rule0_actual_list_bundle {m} (w : Fin m) (env : Fin 4 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule0.queries w env = LogicalStaticQueries.bundle 3 false w env := by
  rw [rule0_queries]
  exact LogicalStaticQueryList.original_bundle 3 false w env

theorem rule1_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule1.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule1_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule2_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule2.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule2_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule3_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule3.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule3_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule4_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule4.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule4_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule5_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule5.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule5_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule6_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule6.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule6_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule7_actual_list_bundle {m} (w : Fin m) (env : Fin 1 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule7.queries w env = LogicalStaticQueries.bundle 0 false w env := by
  rw [rule7_queries]
  exact LogicalStaticQueryList.original_bundle 0 false w env

theorem rule8_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule8.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule8_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule9_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule9.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule9_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule10_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule10.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule10_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule11_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule11.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule11_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule12_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule12.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule12_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule13_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule13.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule13_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule14_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule14.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule14_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule15_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule15.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule15_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule16_actual_list_bundle {m} (w : Fin m) (env : Fin 4 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule16.queries w env = LogicalStaticQueries.bundle 3 false w env := by
  rw [rule16_queries]
  exact LogicalStaticQueryList.original_bundle 3 false w env

theorem rule17_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule17.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule17_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule18_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule18.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule18_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule19_actual_list_bundle {m} (w : Fin m) (env : Fin 3 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule19.queries w env = LogicalStaticQueries.bundle 2 false w env := by
  rw [rule19_queries]
  exact LogicalStaticQueryList.original_bundle 2 false w env

theorem rule22_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule22.queries w env = LogicalStaticQueries.bundle 1 false w env := by
  rw [rule22_queries]
  exact LogicalStaticQueryList.original_bundle 1 false w env

theorem rule26_actual_list_bundle {m} (w : Fin m) (env : Fin 2 → Fin m) :
    LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule26.queries w env = LogicalStaticQueries.bundle 1 true w env := by
  rw [rule26_queries]
  exact LogicalStaticQueryList.original_bundle 1 true w env

end PPAC.Migration.Internal.LogicalStaticPatterns
