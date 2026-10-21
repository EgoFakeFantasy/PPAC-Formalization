import PPAC.Migration.Internal.ObjectStructuralListProjection

/-! 真实投影递归的存在唯一与对象等词替换；不从Prop抽取宿主数据。 -/
namespace PPAC.Migration.Internal.StructuralListIterationTransport
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def existsIteration {m} (head : Bool) (w a r : Fin m) : Formula m :=
  NaturalEvaluationSyntax.existsValue (matrix head) (params w) w a r

theorem existsIteration_rename {m k} (head : Bool) (w a r : Fin m) (s : Fin m → Fin k) :
    (existsIteration head w a r).rename s = existsIteration head (s w) (s a) (s r) := by
  simp only [existsIteration, NaturalEvaluationSyntax.existsValue_rename]
  rfl

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) : Derives Γ (existsIteration head w a r) := by
  have hA := ZFContext.arithmetic hZ
  exact NaturalEvaluationExistence.at_natural (matrix head) (params w) w a r hw hr
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw)
    (StructuralListProjectionRecursion.actual_recursors hZ head w a hw)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r y z : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w))
    (hy : Derives Γ (iteration head w a r y)) (hz : Derives Γ (iteration head w a r z)) : Derives Γ (.equal y z) := by
  have hA := ZFContext.arithmetic hZ
  exact NaturalEvaluationUniqueness.evaluation_unique (matrix head) (params w) w a r y z hA.base.extensionality hw hr
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw)
    (StructuralListProjectionRecursion.actual_recursors hZ head w a hw) hy hz

theorem step_input_subst {m} {Γ : Context m} (head : Bool) (w x z y : Fin m)
    (he : Derives Γ (.equal x z)) (hy : Derives Γ (step head w x y)) : Derives Γ (step head w z y) := by
  have hi : Derives Γ ((step head w.castSucc (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (step head w.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem step_output_subst {m} {Γ : Context m} (head : Bool) (w x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (step head w x y)) : Derives Γ (step head w x z) := by
  have hi : Derives Γ ((step head w.castSucc x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (step head w.castSucc x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem seed_subst {m} {Γ : Context m} (head : Bool) (w a b r y : Fin m)
    (he : Derives Γ (.equal a b)) (hy : Derives Γ (iteration head w a r y)) : Derives Γ (iteration head w b r y) := by
  have hi : Derives Γ ((iteration head w.castSucc (Fin.last m) r.castSucc y.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (iteration head w.castSucc (Fin.last m) r.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem index_subst {m} {Γ : Context m} (head : Bool) (w a r s y : Fin m)
    (he : Derives Γ (.equal r s)) (hy : Derives Γ (iteration head w a r y)) : Derives Γ (iteration head w a s y) := by
  have hi : Derives Γ ((iteration head w.castSucc a.castSucc (Fin.last m) y.castSucc).instantiate r) := by
    simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (iteration head w.castSucc a.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem value_subst {m} {Γ : Context m} (head : Bool) (w a r y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (iteration head w a r y)) : Derives Γ (iteration head w a r z) := by
  have hi : Derives Γ ((iteration head w.castSucc a.castSucc r.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (iteration head w.castSucc a.castSucc r.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, iteration_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralListIterationTransport
