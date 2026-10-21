import PPAC.Migration.Internal.StructuralListValidity

/-! 前缀反演所需真实成员闭包、后继域包含和对象等词替换。 -/
namespace PPAC.Migration.Internal.StructuralListTraceOrder
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralListSyntax StructuralListTraceSyntax

theorem member_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hi : Derives Γ (.mem i p)) : Derives Γ (.mem i w) := by
  have htw := OmegaStructureInduction.omega_transitive w (ZFContext.separation hZ OmegaStructureSyntax.subsetMatrix) hw
  have hsub := Derives.impE (OmegaStructureSyntax.transitive_at w p htw) hp
  exact .impE (RestrictionSyntax.subset_at p w i hsub) hi

theorem old_subset {m} {Γ : Context m} (l d : Fin m) (hd : Derives Γ (successor d l)) : Derives Γ (RestrictionSyntax.subset l d) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  have hd1 : Derives (Context.add M (Context.image Formula.raise Γ)) (successor d.castSucc l.castSucc) := by simpa only [Formula.raise, successor_rename] using under hd M
  exact InsertLogic.old_member _ _ _ _ hd1 (.hyp (Or.inl rfl))

theorem edge_input_subst {m} {Γ : Context m} (f i j a : Fin m) (he : Derives Γ (.equal i j))
    (hi : Derives Γ (edge f i a)) : Derives Γ (edge f j a) := by
  have h : Derives Γ ((edge f.castSucc (Fin.last m) a.castSucc).instantiate i) := by
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  have ho := Derives.eqSubst (edge f.castSucc (Fin.last m) a.castSucc) he h
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem nil_output_subst {m} {Γ : Context m} (w n p : Fin m) (he : Derives Γ (.equal n p)) (hn : Derives Γ (nilCode w n)) : Derives Γ (nilCode w p) := by
  have h : Derives Γ ((nilCode w.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, nilCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (nilCode w.castSucc (Fin.last m)) he h
  simpa only [Formula.instantiate, nilCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem step_output_subst {m} {Γ : Context m} (w a b c : Fin m) (he : Derives Γ (.equal b c)) (hb : Derives Γ (step w a b)) : Derives Γ (step w a c) := by
  have h : Derives Γ ((step w.castSucc a.castSucc (Fin.last m)).instantiate b) := by
    simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb
  have ho := Derives.eqSubst (step w.castSucc a.castSucc (Fin.last m)) he h
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralListTraceOrder
