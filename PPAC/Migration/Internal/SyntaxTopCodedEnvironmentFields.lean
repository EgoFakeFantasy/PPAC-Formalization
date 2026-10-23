import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentUnique

/-! 首槽数值环境的完整原列表字段律，保留源域守卫，不能把表外字段当合法项像。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopCodedEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateCoded w a b A t R S))
    (hi : Derives Γ (empty i)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff (.equal q t)) := by
  let E := instantiateBody w a b A t R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hi2 : Derives Δ (empty i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.instantiate_zero hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc q.castSucc.castSucc hw2 (.conjL hE) hi2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last m).castSucc A.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjL (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename]) ho

theorem instantiate_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateCoded w a b A t R S))
    (hj : Derives Γ (Formula.mem j a)) (hi : Derives Γ (successor i j)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff (SyntaxVariableSyntax.code true w j q)) := by
  let E := instantiateBody w a b A t R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hj2 : Derives Δ (Formula.mem j.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hj E)
  have hi2 : Derives Δ (successor i.castSucc.castSucc j.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.instantiate_bound hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc j.castSucc.castSucc q.castSucc.castSucc hw2 (.conjL hE) hj2 hi2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last m).castSucc A.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjL (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

theorem instantiate_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S i q : Fin m)
    (he : Derives Γ (instantiateCoded w a b A t R S))
    (hi : Derives Γ (Formula.mem i b)) :
    Derives Γ (((Formula.mem i b).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code false w i q)) := by
  let E := instantiateBody w a b A t R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hi2 : Derives Δ (Formula.mem i.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.instantiate_free hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc q.castSucc.castSucc (.conjL hE) hi2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjR (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractCoded w a b A B R S))
    (hi : Derives Γ (empty i)) :
    Derives Γ (((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code true w i q)) := by
  let E := abstractBody w a b A B R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hi2 : Derives Δ (empty i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.abstract_zero hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc q.castSucc.castSucc hw2 (.conjL hE) hi2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last (m+1)) B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjR (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S i j q : Fin m)
    (he : Derives Γ (abstractCoded w a b A B R S))
    (hi : Derives Γ (Formula.mem i a)) (hj : Derives Γ (successor j i)) :
    Derives Γ (((Formula.mem i a).conj (StructuralListFieldSyntax.field w R i q)).iff (SyntaxVariableSyntax.code true w j q)) := by
  let E := abstractBody w a b A B R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hi2 : Derives Δ (Formula.mem i.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hi E)
  have hj2 : Derives Δ (successor j.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hj E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.abstract_bound hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc j.castSucc.castSucc q.castSucc.castSucc (.conjL hE) hi2 hj2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjL (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractCoded w a b A B R S))
    (hj : Derives Γ (Formula.mem j b)) (hi : Derives Γ (successor i j)) :
    Derives Γ (((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code false w j q)) := by
  let E := abstractBody w a b A B R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hj2 : Derives Δ (Formula.mem j.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hj E)
  have hi2 : Derives Δ (successor i.castSucc.castSucc j.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := SyntaxTopEnvironmentFields.abstract_free hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc j.castSucc.castSucc q.castSucc.castSucc hw2 (.conjL hE) hj2 hi2
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (Fin.last (m+1)) B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc (.conjR (.conjR hE))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFields
