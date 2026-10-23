import PPAC.Migration.Internal.LookupTableRecursiveSyntax

/-! 原Cons的实际tail严格界、双投影存在及旧严格迭代核心的Cons递归方程。 -/
namespace PPAC.Migration.Internal.LookupTableProgramFacts
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tail_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (selected false w n t)) : Derives Γ (.mem t n) := by
  let B := StructuralListProjectionSyntax.body false w.castSucc n.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjR (StructuralConsCore.components (ZFContext.under hZ B) w.castSucc (Fin.last m) t.castSucc n.castSucc hw1 (.conjR (.conjL hB)) (.conjL (.conjL hB)) (.conjR hB))

theorem selected_head_has_tail {m} {Γ : Context m} (w n y : Fin m) (hs : Derives Γ (selected true w n y)) :
    Derives Γ (hasCons false w n) := by
  let B := StructuralListProjectionSyntax.body true w.castSucc n.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := intro_selected false w.castSucc n.castSucc (Fin.last m) y.castSucc
    (.conjI (.conjI (.conjR (.conjL hB)) (.conjL (.conjL hB))) (.conjR hB))
  exact of_eq (hasCons_rename false w n Fin.castSucc).symm (intro_hasCons false w.castSucc n.castSucc (Fin.last m) ht)

theorem head_has_tail {m} {Γ : Context m} (w n : Fin m) (hs : Derives Γ (hasCons true w n)) : Derives Γ (hasCons false w n) := by
  let B := selected true w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  exact of_eq (hasCons_rename false w n Fin.castSucc).symm (selected_head_has_tail w.castSucc n.castSucc (Fin.last m) (.hyp (Or.inl rfl) : Derives Δ B))

theorem tail_of_returned {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hy : Derives Γ (StrictLookupSyntax.returned w n i y)) :
    Derives Γ (hasCons false w n) := by
  apply SourcePropositional.by_cases (hasCons true w n)
  · exact head_has_tail w n (.hyp (Or.inl rfl))
  · exact .botE (StrictLookupFailure.point_absurd (ZFContext.add hZ _) w n i y (add hw _) (add hi _) (.hyp (Or.inl rfl)) (add hy _))

theorem successor_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t j i y : Fin m)
    (hw : Derives Γ (omega w)) (hj : Derives Γ (.mem j w)) (hi : Derives Γ (successor i j))
    (ht : Derives Γ (selected false w n t)) :
    Derives Γ ((StrictLookupSyntax.returned w n i y).iff (StrictLookupSyntax.returned w t j y)) := by
  let B := StructuralListProjectionSyntax.body false w.castSucc n.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (successor i.castSucc j.castSucc) := of_eq (successor_rename i j Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := StrictLookupRules.successor_iff (ZFContext.under hZ B) w.castSucc (Fin.last m) t.castSucc n.castSucc j.castSucc i.castSucc y.castSucc hw1 (.conjR (.conjL hB)) (.conjL (.conjL hB)) (under hj B) hi1 (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StrictLookupSyntax.returned_rename]) ho

end PPAC.Migration.Internal.LookupTableProgramFacts
