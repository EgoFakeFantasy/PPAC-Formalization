import PPAC.Migration.Internal.StructuralListTraceAppend

/-! 纯对象内部轨迹的Nil/Cons实际闭包及范围；反向解码另行验收。 -/
namespace PPAC.Migration.Internal.StructuralListValidity
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListTraceSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem cons_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (valid w t))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (valid w n) := by
  let V := validBody w t
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  apply eliminate_valid w t _ ht
  have hZ5 : ZFContext.Evidence Δ := zf_under_five hZ V
  have hw5 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_five hw V
  have hc5 : Derives Δ (consCode w.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, consCode_rename] using under_five hc V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hout := StructuralListTraceAppend.extend_valid hZ5 _ _ _ _ _ _ _ _ _ hw5 (under_five hh V) hV hc5
  simpa only [Formula.raise, valid_rename] using hout

theorem range {m} {Γ : Context m} (w n : Fin m) (hn : Derives Γ (valid w n)) : Derives Γ (.mem n w) := by
  let V := validBody w n
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  apply eliminate_valid w n _ hn
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  exact StructuralListTraceProperties.range _ _ _ _ _ _ _ hV
end PPAC.Migration.Internal.StructuralListValidity
