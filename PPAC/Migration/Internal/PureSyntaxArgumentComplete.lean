import PPAC.Migration.Internal.PureSyntaxConsComplete

/-! 内部nil／cons全部分解推出真实参数查询；统一严格成员IH暂保留。 -/
namespace PPAC.Migration.Internal.PureSyntaxArgumentComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PureSyntaxListInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_parts_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n h t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hp : Derives Γ (TypedArgumentListElimination.consParts w k b f h t)) :
    Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  have hless := Derives.conjR (StructuralConsCore.components hZ w h t n hw hh ht hc)
  let B := ((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj
    ((SyntaxTermSyntax.term w.castSucc b.castSucc f.castSucc h.castSucc).conj
      (SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) b.castSucc f.castSucc t.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hl1 : Derives Δ (.mem t.castSucc n.castSucc) := under hless B
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht1 := Derives.impE (.conjR (correct_at w.castSucc t.castSucc b.castSucc f.castSucc (Fin.last m) (allIH_at _ _ _ hi1 hl1))) (.conjR (.conjR hB))
  exact of_eq (PureSyntaxTrace.arguments_rename w b f k n Fin.castSucc).symm
    (PureSyntaxConsComplete.checked_cons hZ1 w.castSucc b.castSucc f.castSucc (Fin.last m) k.castSucc h.castSucc t.castSucc n.castSucc hw1 (.conjL (.conjR hB)) (.conjR (.conjR hB)) ht1 hc1 (.conjR (.conjL hB)))

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n)) :
    Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  apply Derives.disjE (TypedArgumentListCases.forward hZ w k b f n hw ht)
  · let E := TypedArgumentListCases.nilCase w k b f n
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact PureSyntaxNilComplete.checked_nil (ZFContext.add hZ E) w b f k n (add hw E) (.conjL (.conjR hE)) (.conjR (.conjR hE)) (.conjL hE)
  · let E := TypedArgumentListCases.consCase w k b f n
    let B := TypedArgumentListCases.consBody w k b f n
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw E) B)
    have hi2 : Derives Δ (allIH (old 2 w) (old 2 n)) := of_eq (allIH_rename w n (old 2)) (HornBinderRules.under_body 2 (add hi E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hout := cons_parts_checked hZ2 (old 2 w) (old 2 b) (old 2 f) (old 2 k) (old 2 n) (slot 2 0) (slot 2 1) hw2 hi2 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjL (.conjR hB)) (.conjR (.conjR hB))
    exact of_eq (PureSyntaxTrace.arguments_rename w b f k n (old 2)).symm hout

theorem checked_iff_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n)) :
    Derives Γ ((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact PureSyntaxArgumentSound.checked_sound (ZFContext.add hZ _) w b f k n (add hw _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact checked_complete (ZFContext.add hZ _) w b f k n (add hw _) (add hi _) (.hyp (Or.inl rfl))

theorem correct_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n)) : Derives Γ (correct w n) := by
  apply OriginalUniversalBlock.intro_many 3 (body w n)
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hi1 := of_eq (allIH_rename w n (old 3)) (HornBinderRules.under_many 3 hi)
  exact checked_iff_from_induction (HornBinderRules.zf_many 3 hZ) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) hw1 hi1

end PPAC.Migration.Internal.PureSyntaxArgumentComplete
