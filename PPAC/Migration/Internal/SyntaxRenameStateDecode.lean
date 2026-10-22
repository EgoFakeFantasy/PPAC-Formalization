import PPAC.Migration.Internal.SyntaxRenameState

/-! 任意内部自然状态码的实际唯一七字段解码；所有候选仍在对象量词范围内。 -/
namespace PPAC.Migration.Internal.SyntaxRenameStateDecode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique_params {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (cell w r s a b c d q h)) :
    Derives Γ (uniqueParams w h r s a b c d q) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := cell w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))
  have hZ7 := zf_under_seven hZ B
  have hw7 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_seven hw B
  have hc7 : Derives Δ (cell w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, cell_rename] using under_seven hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxRenameState.same_fields hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw7 hB hc7

theorem actual_decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (recognized w h)) : Derives Γ (decodedFiber w h) := by
  let B := stateBody w h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))
  apply eliminate_seven B _ hc
  have hZ7 := zf_under_seven hZ B
  have hw7 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_seven hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := unique_params hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) hw7 (.conjL hB)
  have ho := intro_decoded w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) hB hu
  simpa only [Formula.raise, decodedFiber_rename] using ho

theorem recognized_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (recognized w h)) : Derives Γ (.mem h w) := by
  let B := stateBody w h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))
  apply eliminate_seven B _ hc
  have hZ7 := zf_under_seven hZ B
  have hw7 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_seven hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxRenameState.natural hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw7 (.conjL hB)

theorem recognized_of_fiber {m} {Γ : Context m} (w h : Fin m)
    (hc : Derives Γ (decodedFiber w h)) : Derives Γ (recognized w h) := by
  let B := (stateBody w h).conj (uniqueParams w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))
  apply eliminate_seven B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := intro_recognized w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) (.conjL hB)
  simpa only [Formula.raise, recognized_rename] using ho

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((recognized w h).iff (decodedFiber w h)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact actual_decode (ZFContext.add hZ _) w h (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact recognized_of_fiber w h (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxRenameStateDecode
