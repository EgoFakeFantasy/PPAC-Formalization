import PPAC.Migration.Internal.RawCodeField
import PPAC.Migration.Internal.SyntaxForests

/-! 仅在实际规范Cons条件下桥接原始投影；不改变任意非规范外壳上的定义。 -/
namespace PPAC.Migration.Internal.RawCodeProjectionCanonical
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax

theorem value_consAt {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w e h t n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consAt w e h t n)) : Derives Γ (RawCodeProjectionSyntax.step head w n (if head then h else t)) := by
  let B := consAtWitness w e h t n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hc
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := GodelPairCore.range hZ1 _ _ _ _ hw1 (.conjL hB)
  have hout := RawCodeProjection.intro_raw_pair head w.castSucc e.castSucc (Fin.last m) h.castSucc t.castSucc n.castSucc (under he B) hp (under hh B) (under ht B) (.conjR hB) (.conjL hB)
  simpa only [Formula.raise, RawCodeProjectionSyntax.step_rename, apply_ite] using hout

theorem value_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (RawCodeProjectionSyntax.step head w n (if head then h else t)) := by
  let B := consUnits w h t n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_cons w h t n _ hc
  have hZ2 := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hB) (.conjL (.conjR hB))
  have hout := value_consAt hZ2 head w.castSucc.castSucc (Fin.last (m+1)) h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc hw2 he (OrderedPairElimination.under_two hh B) (OrderedPairElimination.under_two ht B) (.conjR (.conjR hB))
  simpa only [Formula.raise, RawCodeProjectionSyntax.step_rename, apply_ite] using hout

theorem on_cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w h t n y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n)) :
    Derives Γ ((RawCodeProjectionSyntax.step head w n y).iff (.equal y (if head then h else t))) := by
  have hv := value_cons hZ head w h t n hw hh ht hc
  apply Derives.conjI
  · apply Derives.impI
    exact RawCodeProjection.functional_point (ZFContext.add hZ _) head _ _ _ _ (add hw _) (.hyp (Or.inl rfl)) (add hv _)
  · apply Derives.impI
    exact RawCodeProjectionSyntax.output_subst head w n _ y (eq_symm (.hyp (Or.inl rfl))) (add hv _)

end PPAC.Migration.Internal.RawCodeProjectionCanonical
