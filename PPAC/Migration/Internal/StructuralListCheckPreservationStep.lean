import PPAC.Migration.Internal.StructuralListCheckUnique

/-! 首次终端以前，真实tail一步保持并反射原Valid；不将Valid用于检查定义。 -/
namespace PPAC.Migration.Internal.StructuralListCheckPreservationStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
open StructuralListTraceSyntax (valid valid_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem valid_nonterminal_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hno : Derives Γ (terminal w n).neg) (hv : Derives Γ (valid w n)) :
    Derives Γ (hasCons false w n) := by
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hv
  apply Derives.disjE hd
  · exact .botE (.impE (add hno _) (.disjR (.hyp (Or.inl rfl))))
  · let P := StructuralListDecodeSyntax.tailCase w n
    let Γp := Context.add P Γ
    let T := (valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Ξ := Context.add T (Context.image Formula.raise Γp)
    have ht : Derives Γp (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) ht
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have htW := StructuralListValidity.range _ _ (.conjL hT)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hh : Derives Ξ (.ex H) := .conjR hT
    apply Derives.exE (p := H) hh
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have hsel := StructuralListProjection.selected_cons false _ _ _ _ (.conjL hH) (under htW H) (.conjR hH)
    have hout := intro_hasCons false _ _ _ hsel
    simpa only [Formula.raise, hasCons_rename] using hout

theorem off_invalid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hno : Derives Γ (terminal w n).neg) (hc : Derives Γ (hasCons false w n).neg) :
    Derives Γ (valid w n).neg := by
  apply Derives.impI
  exact .impE (add hc _) (valid_nonterminal_cons (ZFContext.add hZ _) _ _ (add hw _) (add hno _) (.hyp (Or.inl rfl)))

theorem preserve {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b : Fin m)
    (hw : Derives Γ (omega w)) (hno : Derives Γ (terminal w n).neg) (hs : Derives Γ (step false w n b)) :
    Derives Γ ((valid w n).iff (valid w b)) := by
  apply Derives.disjE hs
  · let C := selected false w n b
    let Γc := Context.add C Γ
    let H := body false w.castSucc n.castSucc b.castSucc (Fin.last m)
    let Δ := Context.add H (Context.image Formula.raise Γc)
    have hh : Derives Γc (.ex H) := .hyp (Or.inl rfl)
    apply Derives.exE (p := H) hh
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ C) H
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw C) H
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have hout := StructuralListDecode.cons_iff hZ1 _ _ _ _ hw1 (.conjR (.conjL hH)) (.conjL (.conjL hH)) (.conjR hH)
    simpa only [Formula.raise, Formula.rename, Formula.iff, valid_rename] using hout
  · let C := (hasCons false w n).neg.conj (empty b)
    let Δ := Context.add C Γ
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hnv := off_invalid (ZFContext.add hZ C) _ _ (add hw C) (add hno C) (.conjL hC)
    have hbv := StructuralListDecode.zero_rejected (ZFContext.add hZ C) _ _ (add hw C) (.conjR hC)
    apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (add hnv _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .botE (.impE (add hbv _) (.hyp (Or.inl rfl)))

theorem valid_equal_iff {m} {Γ : Context m} (w a b : Fin m) (he : Derives Γ (.equal a b)) : Derives Γ ((valid w a).iff (valid w b)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact StructuralListTraceSyntax.output_subst _ _ _ (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact StructuralListTraceSyntax.output_subst _ _ _ (eq_symm (add he _)) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListCheckPreservationStep
