import PPAC.Migration.Internal.PacketVarintCanonicalPieces

/-! Full raw fold decomposition, real canonical cells and actual shorter graphs give exact canonical reverse branches. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalDecomposition
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintCanonicalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem continuation_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B s n h x q z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (PacketVarintTraceSyntax.foldAt w B x z q))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (ht : Derives Γ (PacketVarintCellSyntax.continuation w B h q n)) :
    Derives Γ (largeCase false w B n s) := by
  let D := (empty q.castSucc).neg.conj ((PacketAffineSyntax.affine w.castSucc B.castSucc (Fin.last m) q.castSucc n.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc h.castSucc))
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) ht
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz D)
  have hf1 := of_eq (PacketVarintTraceSyntax.foldAt_rename w B x z q Fin.castSucc) (under hf D)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x s Fin.castSucc) (under hc D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hnonempty := PacketVarintCanonicalPieces.nonempty_suffix hZ1 w.castSucc B.castSucc x.castSucc z.castSucc q.castSucc hw1 hz1 hf1 (.conjL hD)
  have hp := intro_at w.castSucc B.castSucc q.castSucc x.castSucc z.castSucc hz1 hf1 hnonempty
  simpa only [Formula.raise,largeCase_rename] using intro_large false w.castSucc B.castSucc n.castSucc s.castSucc (Fin.last m) q.castSucc h.castSucc x.castSucc
    (.conjL (.conjR hD)) (.conjL hD) (.conjR (.conjR hD)) hp hc1

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B s z n h x q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (PacketVarintTraceSyntax.foldAt w B x z q))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (ht : Derives Γ (PacketVarintCellSyntax.cell w B x h q n)) :
    Derives Γ (atCriterion false w B n s) := by
  apply Derives.disjE (.conjR (.conjR (.conjR ht)))
  · exact .disjL (PacketVarintCanonicalPieces.terminal_point w B s n h x q (add hc _) (.hyp (Or.inl rfl)))
  · exact .disjR (continuation_point (ZFContext.add hZ _) w B s n h x q z (add hw _) (add hz _) (add hf _) (add hc _) (.hyp (Or.inl rfl)))

theorem cons_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B s z n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketVarintRecursionSyntax.consCase w B s z n)) :
    Derives Γ (atCriterion false w B n s) := by
  let R := PacketVarintRecursionSyntax.consBody w B s z n
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hz3 := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (atCriterion_rename false w B n s (old 3)).symm
    (cons_point hZ3 (old 3 w) (old 3 B) (old 3 s) (old 3 z) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)
      hw3 hz3 (.conjL (.conjR hR)) (.conjL hR) (.conjR (.conjR hR)))

theorem fold_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B s z n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (PacketVarintTraceSyntax.foldAt w B s z n))
    (hs : Derives Γ (StructuralListSyntax.nilCode w s).neg) : Derives Γ (atCriterion false w B n s) := by
  have hc := PacketVarintDecomposition.fold_forward hZ w B s z n hw hf
  apply Derives.disjE hc
  · exact .botE (.impE (add hs _) (.conjL (.hyp (Or.inl rfl))))
  · exact cons_case (ZFContext.add hZ _) w B s z n (add hw _) (add hz _) (.hyp (Or.inl rfl))

theorem at_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (canonicalAt w B n s)) : Derives Γ (atCriterion false w B n s) := by
  let Z := (empty (Fin.last m)).conj ((PacketVarintTraceSyntax.foldAt w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc).conj
    (StructuralListSyntax.nilCode w.castSucc s.castSucc).neg)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) hc
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  simpa only [Formula.raise,atCriterion_rename] using fold_point hZ1 w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc hw1 (.conjL hZ0) (.conjL (.conjR hZ0)) (.conjR (.conjR hZ0))

end PPAC.Migration.Internal.PacketVarintCanonicalDecomposition
