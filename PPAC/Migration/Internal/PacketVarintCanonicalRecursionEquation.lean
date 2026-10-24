import PPAC.Migration.Internal.PacketVarintCanonicalDecomposition

/-! The previously constructed actual canonical terminal and continuation graphs give the converse exact recursion. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalRecursionEquation
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintCanonicalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (smallCase w B n s)) : Derives Γ (canonicalAt w B n s) := by
  let E := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) s.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR hc)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  simpa only [Formula.raise,canonicalAt_rename] using PacketVarintConstruct.terminal_at hZ1 w.castSucc B.castSucc n.castSucc (Fin.last m) s.castSucc hw1 (under hB E) (under (.conjL hc) E) (.conjL hE) (.conjR hE)

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (largeCase false w B n s)) : Derives Γ (canonicalAt w B n s) := by
  let R := largeBody false w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (canonicalAt_rename w B n s (old 4)).symm
    (PacketVarintConstruct.continuation_at hZ4 (old 4 w) (old 4 B) (slot 4 1) (slot 4 3) (slot 4 0) (slot 4 2) (old 4 n) (old 4 s)
      hw4 (.conjL (.conjR hR)) (.conjL (.conjR (.conjR (.conjR hR)))) (.conjL hR) (.conjL (.conjR (.conjR hR))) (.conjR (.conjR (.conjR (.conjR hR)))))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (atCriterion false w B n s)) : Derives Γ (canonicalAt w B n s) := by
  apply Derives.disjE hc
  · exact small_backward (ZFContext.add hZ _) w B n s (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · exact large_backward (ZFContext.add hZ _) w B n s (add hw _) (.hyp (Or.inl rfl))

theorem at_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) : Derives Γ ((canonicalAt w B n s).iff (atCriterion false w B n s)) :=
  .conjI (.impI (PacketVarintCanonicalDecomposition.at_forward (ZFContext.add hZ _) w B n s (add hw _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w B n s (add hw _) (add hB _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketVarintCanonicalRecursionEquation
