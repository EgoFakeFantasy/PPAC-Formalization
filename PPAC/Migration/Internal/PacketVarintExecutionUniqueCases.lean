import PPAC.Migration.Internal.PacketVarintExecutionUniqueValues

/-! Both complete singleton or EX4 continuation witness blocks are object-eliminated before branch comparison. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionUniqueCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hs : Derives Γ (PacketVarintCanonicalRecursionSyntax.smallCase w B n s)) (ht : Derives Γ (PacketVarintCanonicalRecursionSyntax.smallCase w B n t)) : Derives Γ (.equal s t) := by
  have hn := StructuralListTraceOrder.member_member hZ w n B hw (SyntaxNumerals.range hZ 128 w B hw hB) (.conjL hs)
  let E := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) s.castSucc)
  let ΓE := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR hs)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have ht1 := of_eq (PacketVarintCanonicalRecursionSyntax.smallCase_rename w B n t Fin.castSucc) (under ht E)
  let F := (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1))).conj (StructuralListSyntax.consCode w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) t.castSucc.castSucc)
  let Δ := Context.add F (Context.image Formula.raise ΓE)
  apply Derives.exE (p := F) (.conjR ht1)
  have hZ2 := ZFContext.under hZ1 F
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 F)
  have hE : Derives ΓE E := .hyp (Or.inl rfl)
  have he2 := of_eq (StructuralListSyntax.nilCode_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hE) F)
  have hs2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc n.castSucc (Fin.last m) s.castSucc Fin.castSucc) (under (.conjR hE) F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  exact PacketVarintExecutionUniqueValues.small_values hZ2 w.castSucc.castSucc n.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (under (under hn E) F) he2 (.conjL hF) hs2 (.conjR hF)

theorem large_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (hs : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n s)) (ht : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n t)) : Derives Γ (.equal s t) := by
  let R := PacketVarintCanonicalRecursionSyntax.largeBody true w B n s
  let ΓR := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hs
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hi4 := of_eq (earlier_rename w n (old 4)) (HornBinderRules.under_body 4 hi R)
  have ht4 := of_eq (PacketVarintCanonicalRecursionSyntax.largeCase_rename true w B n t (old 4)) (HornBinderRules.under_body 4 ht R)
  let S := PacketVarintCanonicalRecursionSyntax.largeBody true (old 4 w) (old 4 B) (old 4 n) (old 4 t)
  let Δ := Context.add S (raisedContext 4 ΓR)
  apply HornBinderRules.eliminate_many 4 S _ ht4
  have hZ8 := HornBinderRules.zf_body 4 hZ4 S
  have hw8 := of_eq (omega_rename (old 4 w) (old 4)) (HornBinderRules.under_body 4 hw4 S)
  have hB8 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 (old 4 B) (old 4)) (HornBinderRules.under_body 4 hB4 S)
  have hi8 := of_eq (earlier_rename (old 4 w) (old 4 n) (old 4)) (HornBinderRules.under_body 4 hi4 S)
  have hR : Derives ΓR R := .hyp (Or.inl rfl)
  have ha0 := of_eq (PacketAffineSyntax.affine_rename (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) (old 4)) (HornBinderRules.under_body 4 (.conjL hR) S)
  have hq0 : Derives Δ (empty (old 4 (slot 4 1 : Fin (m+4)))).neg := by
    simpa only [Formula.rename,Formula.neg,empty_rename] using HornBinderRules.under_body 4 (.conjL (.conjR hR)) S
  have hs0 := of_eq (NaturalAdditionSyntax.sum_rename (old 4 w) (slot 4 0) (old 4 B) (slot 4 2) (old 4)) (HornBinderRules.under_body 4 (.conjL (.conjR (.conjR hR))) S)
  have hx0 := of_eq (canonical_rename (old 4 w) (slot 4 1) (slot 4 3) (old 4)) (HornBinderRules.under_body 4 (.conjL (.conjR (.conjR (.conjR hR)))) S)
  have hc0 := of_eq (StructuralListSyntax.consCode_rename (old 4 w) (slot 4 2) (slot 4 3) (old 4 s) (old 4)) (HornBinderRules.under_body 4 (.conjR (.conjR (.conjR (.conjR hR)))) S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact PacketVarintExecutionUniqueValues.values hZ8 (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (old 4 n)) (old 4 (old 4 s)) (old 4 (old 4 t))
    (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (slot 4 2)) (old 4 (slot 4 3)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    hw8 hB8 hi8 ha0 (.conjL hS) hq0 hs0 (.conjL (.conjR (.conjR hS))) hx0 (.conjL (.conjR (.conjR (.conjR hS)))) hc0 (.conjR (.conjR (.conjR (.conjR hS))))

end PPAC.Migration.Internal.PacketVarintExecutionUniqueCases
