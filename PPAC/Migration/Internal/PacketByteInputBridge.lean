import PPAC.Migration.Internal.PacketByteInputDecomposition

/-! Independent byte and list guards use the same internally unique radix 256. -/
namespace PPAC.Migration.Internal.PacketByteInputBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketByteInputSyntax PacketByteInputRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem byte_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (C h : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hb : Derives Γ (byte h)) : Derives Γ (.mem h C) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (.mem h.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ R) 256 (Fin.last m) C.castSucc (.conjL hR) hC1
  exact UnorderedPairLogic.mem_container_subst (Fin.last m) C.castSucc h.castSucc he (.conjR hR)

theorem actual_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (byteList w n)) : Derives Γ (inputAt w C n) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (inputAt w.castSucc (Fin.last m) n.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hi
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ R) 256 (Fin.last m) C.castSucc (.conjL hR) hC1
  simpa only [Formula.raise,inputAt_rename] using PacketByteInputProperties.radix_subst w.castSucc (Fin.last m) n.castSucc C.castSucc he (.conjR hR)

theorem actual_iff_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((byteList w n).iff (inputAt w C n)) :=
  .conjI (.impI (actual_at (ZFContext.add hZ _) w C n (add hC _) (.hyp (Or.inl rfl))))
    (.impI (intro_actual w C n (add hC _) (.hyp (Or.inl rfl))))

theorem cons_to_actual {m} {Γ : Context m} (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (consCase w C n)) : Derives Γ (actualCons w n) := by
  let R := consBody w C n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hc
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_body 2 hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hh := intro_byte (old 2 C) (slot 2 0) hC2 (.conjL (.conjR hR))
  have ht := intro_actual (old 2 w) (old 2 C) (slot 2 1) hC2 (.conjR (.conjR hR))
  exact of_eq (actualCons_rename w n (old 2)).symm (intro_actual_cons (old 2 w) (old 2 n) (slot 2 0) (slot 2 1) (.conjL hR) hh ht)

theorem actual_to_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (actualCons w n)) : Derives Γ (consCase w C n) := by
  let R := actualBody w n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hc
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_body 2 hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hh := byte_at hZ2 (old 2 C) (slot 2 0) hC2 (.conjL (.conjR hR))
  have ht := actual_at hZ2 (old 2 w) (old 2 C) (slot 2 1) hC2 (.conjR (.conjR hR))
  exact of_eq (consCase_rename w C n (old 2)).symm (intro_cons (old 2 w) (old 2 C) (old 2 n) (slot 2 0) (slot 2 1) (.conjL hR) hh ht)

theorem to_actual {m} {Γ : Context m} (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (criterionAt w C n)) : Derives Γ (criterion w n) := by
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (cons_to_actual w C n (add hC _) (.hyp (Or.inl rfl)))

theorem from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (criterion w n)) : Derives Γ (criterionAt w C n) := by
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (actual_to_cons (ZFContext.add hZ _) w C n (add hC _) (.hyp (Or.inl rfl)))

theorem cases_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((criterionAt w C n).iff (criterion w n)) :=
  .conjI (.impI (to_actual w C n (add hC _) (.hyp (Or.inl rfl))))
    (.impI (from_actual (ZFContext.add hZ _) w C n (add hC _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketByteInputBridge
