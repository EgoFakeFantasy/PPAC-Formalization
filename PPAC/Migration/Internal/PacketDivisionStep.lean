import PPAC.Migration.Internal.PacketDivisionTransitions

/-! Digit successor below radix gives the ordinary branch or a proved carry; all witnesses stay internal. -/
namespace PPAC.Migration.Internal.PacketDivisionStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketDivisionSyntax PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)

theorem carry_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) (hs : Derives Γ (successor s n)) (hc : Derives Γ (successor B d)) :
    Derives Γ (decomposes w B s) := by
  have hz := SyntaxNumerals.exists_numeral hZ 0 w hw
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) hz
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB Z)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha Z)
  have hs1 := of_eq (successor_rename s n Fin.castSucc) (under hs Z)
  have hc1 := of_eq (successor_rename B d Fin.castSucc) (under hc Z)
  have hZero : Derives Δ Z := .hyp (Or.inl rfl)
  have hzB := PacketAffineLiteral.zero_below hZ1 wide w.castSucc B.castSucc (Fin.last m)
    (.conjI (radix_guard _ _ _ _ _ ha1) hB1) (.conjR hZero)
  have hQ := OriginalBinderStepSyntax.successor_exists w.castSucc q.castSucc hw1 (tail_guard _ _ _ _ _ ha1)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) q.castSucc.castSucc)
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hQ
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have ha2 := of_eq (affine_rename w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc Fin.castSucc) (under ha1 Q)
  have hs2 := of_eq (successor_rename s.castSucc n.castSucc Fin.castSucc) (under hs1 Q)
  have hc2 := of_eq (successor_rename B.castSucc d.castSucc Fin.castSucc) (under hc1 Q)
  have hz2 := of_eq (empty_rename (Fin.last m) Fin.castSucc) (under (.conjR hZero) Q)
  have hQ2 : Derives Ξ Q := .hyp (Or.inl rfl)
  have hA := PacketDivisionTransitions.carry hZ2 w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc
    n.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 ha2 hs2 hc2 (.conjR hQ2) hz2 (under hzB Q)
  have ho := intro_decomposes w.castSucc.castSucc B.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hA
  simpa only [Formula.raise, decomposes_rename] using ho

theorem from_affine {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) (hs : Derives Γ (successor s n)) : Derives Γ (decomposes w B s) := by
  have hd := OriginalBinderStepSyntax.successor_exists w d hw (digit_natural hZ w B d q n hw ha)
  let D := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) d.castSucc)
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) hd
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB D)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha D)
  have hs1 := of_eq (successor_rename s n Fin.castSucc) (under hs D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hb := GodelPairArithmetic.successor_below hZ1 w.castSucc d.castSucc B.castSucc (Fin.last m) hw1
    (digit_natural hZ1 _ _ _ _ _ hw1 ha1) (radix_guard _ _ _ _ _ ha1) (.conjR hD) (digit_guard _ _ _ _ _ ha1)
  apply Derives.disjE hb
  · have he : Derives (Context.add (Formula.equal (Fin.last m) B.castSucc) Δ) (.equal (Fin.last m) B.castSucc) := .hyp (Or.inl rfl)
    have hc := NaturalAdditionAlgebraLaws.successor_output_subst (Fin.last m) B.castSucc d.castSucc he (add (.conjR hD) _)
    exact of_eq (decomposes_rename w B s Fin.castSucc).symm
      (carry_exists (ZFContext.add hZ1 _) wide w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc s.castSucc
        (add hw1 _) (add hB1 _) (add ha1 _) (add hs1 _) hc)
  · have hA := PacketDivisionTransitions.increment (ZFContext.add hZ1 _) w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc s.castSucc
      (Fin.last m) (add hw1 _) (add ha1 _) (add hs1 _) (add (.conjR hD) _) (.hyp (Or.inl rfl))
    exact of_eq (decomposes_rename w B s Fin.castSucc).symm
      (intro_decomposes w.castSucc B.castSucc s.castSucc (Fin.last m) q.castSucc hA)

theorem from_decomposition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hi : Derives Γ (decomposes w B n)) (hs : Derives Γ (successor s n)) : Derives Γ (decomposes w B s) := by
  let C := decompositionBody w B n
  let Δ := Context.add C (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hi
  have hw2 := of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw C)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hB C)
  have hs2 := of_eq (successor_rename s n (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hs C)
  exact of_eq (decomposes_rename w B s (HornBinderSyntax.old 2)).symm
    (from_affine (HornBinderRules.zf_body 2 hZ C) wide (HornBinderSyntax.old 2 w) (HornBinderSyntax.old 2 B)
      (HornBinderSyntax.slot 2 0) (HornBinderSyntax.slot 2 1) (HornBinderSyntax.old 2 n) (HornBinderSyntax.old 2 s)
      hw2 hB2 (.hyp (Or.inl rfl)) hs2)

end PPAC.Migration.Internal.PacketDivisionStep
