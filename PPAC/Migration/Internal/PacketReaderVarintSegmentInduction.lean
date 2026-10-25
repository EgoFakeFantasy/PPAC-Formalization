import PPAC.Migration.Internal.PacketReaderVarintSegmentCases

/-! Full original Separation and Foundation discharge every smaller-token assumption in one fixed object Formula5. -/
namespace PPAC.Migration.Internal.PacketReaderVarintSegmentInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderVarintSegmentSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (earlier w B z o n)) : Derives Γ (property w B z o n) := by
  apply OriginalUniversalBlock.intro_many 9 (body w B z o n)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let A := PacketVarintSyntax.canonical (old 9 w) (old 9 n) (slot 9 0)
  let S := StructuralListSpliceSyntax.splice (old 9 w) (slot 9 0) (slot 9 1) (slot 9 2)
  let T := PacketReaderStepSyntax.state (old 9 w) (slot 9 1) (slot 9 3) (slot 9 4) (slot 9 5)
  let G := guard (old 9 o) (old 9 n) (slot 9 4)
  let U := PacketAffineSyntax.equation (old 9 w) (old 9 n) (slot 9 3) (slot 9 4) (slot 9 6)
  let C := StructuralListSyntax.consCode (old 9 w) (slot 9 6) (slot 9 5) (slot 9 7)
  let Δ := Context.add C (Context.add U (Context.add G (Context.add T (Context.add S (Context.add A (raisedContext 9 Γ))))))
  have hZ9 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 9 hZ) A) S) T) G) U) C
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 9)) := add (add (add (add (add (add (HornBinderRules.under_many 9 hh) A) S) T) G) U) C
  have hw9 := of_eq (omega_rename w (old 9)) (lift hw)
  have hB9 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 9)) (lift hB)
  have hz9 := of_eq (empty_rename z (old 9)) (lift hz)
  have hi9 := of_eq (earlier_rename w B z o n (old 9)) (lift hi)
  have hA : Derives Δ A := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hS : Derives Δ S := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hT : Derives Δ T := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hG : Derives Δ G := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hU : Derives Δ U := .hyp (Or.inr (Or.inl rfl))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact PacketReaderVarintSegmentCases.point hZ9 (old 9 w) (old 9 B) (old 9 z) (old 9 o) (old 9 n) (slot 9 0) (slot 9 1) (slot 9 2) (slot 9 3) (slot 9 4) (slot 9 5) (slot 9 6) (slot 9 7) (slot 9 8)
    hw9 hB9 hz9 (lift ho) hi9 hA hS hT hG hU hC

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w)) :
    Derives Γ (BoundedInduction.progressive PacketReaderVarintSegmentSyntax.matrix (PacketVarintPrefixRecursionSyntax.four w B z o) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,PacketReaderVarintSegmentSyntax.matrix_pred,paramsUp,PacketVarintPrefixRecursionSyntax.four]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ.raise := add (add (Derives.rename Fin.castSucc hh) N) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise,empty_rename] using lift hz
  exact property_from_earlier hZ1 w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) hw1 hB1 hz1 (lift ho) (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w)) :
    Derives Γ (allProperties w B z o) := by
  have h := BoundedInduction.induction_on_set PacketReaderVarintSegmentSyntax.matrix (PacketVarintPrefixRecursionSyntax.four w B z o) w
    (ZFContext.separation hZ PacketReaderVarintSegmentSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w B z o hw hB hz ho)
  have h0 : PacketVarintPrefixRecursionSyntax.four w B z o (0 : Fin 4) = w := rfl
  have h1 : PacketVarintPrefixRecursionSyntax.four w B z o (1 : Fin 4) = B := rfl
  have h2 : PacketVarintPrefixRecursionSyntax.four w B z o (2 : Fin 4) = z := rfl
  have h3 : PacketVarintPrefixRecursionSyntax.four w B z o (3 : Fin 4) = o := rfl
  simpa only [allProperties,BoundedInduction.holds,PacketReaderVarintSegmentSyntax.matrix_pred,paramsUp,h0,h1,h2,h3] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hn : Derives Γ (.mem n w)) : Derives Γ (property w B z o n) := by
  have h : Derives Γ ((Formula.mem n w).imp (property w B z o n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE n (all_properties hZ w B z o hw hB hz ho))
  exact .impE h hn

theorem segment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T L v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hCanonical : Derives Γ (PacketVarintSyntax.canonical w n C)) (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a)) (hG : Derives Γ (guard o n s))
    (hu : Derives Γ (PacketAffineSyntax.equation w n v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ (agreement w B z o L T v s a c p) := by
  have hProp := at_code hZ w B z o n hw hB hz ho (.conjL (PacketVarintDomain.domain w n C hCanonical))
  have hCase := at_fields w B z o n C T L v s a u c p hProp
  exact .impE (.impE (.impE (.impE (.impE (.impE hCase hCanonical) hSp) hT) hG) hu) hc

end PPAC.Migration.Internal.PacketReaderVarintSegmentInduction
