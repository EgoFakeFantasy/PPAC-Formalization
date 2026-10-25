import PPAC.Migration.Internal.PacketReaderVarintSegmentSyntax

/-! The genuine continuation-byte branch consumes an actual canonical smaller segment. Intermediate value and scale are constructed and eliminated inside the object derivation. -/
namespace PPAC.Migration.Internal.PacketReaderVarintSegmentContinue
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderVarintSegmentSyntax
open PacketAffineSyntax (equation equation_rename affine affine_rename)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n d k h X Y T L v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hAff : Derives Γ (affine w B d k n)) (hk : Derives Γ (empty k).neg)
    (hSum : Derives Γ (sum w d B h)) (hCanonical : Derives Γ (PacketVarintSyntax.canonical w k X))
    (hSplice : Derives Γ (StructuralListSpliceSyntax.splice w X T Y)) (hHead : Derives Γ (StructuralListSyntax.consCode w h Y L))
    (hState : Derives Γ (PacketReaderStepSyntax.state w T v s a))
    (hValue : Derives Γ (equation w n v s u)) (hCons : Derives Γ (StructuralListSyntax.consCode w u a c))
    (hIH : Derives Γ (property w B z o k)) : Derives Γ (agreement w B z o L T v s a c p) := by
  have hdN := PacketAffineCore.digit_natural hZ w B d k n hw hAff
  have hvN := Derives.conjL (.conjR hState)
  have hsN := Derives.conjL (.conjR (.conjR hState))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (equation w.castSucc d.castSucc v.castSucc s.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderArithmetic.exists_equation hZ w d v s hw hdN hvN hsN)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (product w.castSucc.castSucc s.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) (ZFArithmetic.mul_exists hZ1 w.castSucc s.castSucc B.castSucc hw1 (under hsN R) (under hB R))
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under hh R) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have hAff2 : Derives Ξ (affine w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise,affine_rename] using lift hAff
  have hk2 : Derives Ξ (empty k.castSucc.castSucc).neg := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hk
  have hSum2 : Derives Ξ (sum w.castSucc.castSucc d.castSucc.castSucc B.castSucc.castSucc h.castSucc.castSucc) := by
    simpa only [Formula.raise,sum_rename] using lift hSum
  have hCanonical2 : Derives Ξ (PacketVarintSyntax.canonical w.castSucc.castSucc k.castSucc.castSucc X.castSucc.castSucc) := by
    simpa only [Formula.raise,PacketVarintSyntax.canonical_rename] using lift hCanonical
  have hSplice2 : Derives Ξ (StructuralListSpliceSyntax.splice w.castSucc.castSucc X.castSucc.castSucc T.castSucc.castSucc Y.castSucc.castSucc) := by
    simpa only [Formula.raise,StructuralListSpliceSyntax.splice_rename] using lift hSplice
  have hHead2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc Y.castSucc.castSucc L.castSucc.castSucc) := by
    simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hHead
  have hState2 : Derives Ξ (PacketReaderStepSyntax.state w.castSucc.castSucc T.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise,PacketReaderStepSyntax.state_rename] using lift hState
  have hValue2 : Derives Ξ (equation w.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise,equation_rename] using lift hValue
  have hCons2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc u.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hCons
  have hIH2 : Derives Ξ (property w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc k.castSucc.castSucc) := by
    simpa only [Formula.raise,property_rename] using lift hIH
  have hR2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (equation w.castSucc.castSucc d.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [R,Formula.raise,Formula.rename,equation_rename] using under hR Q
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) := by simpa only [Formula.raise,empty_rename] using lift hz
  have hd2 := PacketAffineCore.digit_natural hZ2 _ _ _ _ _ hw2 hAff2
  have hKN := PacketAffineCore.tail_guard _ _ _ _ _ hAff2
  have hVN := Derives.conjL (.conjR hState2)
  have hSN := Derives.conjL (.conjR (.conjR hState2))
  have hTailValue := PacketReaderAffineCompose.decompose hZ2 w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) u.castSucc.castSucc
    hw2 (lift hB) hd2 hKN hVN hSN (PacketAffineCore.equation_of_affine _ _ _ _ _ hAff2) (.conjR hR2) (.conjR hQ) hValue2
  have hUpdated : Derives Ξ (PacketReaderStepSyntax.state w.castSucc.castSucc T.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc) :=
    .conjI (.conjL hState2) (.conjI (.conjL hR2) (.conjI (.conjL hQ) (.conjR (.conjR (.conjR hState2)))))
  have hGuard : Derives Ξ (guard o.castSucc.castSucc k.castSucc.castSucc (Fin.last (m+1))) := .disjR hk2
  have hCase := at_fields w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc k.castSucc.castSucc X.castSucc.castSucc T.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc u.castSucc.castSucc c.castSucc.castSucc p.castSucc.castSucc hIH2
  have hSmall := Derives.impE (Derives.impE (Derives.impE (Derives.impE (Derives.impE (Derives.impE hCase hCanonical2) hSplice2) hUpdated) hGuard) hTailValue) hCons2
  have hYValid := Derives.conjL (.conjR hSplice2)
  have hOldY : Derives Ξ (PacketReaderStepSyntax.state w.castSucc.castSucc Y.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc) := .conjI hYValid (.conjR hState2)
  have hHN := ZFArithmetic.add_range hZ2 _ _ _ _ hw2 hd2 hSum2
  have hHeadRest : Derives Ξ (PacketReaderInputSyntax.headRest w.castSucc.castSucc L.castSucc.castSucc h.castSucc.castSucc Y.castSucc.castSucc) := .conjI hHN (.conjI hYValid hHead2)
  have hAdvance := PacketReaderVarintBranches.continuation_digit hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc h.castSucc.castSucc Y.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc
    hw2 (lift hB) hz2 (lift ho) hOldY hHeadRest hd2 hSum2 (.conjR hR2) (.conjR hQ)
  simpa only [Formula.raise,agreement,Formula.iff,Formula.rename,PacketReaderEvalSyntax.eval_rename] using StructuralListSuffixArithmetic.iff_trans hAdvance hSmall

end PPAC.Migration.Internal.PacketReaderVarintSegmentContinue
