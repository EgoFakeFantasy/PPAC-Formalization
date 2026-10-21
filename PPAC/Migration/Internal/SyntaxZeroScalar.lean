import PPAC.Migration.Internal.SyntaxAtomLogic

/-! membership的唯一关系编号0是原leaf(0)树码，恰为实际内部数码2；不混同编号和树码。 -/
namespace PPAC.Migration.Internal.SyntaxZeroScalar
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxNumeralSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (zeroScalar w s)) : Derives Γ (.mem s w) := SyntaxNodeInjective.constructor_range hZ 0 0 w Fin.elim0 s hw hs

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s t : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (zeroScalar w s)) (ht : Derives Γ (zeroScalar w t)) : Derives Γ (.equal s t) :=
  SyntaxConstructors.unique hZ 0 0 w Fin.elim0 s t hw hs ht

theorem index_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i s : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (scalar w i s)) : Derives Γ ((zeroScalar w s).iff (numeral 0 i)) := by
  apply Derives.conjI
  · apply Derives.impI
    let Z := zeroScalar w s
    let Ξ := Context.add Z Γ
    let C := constructorBody 0 0 w Fin.elim0 s
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    apply eliminate_constructor 0 0 w Fin.elim0 s _ (.hyp (Or.inl rfl))
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ Z) C
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw Z) C
    have hs1 : Derives Δ (scalar w.castSucc i.castSucc s.castSucc) := by simpa only [Formula.raise, scalar_rename] using under (add hs Z) C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have heq := SyntaxNodes.tags_equal hZ1 0 0 _ _ _ Fin.elim0 Fin.elim0 _ hw1 hs1 (.conjR hC)
    have hout := SyntaxNumeralSyntax.output_subst 0 _ _ (eq_symm heq) (.conjL hC)
    simpa only [Formula.raise, numeral_rename] using hout
  · apply Derives.impI
    exact intro_constructor 0 0 w Fin.elim0 s i (.hyp (Or.inl rfl)) (add hs _)

theorem at_two {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (successor n e)) : Derives Γ (zeroScalar w n) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hnil := StructuralNil.at_unit hZ w z e hw hz he
  have hraw := StructuralNil.leaf_zero hZ w z e n hw hz he hn
  exact intro_constructor 0 0 w Fin.elim0 n z hz (intro_node 0 w z Fin.elim0 n e hzN hnil hraw)

theorem from_numeral_two {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (numeral 2 n)) : Derives Γ (zeroScalar w n) := by
  let E := (numeral 1 (Fin.last m)).conj (successor n.castSucc (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  apply eliminate_succ 1 n _ hn
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  let Z := (numeral 0 (Fin.last (m+1))).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  apply eliminate_succ 0 (Fin.last m) _ (Derives.conjL hE)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ E) Z
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw E) Z
  have hsucc : Derives Δ (successor n.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, successor_rename] using under (Derives.conjR hE) Z
  have hZ : Derives Δ Z := .hyp (Or.inl rfl)
  have hout := at_two hZ2 _ _ _ _ hw2 (.conjL hZ) (.conjR hZ) hsucc
  simpa only [Formula.raise, zeroScalar_rename] using hout

theorem to_numeral_two {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (zeroScalar w n)) : Derives Γ (numeral 2 n) := by
  have ht := SyntaxNumerals.exists_numeral hZ 2 w hw
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (numeral 2 (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hn1 : Derives Δ (zeroScalar w.castSucc n.castSucc) := by simpa only [Formula.raise, zeroScalar_rename] using under hn T
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hc := from_numeral_two hZ1 _ _ hw1 (.conjR hT)
  have heq := unique hZ1 _ _ _ hw1 hn1 hc
  have hout := SyntaxNumeralSyntax.output_subst 2 _ _ (eq_symm heq) (.conjR hT)
  simpa only [Formula.raise, numeral_rename] using hout

theorem two_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((zeroScalar w n).iff (numeral 2 n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_numeral_two (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_numeral_two (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxZeroScalar
