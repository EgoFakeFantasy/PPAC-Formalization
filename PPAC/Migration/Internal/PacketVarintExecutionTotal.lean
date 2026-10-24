import PPAC.Migration.Internal.PacketVarintExecutionHelpers

/-! Real Nil/Cons, canonical suffixes and addition witnesses construct an actual canonical list for every input. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionTotal
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_at_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n e : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n B))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) : Derives Γ (existsList w n) := by
  have hnN := StructuralListTraceOrder.member_member hZ w n B hw (SyntaxNumerals.range hZ 128 w B hw hB) hn
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc n.castSucc e.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ w n e hw hnN (StructuralNil.range hZ w e hw he))
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB S)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hc := PacketVarintConstruct.terminal hZ1 w.castSucc B.castSucc n.castSucc e.castSucc (Fin.last m) hw1 hB1 (under hn S) he1 (.conjR hS)
  simpa only [Formula.raise,existsList_rename] using intro_list w.castSucc n.castSucc (Fin.last m) (.conjL hS) hc

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n B)) : Derives Γ (existsList w n) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using OrderedPairElimination.under_two hw U
  have hB2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using OrderedPairElimination.under_two hB U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have he := StructuralNil.at_unit hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hU) (.conjR hU)
  simpa only [Formula.raise,existsList_rename] using small_at_nil hZ2 w.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) hw2 hB2 (OrderedPairElimination.under_two hn U) he

theorem from_shift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q x h : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hq : Derives Γ (empty q).neg)
    (hx : Derives Γ (canonical w q x)) (ha : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) : Derives Γ (existsList w n) := by
  have hh := ZFArithmetic.add_range hZ w d B h hw (PacketAffineCore.digit_natural hZ w B d q n hw ha) hs
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc h.castSucc x.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ w h x hw hh (PacketVarintExecutionHelpers.list_natural w q x hx))
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB S)
  have hq1 : Derives Δ (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq S
  have hx1 := of_eq (canonical_rename w q x Fin.castSucc) (under hx S)
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under ha S)
  have hs1 := of_eq (NaturalAdditionSyntax.sum_rename w d B h Fin.castSucc) (under hs S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hc := PacketVarintConstruct.continuation hZ1 w.castSucc B.castSucc q.castSucc x.castSucc d.castSucc h.castSucc n.castSucc (Fin.last m) hw1 hB1 hq1 hx1 ha1 hs1 (.conjR hS)
  simpa only [Formula.raise,existsList_rename] using intro_list w.castSucc n.castSucc (Fin.last m) (.conjL hS) hc

theorem from_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q x : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hq : Derives Γ (empty q).neg)
    (hx : Derives Γ (canonical w q x)) (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) : Derives Γ (existsList w n) := by
  let H := (Formula.mem (Fin.last m) w.castSucc).conj (NaturalAdditionSyntax.sum w.castSucc d.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) (ZFArithmetic.add_exists hZ w d B hw (PacketAffineCore.digit_natural hZ w B d q n hw ha) (PacketAffineCore.radix_guard _ _ _ _ _ ha))
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB H)
  have hq1 : Derives Δ (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq H
  have hx1 := of_eq (canonical_rename w q x Fin.castSucc) (under hx H)
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under ha H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  simpa only [Formula.raise,existsList_rename] using from_shift hZ1 w.castSucc B.castSucc n.castSucc d.castSucc q.castSucc x.castSucc (Fin.last m) hw1 hB1 hq1 hx1 ha1 (.conjR hH)

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hn : Derives Γ (Formula.mem n B).neg) : Derives Γ (existsList w n) := by
  have hq := PacketTokenByteBounds.quotient_nonzero hZ w B d q n hw ha hn
  have hp := PacketVarintExecutionHelpers.below_property hZ w B n d q hw hB hi ha hq
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (canonical w.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (.conjL hp)
  have hZ1 := ZFContext.under hZ X
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw X)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB X)
  have hq1 : Derives Δ (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq X
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under ha X)
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  simpa only [Formula.raise,existsList_rename] using from_list hZ1 w.castSucc B.castSucc n.castSucc d.castSucc q.castSucc (Fin.last m) hw1 hB1 hq1 (.conjR hX) ha1

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (earlier w n)) : Derives Γ (existsList w n) := by
  apply SourcePropositional.by_cases (Formula.mem n B) (existsList w n)
  · exact small_point (ZFContext.add hZ _) w B n (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · let N := (Formula.mem n B).neg
    let R := PacketDivisionSyntax.decompositionBody w B n
    let Δ := Context.add R (raisedContext 2 (Context.add N Γ))
    apply HornBinderRules.eliminate_many 2 R _ (add (PacketDivisionInduction.exists_decomposition hZ false w B n hw hB hn) N)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ N) R
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw N) R)
    have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_body 2 (add hB N) R)
    have hi2 := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_body 2 (add hi N) R)
    have hn2 : Derives Δ (Formula.mem (old 2 n) (old 2 B)).neg := by
      simpa only [N,Formula.rename,Formula.neg] using HornBinderRules.under_body 2 (Derives.hyp (Γ := Context.add N Γ) (Or.inl rfl)) R
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    exact of_eq (existsList_rename w n (old 2)).symm (large_point hZ2 (old 2 w) (old 2 B) (old 2 n) (slot 2 0) (slot 2 1) hw2 hB2 hi2 hR hn2)

end PPAC.Migration.Internal.PacketVarintExecutionTotal
