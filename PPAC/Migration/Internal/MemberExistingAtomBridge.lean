import PPAC.Migration.Internal.AtomicProgramAlignment

/-! 独立成员结果规格与既有FormulaTransformAtomSyntax.membership的全候选双向接口。 -/
namespace PPAC.Migration.Internal.MemberExistingAtomBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem to_existing {m} {Γ : Context m} (_hZ : ZFContext.Evidence Γ)
    (w R S a b c d s x y n q : Fin m)
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (hMaps : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
    (hp : Derives Γ (MemberProgramSyntax.returned w R S c d s x y q)) :
    Derives Γ (FormulaTransformAtomSyntax.membership w R S a b c d n q) := by
  let B := MemberProgramSyntax.body w R S c d s x y q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hp
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 h B
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 2 w) (old 2 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 2)) (lift hs)
  have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 2 w) (old 2 s) (old 2 x) (old 2 y) (old 2 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 2)) (lift hn)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 2 w) (old 2 a) (old 2 b) (SyntaxAtomSyntax.two (old 2 x) (old 2 y))) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (lift ht)
  have hMaps1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 R) (old 2 S)) := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a b c d R S (old 2)) (lift hMaps)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 0
  have hy := ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 1
  have hrx := ArgumentForestProgramSyntax.run_at 2 _ _ _ _ _ (.conjR (.conjR hB)) 0
  have hry := ArgumentForestProgramSyntax.run_at 2 _ _ _ _ _ (.conjR (.conjR hB)) 1
  have hCheckedX : Derives Δ (TermTransformProgramSyntax.checked (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 x) (slot 2 0)) := .conjI (.conjI hMaps1 hx) hrx
  have hCheckedY : Derives Δ (TermTransformProgramSyntax.checked (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 y) (slot 2 1)) := .conjI (.conjI hMaps1 hy) hry
  have hData := Derives.conjI hs1 (.conjI hn1 (.conjI (.conjL (.conjR hB)) (.conjI hCheckedX hCheckedY)))
  have ho := FormulaTransformAtomSyntax.intro_membership (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (old 2 q) (old 2 s) (old 2 x) (old 2 y) (slot 2 0) (slot 2 1) hData
  exact of_eq (FormulaTransformAtomSyntax.membership_rename w R S a b c d n q (old 2)).symm ho

theorem from_existing {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hp : Derives Γ (FormulaTransformAtomSyntax.membership w R S a b c d n q)) :
    Derives Γ (MemberProgramSyntax.returned w R S c d s x y q) := by
  let B := FormulaTransformAtomSyntax.membershipBody w R S a b c d n q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ hp
  have hZ1 := HornBinderRules.zf_body 5 hZ B
  have hw1 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 5 w) (old 5 s) (old 5 x) (old 5 y) (old 5 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 5)) (HornBinderRules.under_body 5 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hSource := Derives.conjL (Derives.conjR hB)
  have hSymbol := SyntaxNodeInjective.constructor_input_eq hZ1 3 2 2 (old 5 w) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 1) (slot 5 2)) (SyntaxAtomSyntax.three (old 5 s) (old 5 x) (old 5 y)) (old 5 n) 0 hw1 hSource hn1
  have hX := SyntaxNodeInjective.constructor_input_eq hZ1 3 2 2 (old 5 w) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 1) (slot 5 2)) (SyntaxAtomSyntax.three (old 5 s) (old 5 x) (old 5 y)) (old 5 n) 1 hw1 hSource hn1
  have hY := SyntaxNodeInjective.constructor_input_eq hZ1 3 2 2 (old 5 w) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 1) (slot 5 2)) (SyntaxAtomSyntax.three (old 5 s) (old 5 x) (old 5 y)) (old 5 n) 2 hw1 hSource hn1
  have hxChecked := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hB)))
  have hyChecked := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB)))
  have hxType := TermTransformProgramValue.target_type hZ1 (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 b) (old 5 c) (old 5 d) (slot 5 1) (slot 5 3) hw1 hxChecked
  have hyType := TermTransformProgramValue.target_type hZ1 (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 b) (old 5 c) (old 5 d) (slot 5 2) (slot 5 4) hw1 hyChecked
  have hxRun := ArgumentForestProgramSyntax.run_input_subst (old 5 w) (old 5 R) (old 5 S) (slot 5 1) (old 5 x) (slot 5 3) hX (.conjR hxChecked)
  have hyRun := ArgumentForestProgramSyntax.run_input_subst (old 5 w) (old 5 R) (old 5 S) (slot 5 2) (old 5 y) (slot 5 4) hY (.conjR hyChecked)
  have hMember := AtomicProgramAlignment.member_symbol_subst (old 5 w) (slot 5 0) (old 5 s) (slot 5 3) (slot 5 4) (old 5 q) hSymbol (.conjL (.conjR (.conjR hB)))
  have hTypes : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 5 w) (old 5 c) (old 5 d) (SyntaxAtomSyntax.two (slot 5 3) (slot 5 4))) := .conjI hxType (.conjI hyType (.eqRefl _))
  have hRuns : Derives Δ (ArgumentForestProgramSyntax.runs 2 (old 5 w) (old 5 R) (old 5 S) (SyntaxAtomSyntax.two (old 5 x) (old 5 y)) (SyntaxAtomSyntax.two (slot 5 3) (slot 5 4))) := .conjI hxRun (.conjI hyRun (.eqRefl _))
  have ho := MemberProgramSyntax.intro_returned (old 5 w) (old 5 R) (old 5 S) (old 5 c) (old 5 d) (old 5 s) (old 5 x) (old 5 y) (old 5 q) (slot 5 3) (slot 5 4) hTypes hMember hRuns
  exact of_eq (MemberProgramSyntax.returned_rename w R S c d s x y q (old 5)).symm ho

theorem iff_existing {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (hMaps : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S)) :
    Derives Γ ((MemberProgramSyntax.returned w R S c d s x y q).iff (FormulaTransformAtomSyntax.membership w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_existing (ZFContext.add hZ _) w R S a b c d s x y n q (add hs _) (add hn _) (add ht _) (add hMaps _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_existing (ZFContext.add hZ _) w R S a b c d s x y n q (add hw _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.MemberExistingAtomBridge
