import PPAC.Migration.Internal.PureSyntaxMembershipInput
import PPAC.Migration.Internal.ArgumentPairOutput

/-! 固定符号零载荷与纯成员码、内部二项有类型森林的对象对应。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipType
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem data_app_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w zero args n : Fin m)
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 zero)) :
    Derives Γ ((PureSyntaxMembershipInput.data w args n).iff (OriginalFormulaApplicationSyntax.application w zero args n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := PureSyntaxMembershipInput.data w args n
    let B := PureSyntaxMembershipInput.body w args n
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have hz3 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 3 zero)) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 zero (old 3)) (HornBinderRules.under_body 3 (add hz E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := OriginalFormulaMemberApplication.scalar_at_zero hZ3 (old 3 w) (old 3 zero) (slot 3 0) hz3 (.conjL hB)
    have ho := OriginalFormulaApplicationSyntax.intro_application (old 3 w) (old 3 zero) (old 3 args) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hs (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
    exact of_eq (OriginalFormulaApplicationSyntax.application_rename w zero args n (old 3)).symm ho
  · apply Derives.impI
    let E := OriginalFormulaApplicationSyntax.application w zero args n
    let B := OriginalFormulaApplicationSyntax.body w zero args n
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hz3 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 3 zero)) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 zero (old 3)) (HornBinderRules.under_body 3 (add hz E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := SyntaxNodeSyntax.intro_constructor 0 0 (old 3 w) Fin.elim0 (slot 3 0) (old 3 zero) hz3 (.conjL hB)
    have ho := PureSyntaxMembershipInput.intro_data (old 3 w) (old 3 args) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hs (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
    exact of_eq (PureSyntaxMembershipInput.data_rename w args n (old 3)).symm ho

theorem at_forest_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s x y args n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hf : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args)) :
    Derives Γ ((PureSyntaxMembershipInput.data w args n).iff (SyntaxAtomSyntax.memberCode w s x y n)) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (Source.SetLanguage.empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (.conjL (.conjL hw))
  have hZ1 := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w.castSucc s.castSucc) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s Fin.castSucc) (under hs Z)
  have hf1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) args.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hf Z)
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have ho := SyntaxTypeLocalTransfer.iff_trans (data_app_iff hZ1 w.castSucc (Fin.last m) args.castSucc n.castSucc (.conjR hZ0))
    (OriginalFormulaMemberApplication.member_at_forest_iff hZ1 w.castSucc (Fin.last m) s.castSucc x.castSucc y.castSucc args.castSucc n.castSucc hw1 (.conjR hZ0) hs1 hf1)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, PureSyntaxMembershipInput.data_rename, SyntaxAtomSyntax.memberCode_rename]) ho

theorem from_typed_forest {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f args n x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (PureSyntaxMembershipInput.data w args n))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w b f (SyntaxAtomSyntax.two x y)))
    (hf : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (SyntaxConstructors.exists_constructor hZ 0 0 w Fin.elim0 hw (.eqRefl w))
  have hZ1 := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hd1 : Derives Δ (PureSyntaxMembershipInput.data w.castSucc args.castSucc n.castSucc) := of_eq (PureSyntaxMembershipInput.data_rename w args n Fin.castSucc) (under hd Z)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc b.castSucc f.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq
    (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht Z)
  have hf1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) args.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hf Z)
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have hcode := Derives.impE (.conjL (at_forest_iff hZ1 _ _ _ _ _ _ hw1 (.conjR hZ0) hf1)) hd1
  have hx := ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 0
  have hy := ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 1
  have ho := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ1 _ _ _ _ _ _ _ hw1 hcode)) (.conjI (.conjR hZ0) (.conjI hx hy))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f Fin.castSucc).symm ho

theorem from_pair_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f args n : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (PureSyntaxMembershipInput.data w args n))
    (hp : Derives Γ (ArgumentPairOutput.output w b f args)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := ArgumentPairOutput.body w b f args
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hp
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hd2 : Derives Δ (PureSyntaxMembershipInput.data (old 2 w) (old 2 args) (old 2 n)) := of_eq (PureSyntaxMembershipInput.data_rename w args n (old 2)) (HornBinderRules.under_body 2 hd B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := from_typed_forest hZ2 (old 2 w) (old 2 b) (old 2 f) (old 2 args) (old 2 n) (slot 2 0) (slot 2 1) hw2 hd2 (.conjL hB) (.conjR hB)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 2)).symm ho

theorem from_typed_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f args n len : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (PureSyntaxMembershipInput.data w args n))
    (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len)) (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w len b f args)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) :=
  from_pair_output hZ w b f args n hw hd (ArgumentPairOutput.exists_output hZ w len b f args hw hl ht)

end PPAC.Migration.Internal.PureSyntaxMembershipType
