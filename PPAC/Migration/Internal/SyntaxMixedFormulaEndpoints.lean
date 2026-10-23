import PPAC.Migration.Internal.SyntaxMixedFormulaSelectedIff

/-! 合法输入下原十一构造的精确端点律；量词同时使用两张实际提升环境码。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxMixedFormulaOutputSyntax SyntaxMixedFormulaJudgmentSyntax SyntaxMixedFormulaKnownFieldsSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((substituted w r s a b c d n q).iff (equalOperands w r s a b c d x y X Y)) := by
  have h1 := SyntaxMixedFormulaSelectedIff.source_case hZ 3 2 w r s a b c d n q (SyntaxAtomSyntax.two x y) hw hi hc
  have h2 := SyntaxMixedFormulaRawFields.equality_iff hZ w r s a b c d n q x y X Y hw hc hd
  exact SyntaxTypeLocalTransfer.iff_trans h1 h2

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q z Z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((substituted w r s a b c d n q).iff (memberOperands w r s a b c d z Z x y X Y)) := by
  have h1 := SyntaxMixedFormulaSelectedIff.source_case hZ 2 3 w r s a b c d n q (SyntaxAtomSyntax.three z x y) hw hi hc
  have h2 := SyntaxMixedFormulaRawFields.membership_iff hZ w r s a b c d n q z Z x y X Y hw hc hd
  exact SyntaxTypeLocalTransfer.iff_trans h1 h2

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w r s a b c d n q x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hd : Derives Γ (SyntaxLogicalSyntax.singleCode tag w X q)) :
    Derives Γ ((substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d X)) := by
  have h1 : Derives Γ ((substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.single tag advance w r s a b c d n q)) := by
    rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 4 1 w r s a b c d n q (fun _ => x) hw hi hc
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 9 1 w r s a b c d n q (fun _ => x) hw hi hc
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 10 1 w r s a b c d n q (fun _ => x) hw hi hc
  exact SyntaxTypeLocalTransfer.iff_trans h1 (SyntaxMixedFormulaRawFields.single_iff hZ tag advance w r s a b c d n q x X hw hc hd)

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((substituted w r s a b c d n q).iff ((substituted w r s a b c d x X).conj (substituted w r s a b c d y Y))) := by
  have h1 : Derives Γ ((substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.binary kind w r s a b c d n q)) := by
    have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 5 2 w r s a b c d n q (SyntaxAtomSyntax.two x y) hw hi hc
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 6 2 w r s a b c d n q (SyntaxAtomSyntax.two x y) hw hi hc
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 7 2 w r s a b c d n q (SyntaxAtomSyntax.two x y) hw hi hc
    · exact SyntaxMixedFormulaSelectedIff.source_case hZ 8 2 w r s a b c d n q (SyntaxAtomSyntax.two x y) hw hi hc
  exact SyntaxTypeLocalTransfer.iff_trans h1 (SyntaxMixedFormulaRawFields.binary_iff hZ kind w r s a b c d n q x y X Y hw hc hd)

theorem nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((substituted w r s a b c d n q).iff (.equal q n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxMixedFormulaNullary.unique (ZFContext.add hZ _) truth w r s a b c d n q (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxMixedFormulaJudgmentSubst.subst_q w r s a b c d n n q (eq_symm (.hyp (Or.inl rfl)))
      (SyntaxMixedFormulaNullary.intro_self (ZFContext.add hZ _) truth w r s a b c d n (add hw _) (add hi _) (add hc _))

theorem quantified_at_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w r s a b c d n q x X A C K H : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (input w r s a b c d n)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hd : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q)) :
    Derives Γ ((substituted w r s a b c d n q).iff (substituted w K H A b C d x X)) := by
  have hp : Derives Γ ((substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.advanced w x r s a b c d X)) := by
    cases universal
    · exact single_iff hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w r s a b c d n q x X hw hi hc hd
    · exact single_iff hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w r s a b c d n q x X hw hi hc hd
  exact SyntaxTypeLocalTransfer.iff_trans hp (SyntaxMixedFormulaAdvancedOutput.at_lift hZ w x r s a b c d X A C K H hw hl)
end PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints
