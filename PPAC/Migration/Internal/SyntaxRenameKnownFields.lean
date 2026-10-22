import PPAC.Migration.Internal.SyntaxRenameKnownSource

/-! 给定原两端构造的正式 RenameFormula 精确律；规范子判断恢复 Input，不额外假定合法源码。 -/
namespace PPAC.Migration.Internal.SyntaxRenameKnownFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameKnownFieldsSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem remove_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m) (P : Formula m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (P.imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))
    (hl : Derives Γ ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P))) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P) := by
  apply Derives.conjI
  · apply Derives.impI
    let Q := SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q
    have hQ : Derives (Context.add Q Γ) Q := .hyp (Or.inl rfl)
    have hI := SyntaxRenameOutput.input_of_renamed (ZFContext.add hZ Q) w R S a b c d n q (add hw Q) hQ
    exact .impE (.conjL (.impE (add hl Q) hI)) hQ
  · apply Derives.impI
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    exact .impE (.conjR (.impE (add hl P) (.impE (add hi P) hP))) hP

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S r s a b c d n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (equalOperands w r s a b c d x y X Y)) := by
  let P := equalOperands w r s a b c d x y X Y
  have hi : Derives Γ (P.imp (SyntaxRenameOutputSyntax.input w R S a b c d n)) := by
    apply Derives.impI
    exact SyntaxRenameKnownSource.equality_input (ZFContext.add hZ P) w R S r s a b c d n x y X Y (add hw P) (add hr P) (add hs P) (add hc P) (.hyp (Or.inl rfl))
  have hl : Derives Γ ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P)) := by
    apply Derives.impI
    let I := SyntaxRenameOutputSyntax.input w R S a b c d n
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    have h1 := SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 3 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
    have h2 := SyntaxRenameRawFields.equality_iff (ZFContext.add hZ I) w r s a b c d n q x y X Y (add hw I) (add hc I) (add hd I)
    exact SyntaxTypeLocalTransfer.iff_trans h1 h2
  exact remove_input hZ w R S a b c d n q P hw hi hl

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S r s a b c d n q z Z x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (memberOperands w r s a b c d z Z x y X Y)) := by
  let P := memberOperands w r s a b c d z Z x y X Y
  have hi : Derives Γ (P.imp (SyntaxRenameOutputSyntax.input w R S a b c d n)) := by
    apply Derives.impI
    exact SyntaxRenameKnownSource.membership_input (ZFContext.add hZ P) w R S r s a b c d n z Z x y X Y (add hw P) (add hr P) (add hs P) (add hc P) (.hyp (Or.inl rfl))
  have hl : Derives Γ ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P)) := by
    apply Derives.impI
    let I := SyntaxRenameOutputSyntax.input w R S a b c d n
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    have h1 := SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 2 3 w R S r s a b c d n q (SyntaxAtomSyntax.three z x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
    have h2 := SyntaxRenameRawFields.membership_iff (ZFContext.add hZ I) w r s a b c d n q z Z x y X Y (add hw I) (add hc I) (add hd I)
    exact SyntaxTypeLocalTransfer.iff_trans h1 h2
  exact remove_input hZ w R S a b c d n q P hw hi hl

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S r s a b c d n q x X : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode tag w X q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X)) := by
  let P := SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X
  have hi : Derives Γ (P.imp (SyntaxRenameOutputSyntax.input w R S a b c d n)) := by
    apply Derives.impI
    exact SyntaxRenameKnownSource.single_input (ZFContext.add hZ P) tag advance valid w R S r s a b c d n x X (add hw P) (add hr P) (add hs P) (add hc P) (.hyp (Or.inl rfl))
  have hl : Derives Γ ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P)) := by
    apply Derives.impI
    let I := SyntaxRenameOutputSyntax.input w R S a b c d n
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    have h1 : Derives (Context.add I Γ) ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q)) := by
      rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 4 1 w R S r s a b c d n q (fun _ => x) (add hw I) hI (add hr I) (add hs I) (add hc I)
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 9 1 w R S r s a b c d n q (fun _ => x) (add hw I) hI (add hr I) (add hs I) (add hc I)
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 10 1 w R S r s a b c d n q (fun _ => x) (add hw I) hI (add hr I) (add hs I) (add hc I)
    have h2 := SyntaxRenameRawFields.single_iff (ZFContext.add hZ I) tag advance w R S a b c d n q x X (add hw I) (add hc I) (add hd I)
    exact SyntaxTypeLocalTransfer.iff_trans h1 h2
  exact remove_input hZ w R S a b c d n q P hw hi hl

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S r s a b c d n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y))) := by
  let P := (SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)
  have hi : Derives Γ (P.imp (SyntaxRenameOutputSyntax.input w R S a b c d n)) := by
    apply Derives.impI
    exact SyntaxRenameKnownSource.binary_input (ZFContext.add hZ P) kind w R S r s a b c d n x y X Y (add hw P) (add hr P) (add hs P) (add hc P) (.hyp (Or.inl rfl))
  have hl : Derives Γ ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff P)) := by
    apply Derives.impI
    let I := SyntaxRenameOutputSyntax.input w R S a b c d n
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    have h1 : Derives (Context.add I Γ) ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q)) := by
      have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
      rcases hk with rfl | rfl | rfl | rfl
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 5 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 6 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 7 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
      · exact SyntaxRenameSelectedIff.source_case (ZFContext.add hZ I) 8 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) (add hw I) hI (add hr I) (add hs I) (add hc I)
    have h2 := SyntaxRenameRawFields.binary_iff (ZFContext.add hZ I) kind w R S a b c d n q x y X Y (add hw I) (add hc I) (add hd I)
    exact SyntaxTypeLocalTransfer.iff_trans h1 h2
  exact remove_input hZ w R S a b c d n q P hw hi hl

theorem nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w R S r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R))
    (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (.equal n q)) := by
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w a b n hw hc)) (SyntaxRenameKnownSource.source_contexts w R S r s a b c d hr hs)
  have hi := SyntaxRenameKnownSource.input_of_code w R S r s a b c d n hr hs ht
  apply Derives.conjI
  · apply Derives.impI
    exact eq_symm (SyntaxRenameNullary.unique (ZFContext.add hZ _) truth w R S a b c d n q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let E := Formula.equal n q
    have hn := SyntaxRenameNullary.intro_self (ZFContext.add hZ E) truth w R S a b c d n (add hw E) (add hi E) (add hc E)
    exact SyntaxRenameJudgmentSubst.subst_q w R S a b c d n n q (.hyp (Or.inl rfl)) hn

end PPAC.Migration.Internal.SyntaxRenameKnownFields
