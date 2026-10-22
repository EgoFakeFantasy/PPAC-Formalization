import PPAC.Migration.Internal.SyntaxRenameKnownFieldsSyntax

/-! 所有内部候选的原分支精确字段双条件；两端字段由原同码单射恢复，使用原存在和等词规则。 -/
namespace PPAC.Migration.Internal.SyntaxRenameRawFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameBinders SyntaxRenameKnownFieldsSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (w r s a b c d n q x y X Y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).iff (equalOperands w r s a b c d x y X Y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := SyntaxRenameAtomSyntax.equality w r s a b c d n q
    let B := SyntaxRenameAtomSyntax.equalityBody w r s a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))))
    apply eliminate_4 B _ (.hyp (Or.inl rfl))
    have hZk := zf_under_4 (ZFContext.add hZ T) B
    have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 (add hw T) B)
    have hck : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (under_4 (add hc T) B)
    have hdk : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (under_4 (add hd T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxAtomUnique.equal_fields hZk w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc hwk (.conjL hB) hck
    have et := SyntaxAtomUnique.equal_fields hZk w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR hB)) hdk
    have hx0 := SyntaxRenameAtomicSubst.term_source w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc x.castSucc.castSucc.castSucc.castSucc (.conjL es) (.conjL (.conjR (.conjR hB)))
    have hy0 := SyntaxRenameAtomicSubst.term_source w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) y.castSucc.castSucc.castSucc.castSucc (.conjR es) (.conjR (.conjR (.conjR hB)))
    have hx := SyntaxRenameEndpointSubst.term_target w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc X.castSucc.castSucc.castSucc.castSucc (.conjL et) hx0
    have hy := SyntaxRenameEndpointSubst.term_target w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) Y.castSucc.castSucc.castSucc.castSucc (.conjR et) hy0
    have ho : Derives Δ (equalOperands w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc) := .conjI hx hy
    exact of_eq (by simp only [Formula.raise, equalOperands_rename]) ho
  · apply Derives.impI
    let P := equalOperands w r s a b c d x y X Y
    have hp : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    exact SyntaxRenameAtomSyntax.intro_equality w r s a b c d n q x y X Y (.conjI (add hc P) (.conjI (add hd P) hp))

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (w r s a b c d n q z Z x y X Y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).iff (memberOperands w r s a b c d z Z x y X Y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := SyntaxRenameAtomSyntax.membership w r s a b c d n q
    let B := SyntaxRenameAtomSyntax.membershipBody w r s a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ))))))
    apply eliminate_5 B _ (.hyp (Or.inl rfl))
    have hZk := zf_under_5 (ZFContext.add hZ T) B
    have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_5 (add hw T) B)
    have hck : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (under_5 (add hc T) B)
    have hdk : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc Z.castSucc.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (under_5 (add hd T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxAtomUnique.member_fields hZk w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR hB)) hck
    have et := SyntaxAtomUnique.member_fields hZk w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) Z.castSucc.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR (.conjR hB))) hdk
    have hx0 := SyntaxRenameAtomicSubst.term_source w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR es)) (.conjL (.conjR (.conjR (.conjR hB))))
    have hy0 := SyntaxRenameAtomicSubst.term_source w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4)) y.castSucc.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR es)) (.conjR (.conjR (.conjR (.conjR hB))))
    have hx := SyntaxRenameEndpointSubst.term_target w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR et)) hx0
    have hy := SyntaxRenameEndpointSubst.term_target w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) Y.castSucc.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR et)) hy0
    have hz := SyntaxAtomLogic.zeroScalar_output_subst w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc (.conjL es) (.conjL hB)
    have ez := eq_trans (eq_symm (Derives.conjL es)) (Derives.conjL et)
    have ho : Derives Δ (memberOperands w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc Z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc) := .conjI hz (.conjI ez (.conjI hx hy))
    exact of_eq (by simp only [Formula.raise, memberOperands_rename]) ho
  · apply Derives.impI
    let P := memberOperands w r s a b c d z Z x y X Y
    have hp : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have ht := SyntaxAtomUnique.symbol_subst w Z z X Y q (eq_symm (Derives.conjL (.conjR hp))) (add hd P)
    exact SyntaxRenameAtomSyntax.intro_membership w r s a b c d n q z x y X Y (.conjI (.conjL hp) (.conjI (add hc P) (.conjI ht (.conjR (.conjR hp)))))

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode tag w X q)) :
    Derives Γ ((SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d X)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q
    let B := SyntaxRenameRecursiveSyntax.singleBody tag advance w r s a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))
    apply eliminate_2 B _ (.hyp (Or.inl rfl))
    have hZk := zf_under_2 (ZFContext.add hZ T) B
    have hwk : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 (add hw T) B)
    have hck : Derives Δ (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under_2 (add hc T) B)
    have hdk : Derives Δ (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under_2 (add hd T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxLogicalFields.single_fields hZk tag w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc n.castSucc.castSucc hwk (.conjL hB) hck
    have et := SyntaxLogicalFields.single_fields hZk tag w.castSucc.castSucc (Fin.last (m+1)) X.castSucc.castSucc q.castSucc.castSucc hwk (.conjL (.conjR (.conjR hB))) hdk
    have hs := SyntaxRenameLogicalSubst.check_source advance w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) x.castSucc.castSucc es (.conjR (.conjR (.conjR hB)))
    have ho := SyntaxRenameEndpointSubst.check_target advance w.castSucc.castSucc x.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) X.castSucc.castSucc et hs
    exact of_eq (by simp only [Formula.raise, SyntaxRenameRecursiveSyntax.check_rename]) ho
  · apply Derives.impI
    let P := SyntaxRenameRecursiveSyntax.check advance w x r s a b c d X
    have hp : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have hb := SyntaxLogicalFields.single_bound (ZFContext.add hZ P) tag w x n (add hw P) (add hc P)
    exact SyntaxRenameRecursiveSyntax.intro_single tag advance w r s a b c d n q x X (.conjI (add hc P) (.conjI hb (.conjI (add hd P) hp)))

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w r s a b c d y Y))) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q
    let B := SyntaxRenameRecursiveSyntax.binaryBody kind w r s a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))))
    apply eliminate_4 B _ (.hyp (Or.inl rfl))
    have hZk := zf_under_4 (ZFContext.add hZ T) B
    have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 (add hw T) B)
    have hck : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (under_4 (add hc T) B)
    have hdk : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (under_4 (add hd T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxLogicalFields.binary_fields hZk kind w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc hwk (.conjL hB) hck
    have et := SyntaxLogicalFields.binary_fields hZk kind w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR (.conjR (.conjR hB)))) hdk
    have hx0 := SyntaxRenameJudgmentSubst.subst_n w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc x.castSucc.castSucc.castSucc.castSucc (.conjL es) (.conjL (.conjR (.conjR (.conjR (.conjR hB)))))
    have hy0 := SyntaxRenameJudgmentSubst.subst_n w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) y.castSucc.castSucc.castSucc.castSucc (.conjR es) (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
    have hx := SyntaxRenameJudgmentSubst.subst_q w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc X.castSucc.castSucc.castSucc.castSucc (.conjL et) hx0
    have hy := SyntaxRenameJudgmentSubst.subst_q w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) Y.castSucc.castSucc.castSucc.castSucc (.conjR et) hy0
    have ho := Derives.conjI hx hy
    exact of_eq (by simp only [Formula.raise, Formula.rename, SyntaxRenameJudgmentSyntax.renamed_rename]) ho
  · apply Derives.impI
    let P := (SyntaxRenameJudgmentSyntax.renamed w r s a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w r s a b c d y Y)
    have hp : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have hb := SyntaxLogicalFields.binary_bounds (ZFContext.add hZ P) kind w x y n (add hw P) (add hc P)
    exact SyntaxRenameRecursiveSyntax.intro_binary kind w r s a b c d n q x y X Y (.conjI (add hc P) (.conjI (.conjL hb) (.conjI (.conjR hb) (.conjI (add hd P) hp))))

end PPAC.Migration.Internal.SyntaxRenameRawFields
