import PPAC.Migration.Internal.ObjectSyntaxRenameOutput

/-! 固定纯公式中实际项源码、原子字段和解码图参数的对象等词替换。 -/
namespace PPAC.Migration.Internal.SyntaxRenameAtomicSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

theorem term_source {m} {Γ : Context m} (w r s a b c d n q z1 : Fin m)
    (he : Derives Γ (.equal n z1)) (hp : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) :
    Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d z1 q) := by
  let P := SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) q.castSucc
  have e0 : P.instantiate n = SyntaxRenameTermSyntax.renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxRenameTermSyntax.renamed w r s a b c d z1 q := by
    simp only [P, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem equal_x {m} {Γ : Context m} (w x y n z1 : Fin m)
    (he : Derives Γ (.equal x z1)) (hp : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) :
    Derives Γ (SyntaxAtomSyntax.equalCode w z1 y n) := by
  let P := SyntaxAtomSyntax.equalCode w.castSucc (Fin.last m) y.castSucc n.castSucc
  have e0 : P.instantiate x = SyntaxAtomSyntax.equalCode w x y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.equalCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxAtomSyntax.equalCode w z1 y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.equalCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem equal_y {m} {Γ : Context m} (w x y n z1 : Fin m)
    (he : Derives Γ (.equal y z1)) (hp : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) :
    Derives Γ (SyntaxAtomSyntax.equalCode w x z1 n) := by
  let P := SyntaxAtomSyntax.equalCode w.castSucc x.castSucc (Fin.last m) n.castSucc
  have e0 : P.instantiate y = SyntaxAtomSyntax.equalCode w x y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.equalCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxAtomSyntax.equalCode w x z1 n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.equalCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem member_x {m} {Γ : Context m} (w z x y n z1 : Fin m)
    (he : Derives Γ (.equal x z1)) (hp : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) :
    Derives Γ (SyntaxAtomSyntax.memberCode w z z1 y n) := by
  let P := SyntaxAtomSyntax.memberCode w.castSucc z.castSucc (Fin.last m) y.castSucc n.castSucc
  have e0 : P.instantiate x = SyntaxAtomSyntax.memberCode w z x y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxAtomSyntax.memberCode w z z1 y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem member_y {m} {Γ : Context m} (w z x y n z1 : Fin m)
    (he : Derives Γ (.equal y z1)) (hp : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) :
    Derives Γ (SyntaxAtomSyntax.memberCode w z x z1 n) := by
  let P := SyntaxAtomSyntax.memberCode w.castSucc z.castSucc x.castSucc (Fin.last m) n.castSucc
  have e0 : P.instantiate y = SyntaxAtomSyntax.memberCode w z x y n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxAtomSyntax.memberCode w z x z1 n := by
    simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem cases_r {m} {Γ : Context m} (w R S r s a b c d n q z1 : Fin m)
    (he : Derives Γ (.equal r z1)) (hp : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S z1 s a b c d n q) := by
  let P := SyntaxRenameRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc (Fin.last m) s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate r = SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.cases_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxRenameRecursiveSyntax.cases w R S z1 s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.cases_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem cases_s {m} {Γ : Context m} (w R S r s a b c d n q z1 : Fin m)
    (he : Derives Γ (.equal s z1)) (hp : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r z1 a b c d n q) := by
  let P := SyntaxRenameRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc r.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate s = SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.cases_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxRenameRecursiveSyntax.cases w R S r z1 a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.cases_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

end PPAC.Migration.Internal.SyntaxRenameAtomicSubst
