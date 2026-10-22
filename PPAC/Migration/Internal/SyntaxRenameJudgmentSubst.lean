import PPAC.Migration.Internal.SyntaxMapLiftParameters

/-! 固定RenameFormula参数的原对象等词替换；不采用宿主数据选择。 -/
namespace PPAC.Migration.Internal.SyntaxRenameJudgmentSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxRenameJudgmentSyntax

theorem subst_r {m} {Γ : Context m} (w r s a b c d n q r1 : Fin m)
    (he : Derives Γ (.equal r r1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r1 s a b c d n q) := by
  let P := renamed w.castSucc (Fin.last m) s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate r = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate r1 = renamed w r1 s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem subst_a {m} {Γ : Context m} (w r s a b c d n q a1 : Fin m)
    (he : Derives Γ (.equal a a1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s a1 b c d n q) := by
  let P := renamed w.castSucc r.castSucc s.castSucc (Fin.last m) b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate a = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate a1 = renamed w r s a1 b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem subst_c {m} {Γ : Context m} (w r s a b c d n q c1 : Fin m)
    (he : Derives Γ (.equal c c1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s a b c1 d n q) := by
  let P := renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc (Fin.last m) d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate c = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate c1 = renamed w r s a b c1 d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem subst_n {m} {Γ : Context m} (w r s a b c d n q n1 : Fin m)
    (he : Derives Γ (.equal n n1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s a b c d n1 q) := by
  let P := renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) q.castSucc
  have e0 : P.instantiate n = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate n1 = renamed w r s a b c d n1 q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem subst_q {m} {Γ : Context m} (w r s a b c d n q q1 : Fin m)
    (he : Derives Γ (.equal q q1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s a b c d n q1) := by
  let P := renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have e0 : P.instantiate q = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate q1 = renamed w r s a b c d n q1 := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

end PPAC.Migration.Internal.SyntaxRenameJudgmentSubst
