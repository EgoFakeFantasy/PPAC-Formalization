import PPAC.Migration.Internal.SyntaxRenameLogicalSyntax

/-! 全11类实际重命名分支；两个内部映射码实际解码出完整图后供原子项分支使用。 -/
namespace PPAC.Migration.Internal.SyntaxRenameLocalSyntax
open Source SourceAlgebra SourceLogic SyntaxMapCodeSyntax SyntaxRenameQuerySyntax

def cases {m} (w R S r s a b c d h n q : Fin m) : Formula m :=
  ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).disj (SyntaxRenameAtomSyntax.nullary true w a b c d n q)).disj
    ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).disj
      ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).disj
        ((SyntaxRenameLogicalSyntax.single 4 false w h R S a b c d n q).disj
          ((SyntaxRenameLogicalSyntax.binary 0 w h R S a b c d n q).disj
            ((SyntaxRenameLogicalSyntax.binary 1 w h R S a b c d n q).disj
              ((SyntaxRenameLogicalSyntax.binary 2 w h R S a b c d n q).disj
                ((SyntaxRenameLogicalSyntax.binary 3 w h R S a b c d n q).disj
                  ((SyntaxRenameLogicalSyntax.single 9 true w h R S a b c d n q).disj
                    (SyntaxRenameLogicalSyntax.single 10 true w h R S a b c d n q)))))))))

theorem cases_rename {m k} (w R S r s a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (cases w R S r s a b c d h n q).rename ρ = cases (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  simp only [cases, Formula.rename, SyntaxRenameAtomSyntax.nullary_rename, SyntaxRenameAtomSyntax.membership_rename, SyntaxRenameAtomSyntax.equality_rename, SyntaxRenameLogicalSyntax.single_rename, SyntaxRenameLogicalSyntax.binary_rename]

def localRenameData {m} (w R S a b c d h n q r s : Fin m) : Formula m :=
  (encoded w r a c R).conj ((encoded w s b d S).conj (cases w R S r s a b c d h n q))

def localRenameBody {m} (w R S a b c d h n q : Fin m) : Formula (m+2) :=
  localRenameData w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def localRename {m} (w R S a b c d h n q : Fin m) : Formula m := .ex (.ex (localRenameBody w R S a b c d h n q))

theorem localRenameData_rename {m k} (w R S a b c d h n q r s : Fin m) (ρ : Fin m → Fin k) :
    (localRenameData w R S a b c d h n q r s).rename ρ = localRenameData (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) (ρ r) (ρ s) := by
  simp only [localRenameData, Formula.rename, encoded_rename, cases_rename]

theorem localRename_rename {m k} (w R S a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (localRename w R S a b c d h n q).rename ρ = localRename (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  simp only [localRename, localRenameBody, Formula.rename, localRenameData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_localRename {m} {Γ : Context m} (w R S a b c d h n q r s : Fin m)
    (hd : Derives Γ (localRenameData w R S a b c d h n q r s)) : Derives Γ (localRename w R S a b c d h n q) := by
  apply Derives.exI r
  apply Derives.exI s
  simpa only [localRenameBody, Formula.instantiate, Formula.rename, localRenameData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def content {m} (w R S a b c d h n q : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj (localRename w R S a b c d h n q)

theorem content_rename {m k} (w R S a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (content w R S a b c d h n q).rename ρ = content (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  simp only [content, Formula.rename, FormulaCodeSyntax.formulaCode_rename, localRename_rename]

theorem subst_R {m} {Γ : Context m} (w R S a b c d h n q R1 : Fin m)
    (he : Derives Γ (.equal R R1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R1 S a b c d h n q) := by
  let P := content w.castSucc (Fin.last m) S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate R = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate R1 = content w R1 S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_S {m} {Γ : Context m} (w R S a b c d h n q S1 : Fin m)
    (he : Derives Γ (.equal S S1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S1 a b c d h n q) := by
  let P := content w.castSucc R.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate S = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate S1 = content w R S1 a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_a {m} {Γ : Context m} (w R S a b c d h n q a1 : Fin m)
    (he : Derives Γ (.equal a a1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S a1 b c d h n q) := by
  let P := content w.castSucc R.castSucc S.castSucc (Fin.last m) b.castSucc c.castSucc d.castSucc h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate a = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate a1 = content w R S a1 b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_b {m} {Γ : Context m} (w R S a b c d h n q b1 : Fin m)
    (he : Derives Γ (.equal b b1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S a b1 c d h n q) := by
  let P := content w.castSucc R.castSucc S.castSucc a.castSucc (Fin.last m) c.castSucc d.castSucc h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate b = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate b1 = content w R S a b1 c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_c {m} {Γ : Context m} (w R S a b c d h n q c1 : Fin m)
    (he : Derives Γ (.equal c c1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S a b c1 d h n q) := by
  let P := content w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc (Fin.last m) d.castSucc h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate c = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate c1 = content w R S a b c1 d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_d {m} {Γ : Context m} (w R S a b c d h n q d1 : Fin m)
    (he : Derives Γ (.equal d d1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S a b c d1 h n q) := by
  let P := content w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc (Fin.last m) h.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate d = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate d1 = content w R S a b c d1 h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_q {m} {Γ : Context m} (w R S a b c d h n q q1 : Fin m)
    (he : Derives Γ (.equal q q1)) (hc : Derives Γ (content w R S a b c d h n q)) :
    Derives Γ (content w R S a b c d h n q1) := by
  let P := content w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc h.castSucc n.castSucc (Fin.last m)
  have e0 : P.instantiate q = content w R S a b c d h n q := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate q1 = content w R S a b c d h n q1 := by
    simp only [P, Formula.instantiate, content_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem content_subst {m} {Γ : Context m} (w R S a b c d h n q R1 S1 a1 b1 c1 d1 q1 : Fin m)
    (he : Derives Γ (SyntaxRenameStateSyntax.equalParams R S a b c d q R1 S1 a1 b1 c1 d1 q1))
    (hc : Derives Γ (content w R S a b c d h n q)) : Derives Γ (content w R1 S1 a1 b1 c1 d1 h n q1) := by
  have h0 := subst_R w R S a b c d h n q R1 (.conjL he) hc
  have h1 := subst_S w R1 S a b c d h n q S1 (.conjL (.conjR he)) h0
  have h2 := subst_a w R1 S1 a b c d h n q a1 (.conjL (.conjR (.conjR he))) h1
  have h3 := subst_b w R1 S1 a1 b c d h n q b1 (.conjL (.conjR (.conjR (.conjR he)))) h2
  have h4 := subst_c w R1 S1 a1 b1 c d h n q c1 (.conjL (.conjR (.conjR (.conjR (.conjR he))))) h3
  have h5 := subst_d w R1 S1 a1 b1 c1 d h n q d1 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR he)))))) h4
  have h6 := subst_q w R1 S1 a1 b1 c1 d1 h n q q1 (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR he)))))) h5
  exact h6

theorem case_nullary {m} {Γ : Context m} (truth : Bool) (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameAtomSyntax.nullary truth w a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  cases truth
  · exact .disjL (.disjL hc)
  · exact .disjL (.disjR hc)

theorem case_membership {m} {Γ : Context m} (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameAtomSyntax.membership w r s a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  exact (.disjR (.disjL hc))

theorem case_equality {m} {Γ : Context m} (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameAtomSyntax.equality w r s a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  exact (.disjR (.disjR (.disjL hc)))

theorem case_negation {m} {Γ : Context m} (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameLogicalSyntax.single 4 false w h R S a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  exact (.disjR (.disjR (.disjR (.disjL hc))))

theorem case_binary {m} {Γ : Context m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameLogicalSyntax.binary kind w h R S a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc))))))))

theorem case_quantified {m} {Γ : Context m} (universal : Bool) (w R S r s a b c d h n q : Fin m)
    (hc : Derives Γ (SyntaxRenameLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c d n q)) : Derives Γ (cases w R S r s a b c d h n q) := by
  cases universal
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR hc)))))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))))

end PPAC.Migration.Internal.SyntaxRenameLocalSyntax
