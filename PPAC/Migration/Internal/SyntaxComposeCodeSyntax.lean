import PPAC.Migration.Internal.SyntaxComposeGraph

/-! 原自然映射码的实际复合：三幅完整图见证与三个明确作用域均保留在对象量词中。 -/
namespace PPAC.Migration.Internal.SyntaxComposeCodeSyntax
open Source SourceAlgebra SourceLogic SyntaxMapCodeSyntax SyntaxComposeSyntax SyntaxRenameQuerySyntax

def body {m} (w a c e R T K : Fin m) : Formula (m+3) :=
  (encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc).conj
    ((encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc).conj
      ((composed w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc (Fin.last (m+2))).conj
        (encoded w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc)))

def coded {m} (w a c e R T K : Fin m) : Formula m := .ex (.ex (.ex (body w a c e R T K)))

def existsCode {m} (w a c e R T : Fin m) : Formula m := .ex
  (coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc (Fin.last m))

def codeFiber {m} (w a c e R T : Fin m) : Formula m := .ex
  ((coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc (Fin.last m)).conj
    (.all ((coded w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def outputAt {m} (w r t a c e K : Fin m) : Formula m := .ex
  ((composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)).conj
    (encoded w.castSucc (Fin.last m) a.castSucc e.castSucc K.castSucc))

theorem coded_rename {m k} (w a c e R T K : Fin m) (ρ : Fin m → Fin k) :
    (coded w a c e R T K).rename ρ = coded (ρ w) (ρ a) (ρ c) (ρ e) (ρ R) (ρ T) (ρ K) := by
  simp only [coded, body, Formula.rename, encoded_rename, composed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m k} (w a c e R T : Fin m) (ρ : Fin m → Fin k) :
    (existsCode w a c e R T).rename ρ = existsCode (ρ w) (ρ a) (ρ c) (ρ e) (ρ R) (ρ T) := by
  simp only [existsCode, Formula.rename, coded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeFiber_rename {m k} (w a c e R T : Fin m) (ρ : Fin m → Fin k) :
    (codeFiber w a c e R T).rename ρ = codeFiber (ρ w) (ρ a) (ρ c) (ρ e) (ρ R) (ρ T) := by
  simp only [codeFiber, Formula.rename, coded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem outputAt_rename {m k} (w r t a c e K : Fin m) (ρ : Fin m → Fin k) :
    (outputAt w r t a c e K).rename ρ = outputAt (ρ w) (ρ r) (ρ t) (ρ a) (ρ c) (ρ e) (ρ K) := by
  simp only [outputAt, Formula.rename, composed_rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w a c e R T K r t g : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T))
    (hg : Derives Γ (composed w r t a c e g)) (hk : Derives Γ (encoded w g a e K)) : Derives Γ (coded w a c e R T K) := by
  apply Derives.exI r
  apply Derives.exI t
  apply Derives.exI g
  simp only [body, Formula.instantiate, Formula.rename, encoded_rename, composed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr (.conjI ht (.conjI hg hk))

theorem eliminate_code {m} {Γ : Context m} (w a c e R T K : Fin m) (Q : Formula m)
    (he : Derives Γ (coded w a c e R T K))
    (hc : Derives (Context.add (body w a c e R T K) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) Q.raise.raise.raise) : Derives Γ Q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

theorem subst_first {m} {Γ : Context m} (w r t a c e g z : Fin m)
    (he : Derives Γ (.equal r z)) (hg : Derives Γ (composed w r t a c e g)) : Derives Γ (composed w z t a c e g) := by
  let P := composed w.castSucc (Fin.last m) t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc
  have e0 : P.instantiate r = composed w r t a c e g := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z = composed w z t a c e g := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hg))

theorem subst_second {m} {Γ : Context m} (w r t a c e g z : Fin m)
    (he : Derives Γ (.equal t z)) (hg : Derives Γ (composed w r t a c e g)) : Derives Γ (composed w r z a c e g) := by
  let P := composed w.castSucc r.castSucc (Fin.last m) a.castSucc c.castSucc e.castSucc g.castSucc
  have e0 : P.instantiate t = composed w r t a c e g := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z = composed w r z a c e g := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hg))

theorem subst_output {m} {Γ : Context m} (w r t a c e g z : Fin m)
    (he : Derives Γ (.equal g z)) (hg : Derives Γ (composed w r t a c e g)) : Derives Γ (composed w r t a c e z) := by
  let P := composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)
  have e0 : P.instantiate g = composed w r t a c e g := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z = composed w r t a c e z := by simp only [P, Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hg))
end PPAC.Migration.Internal.SyntaxComposeCodeSyntax
