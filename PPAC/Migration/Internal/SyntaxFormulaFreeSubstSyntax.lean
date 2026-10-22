import PPAC.Migration.Internal.SyntaxFreeSubstFields

/-! 保留原替换项列表的全内部公式free替换；实际恒等码和列表转换码均在对象量词内绑定。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeSubstSyntax (codeConversion codeConversion_rename termList termList_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)

def body {m} (w b a c L n q : Fin m) : Formula (m+2) :=
  (identityCode w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
    ((codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))).conj
      (renamed w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
        b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc
        n.castSucc.castSucc q.castSucc.castSucc))

def substituted {m} (w b a c L n q : Fin m) : Formula m := .ex (.ex (body w b a c L n q))

def input {m} (w b a c L n : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n b a).conj (termList w a c L)

def existsOutput {m} (w b a c L n : Fin m) : Formula m := .ex
  (substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m))

def uniqueOutput {m} (w b a c L n q : Fin m) : Formula m := .all
  ((substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) q.castSucc))

def fiber {m} (w b a c L n : Fin m) : Formula m := .ex
  ((substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)))

theorem substituted_rename {m k} (w b a c L n q : Fin m) (ρ : Fin m → Fin k) :
    (substituted w b a c L n q).rename ρ = substituted (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) := by
  simp only [substituted, body, Formula.rename, identityCode_rename, codeConversion_rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_rename {m k} (w b a c L n : Fin m) (ρ : Fin m → Fin k) :
    (input w b a c L n).rename ρ = input (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) := by
  simp only [input, Formula.rename, FormulaCodeSyntax.formulaCode_rename, termList_rename]

theorem existsOutput_rename {m k} (w b a c L n : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w b a c L n).rename ρ = existsOutput (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) := by
  simp only [existsOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w b a c L n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w b a c L n q).rename ρ = uniqueOutput (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w b a c L n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w b a c L n).rename ρ = fiber (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) := by
  simp only [fiber, Formula.rename, substituted_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_substituted {m} {Γ : Context m} (w b a c L n q R S : Fin m)
    (hr : Derives Γ (identityCode w b R)) (hs : Derives Γ (codeConversion w a c L S))
    (hq : Derives Γ (renamed w R S b a b c n q)) : Derives Γ (substituted w b a c L n q) := by
  apply Derives.exI R
  apply Derives.exI S
  simp only [body, Formula.instantiate, Formula.rename, identityCode_rename, codeConversion_rename, renamed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr (.conjI hs hq)

theorem eliminate_substituted {m} {Γ : Context m} (w b a c L n q : Fin m) (P : Formula m)
    (hw : Derives Γ (substituted w b a c L n q))
    (hc : Derives (Context.add (body w b a c L n q) (Context.image Formula.raise (Context.image Formula.raise Γ)))
      P.raise.raise) : Derives Γ P := by
  apply Derives.exE hw
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨v, hv, he⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨v, Or.inr hv, he⟩

theorem intro_exists {m} {Γ : Context m} (w b a c L n q : Fin m)
    (hq : Derives Γ (substituted w b a c L n q)) : Derives Γ (existsOutput w b a c L n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, substituted_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem intro_fiber {m} {Γ : Context m} (w b a c L n q : Fin m)
    (hq : Derives Γ (substituted w b a c L n q)) (hu : Derives Γ (uniqueOutput w b a c L n q)) :
    Derives Γ (fiber w b a c L n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, substituted_rename, uniqueOutput_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hu)

theorem unique_at {m} {Γ : Context m} (w b a c L n q v : Fin m)
    (hu : Derives Γ (uniqueOutput w b a c L n q)) :
    Derives Γ ((substituted w b a c L n v).imp (.equal v q)) :=
  of_eq (by simp only [Formula.instantiate, Formula.rename, substituted_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE v hu)

theorem subst_q {m} {Γ : Context m} (w b a c L n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hq : Derives Γ (substituted w b a c L n q)) :
    Derives Γ (substituted w b a c L n v) := by
  let P := substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  have e0 : P.instantiate q = substituted w b a c L n q := by
    simp only [P, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate v = substituted w b a c L n v := by
    simp only [P, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hq))

end PPAC.Migration.Internal.SyntaxFormulaFreeSubstSyntax
