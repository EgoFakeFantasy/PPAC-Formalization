import PPAC.Migration.Internal.SyntaxFreeShiftFiber

/-! 全内部 free 头槽弱化的纯对象公式；实际恒等码和位移码在对象量词内绑定。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeShiftSyntax (shiftCode shiftCode_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)

def body {m} (w a b B n q : Fin m) : Formula (m+2) :=
  (identityCode w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc).conj
    ((shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))).conj
      (renamed w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
        a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc
        n.castSucc.castSucc q.castSucc.castSucc))

def weakened {m} (w a b B n q : Fin m) : Formula m := .ex (.ex (body w a b B n q))

def input {m} (w a b B n : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj (successor B b)

def existsOutput {m} (w a b B n : Fin m) : Formula m := .ex
  (weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m))

def uniqueOutput {m} (w a b B n q : Fin m) : Formula m := .all
  ((weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) q.castSucc))

def fiber {m} (w a b B n : Fin m) : Formula m := .ex
  ((weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)))

def actualState {m} (w a b n : Fin m) : Formula m := .ex
  ((successor (Fin.last m) b.castSucc).conj
    (fiber w.castSucc a.castSucc b.castSucc (Fin.last m) n.castSucc))

theorem weakened_rename {m k} (w a b B n q : Fin m) (ρ : Fin m → Fin k) :
    (weakened w a b B n q).rename ρ = weakened (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) := by
  simp only [weakened, body, Formula.rename, identityCode_rename, shiftCode_rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_rename {m k} (w a b B n : Fin m) (ρ : Fin m → Fin k) :
    (input w a b B n).rename ρ = input (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) := by
  simp only [input, Formula.rename, FormulaCodeSyntax.formulaCode_rename, successor_rename]

theorem existsOutput_rename {m k} (w a b B n : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w a b B n).rename ρ = existsOutput (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) := by
  simp only [existsOutput, Formula.rename, weakened_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w a b B n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w a b B n q).rename ρ = uniqueOutput (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, weakened_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w a b B n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w a b B n).rename ρ = fiber (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) := by
  simp only [fiber, Formula.rename, weakened_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actualState_rename {m k} (w a b n : Fin m) (ρ : Fin m → Fin k) :
    (actualState w a b n).rename ρ = actualState (ρ w) (ρ a) (ρ b) (ρ n) := by
  simp only [actualState, Formula.rename, successor_rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_weakened {m} {Γ : Context m} (w a b B n q R S : Fin m)
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (shiftCode w b B S))
    (hq : Derives Γ (renamed w R S a b a B n q)) : Derives Γ (weakened w a b B n q) := by
  apply Derives.exI R
  apply Derives.exI S
  simp only [body, Formula.instantiate, Formula.rename, identityCode_rename, shiftCode_rename, renamed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr (.conjI hs hq)

theorem eliminate_weakened {m} {Γ : Context m} (w a b B n q : Fin m) (P : Formula m)
    (hw : Derives Γ (weakened w a b B n q))
    (hc : Derives (Context.add (body w a b B n q) (Context.image Formula.raise (Context.image Formula.raise Γ)))
      P.raise.raise) : Derives Γ P := by
  apply Derives.exE hw
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨v, hv, he⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨v, Or.inr hv, he⟩

theorem intro_exists {m} {Γ : Context m} (w a b B n q : Fin m)
    (hq : Derives Γ (weakened w a b B n q)) : Derives Γ (existsOutput w a b B n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, weakened_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem intro_fiber {m} {Γ : Context m} (w a b B n q : Fin m)
    (hq : Derives Γ (weakened w a b B n q)) (hu : Derives Γ (uniqueOutput w a b B n q)) :
    Derives Γ (fiber w a b B n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, weakened_rename, uniqueOutput_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hu)

theorem unique_at {m} {Γ : Context m} (w a b B n q v : Fin m)
    (hu : Derives Γ (uniqueOutput w a b B n q)) :
    Derives Γ ((weakened w a b B n v).imp (.equal v q)) :=
  of_eq (by simp only [Formula.instantiate, Formula.rename, weakened_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE v hu)

theorem subst_q {m} {Γ : Context m} (w a b B n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hq : Derives Γ (weakened w a b B n q)) :
    Derives Γ (weakened w a b B n v) := by
  let P := weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  have e0 : P.instantiate q = weakened w a b B n q := by
    simp only [P, Formula.instantiate, weakened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate v = weakened w a b B n v := by
    simp only [P, Formula.instantiate, weakened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hq))

theorem renamed_subst_s {m} {Γ : Context m} (w r s a b c d n q s1 : Fin m)
    (he : Derives Γ (.equal s s1)) (hr : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s1 a b c d n q) := by
  let P := renamed w.castSucc r.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate s = renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate s1 = renamed w r s1 a b c d n q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))
end PPAC.Migration.Internal.SyntaxWeakenFreeSyntax
