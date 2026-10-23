import PPAC.Migration.Internal.FormulaTransformStepCorrectness

/-! 独立编译公式程序的状态集合算子；原Separation构造实际内部集合值。 -/
namespace PPAC.Migration.Internal.FormulaTransformOperatorSyntax
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax FormulaTransformProgramSyntax SyntaxMixedFormulaQuerySyntax

def rowBody {m} (w n h p : Fin m) : Formula (m+7) :=
  (SyntaxMixedFormulaStateSyntax.state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj
    (step w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)))

def row {m} (w n h p : Fin m) : Formula m := .ex (.ex (.ex (.ex (.ex (.ex (.ex (rowBody w n h p)))))))

def selectionMatrix : Formula (3+1) := row (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)

def value {m} (w n h v : Fin m) : Formula m := MinimalPredicates.separated selectionMatrix (three w n h) w v

def existsValue {m} (w n h : Fin m) : Formula m := .ex (value w.castSucc n.castSucc h.castSucc (Fin.last m))

def uniqueValue {m} (w n h v : Fin m) : Formula m := .all
  ((value w.castSucc n.castSucc h.castSucc (Fin.last m)).imp (.equal (Fin.last m) v.castSucc))

def fiber {m} (w n h : Fin m) : Formula m := .ex
  ((value w.castSucc n.castSucc h.castSucc (Fin.last m)).conj (uniqueValue w.castSucc n.castSucc h.castSucc (Fin.last m)))

theorem row_rename {m k} (w n h p : Fin m) (ρ : Fin m → Fin k) :
    (row w n h p).rename ρ = row (ρ w) (ρ n) (ρ h) (ρ p) := by
  simp only [row, rowBody, Formula.rename, SyntaxMixedFormulaStateSyntax.state_rename, step_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem selection_at {m} (ρ : Fin 3 → Fin m) (p : Fin m) :
    MinimalPredicates.pred selectionMatrix ρ p = row (ρ 0) (ρ 1) (ρ 2) p := by
  simp only [MinimalPredicates.pred, selectionMatrix, row_rename, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem value_rename {m k} (w n h v : Fin m) (ρ : Fin m → Fin k) :
    (value w n h v).rename ρ = value (ρ w) (ρ n) (ρ h) (ρ v) := by
  simp only [value, MinimalPredicates.separated_rename, three_map]

theorem existsValue_rename {m k} (w n h : Fin m) (ρ : Fin m → Fin k) :
    (existsValue w n h).rename ρ = existsValue (ρ w) (ρ n) (ρ h) := by
  simp only [existsValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueValue_rename {m k} (w n h v : Fin m) (ρ : Fin m → Fin k) :
    (uniqueValue w n h v).rename ρ = uniqueValue (ρ w) (ρ n) (ρ h) (ρ v) := by
  simp only [uniqueValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n h : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n h).rename ρ = fiber (ρ w) (ρ n) (ρ h) := by
  simp only [fiber, Formula.rename, value_rename, uniqueValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_at {m} {Γ : Context m} (w n h v p : Fin m) (hv : Derives Γ (value w n h v)) :
    Derives Γ ((Formula.mem p v).iff ((Formula.mem p w).conj (row w n h p))) := by
  have hi := MinimalPredicates.specialize_separated selectionMatrix (three w n h) w v p hv
  exact of_eq (by simp only [MinimalPredicates.satisfying, selection_at]; rfl) hi

theorem intro_row {m} {Γ : Context m} (w n h p R S a b c d q : Fin m)
    (hs : Derives Γ (SyntaxMixedFormulaStateSyntax.state w R S a b c d q p))
    (hc : Derives Γ (step w R S a b c d h n q)) : Derives Γ (row w n h p) := by
  apply Derives.exI R
  apply Derives.exI S
  apply Derives.exI a
  apply Derives.exI b
  apply Derives.exI c
  apply Derives.exI d
  apply Derives.exI q
  simp only [rowBody, Formula.instantiate, Formula.rename, SyntaxMixedFormulaStateSyntax.state_rename, step_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hc

theorem eliminate_row {m} {Γ : Context m} (w n h p : Fin m) (P : Formula m) (hr : Derives Γ (row w n h p))
    (hc : Derives (Context.add (rowBody w n h p)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise
        (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))))))
      P.raise.raise.raise.raise.raise.raise.raise) : Derives Γ P :=
  SyntaxRenameStateSyntax.eliminate_seven (rowBody w n h p) P hr hc
end PPAC.Migration.Internal.FormulaTransformOperatorSyntax
