import PPAC.Migration.Internal.ObjectBoundedLookupDispatch

/-! 原lookup行的全部内部字段、实际码值与等词传输。 -/
namespace PPAC.Migration.Internal.HornLookupRowSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def row {m} (w n i y r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields n i y) r

def existsRow {m} (w n i y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (row w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m)))

theorem row_rename {m k} (w n i y r : Fin m) (ρ : Fin m → Fin k) :
    (row w n i y r).rename ρ = row (ρ w) (ρ n) (ρ i) (ρ y) (ρ r) := by
  simp only [row, SyntaxNodeSyntax.constructor_rename, OriginalLookupRuleMatrix.rowFields_map]

theorem existsRow_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (existsRow w n i y).rename ρ = existsRow (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [existsRow, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fields_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y a b c r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) (hs : Derives Γ (row w a b c r)) :
    Derives Γ ((Formula.equal n a).conj ((Formula.equal i b).conj (.equal y c))) := by
  have hf (j : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ 3 0 0 w (OriginalLookupExpr.rowFields n i y) (OriginalLookupExpr.rowFields a b c) r j hw hr hs
  exact .conjI (hf 0) (.conjI (hf 1) (hf 2))

theorem code_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) : Derives Γ (.mem r w) :=
  SyntaxNodeInjective.constructor_range hZ 3 0 w _ r hw hr

theorem naturals {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) :
    Derives Γ ((Formula.mem n w).conj ((Formula.mem i w).conj (.mem y w))) := by
  have hR := code_natural hZ w n i y r hw hr
  have hm (j : Fin 3) := StructuralListTraceOrder.member_member hZ w (OriginalLookupExpr.rowFields n i y j) r hw hR
    (SyntaxConstructors.child_member hZ 3 0 w (OriginalLookupExpr.rowFields n i y) r j hw hr)
  exact .conjI (hm 0) (.conjI (hm 1) (hm 2))

theorem exists_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) (hy : Derives Γ (.mem y w)) :
    Derives Γ (existsRow w n i y) := by
  have hs : ∀ j : Fin 3, Derives Γ (.mem (OriginalLookupExpr.rowFields n i y j) w) :=
    fun j => Fin.cases hn (fun k => Fin.cases hi (fun _ => hy) k) j
  exact SyntaxConstructors.exists_constructor hZ 3 0 w _ hw (SyntaxForestSyntax.intro_inputs 3 w _ hs)

theorem value_subst {m} {Γ : Context m} (w n i y r z : Fin m)
    (he : Derives Γ (.equal y z)) (hr : Derives Γ (row w n i y r)) : Derives Γ (row w n i z r) := by
  let P := row w.castSucc n.castSucc i.castSucc (Fin.last m) r.castSucc
  have h0 : P.instantiate y = row w n i y r := by simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = row w n i z r := by simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem code_subst {m} {Γ : Context m} (w n i y r s : Fin m)
    (he : Derives Γ (.equal r s)) (hr : Derives Γ (row w n i y r)) : Derives Γ (row w n i y s) := by
  let P := row w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m)
  have h0 : P.instantiate r = row w n i y r := by simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate s = row w n i y s := by simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem execution_value_subst {m} {Γ : Context m} (w n i y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i z) := by
  let P := LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc (Fin.last m)
  have h0 : P.instantiate y = LookupTableExecutionSyntax.executed w n i y := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = LookupTableExecutionSyntax.executed w n i z := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

theorem successor_output_subst {m} {Γ : Context m} (i s j : Fin m)
    (he : Derives Γ (.equal i s)) (hs : Derives Γ (successor s j)) : Derives Γ (successor i j) := by
  let P := successor (Fin.last m) j.castSucc
  have h0 : P.instantiate s = successor s j := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate i = successor i j := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P (eq_symm he) (of_eq h0.symm hs))

end PPAC.Migration.Internal.HornLookupRowSyntax
