import PPAC.Migration.Internal.NativeAxiomCertificateData
import PPAC.Migration.Internal.FixedAxiomPacketUnique

/-! 七固定ZF及目标三句的实际部分测试；完整Separation／Collection仍须后续接入。 -/
namespace PPAC.Migration.Internal.FixedAxiomTableSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NativeAxiomCertificateData (fixedFormula fixedTag)

def kinds (target : Bool) : List (Fin 10) :=
  if target then [0,1,2,3,4,5,6,7,8,9] else [0,1,2,3,4,5,6]

def branch {m} (kind : Fin 10) (w certificate formula : Fin m) : Formula m :=
  (FixedAxiomPacketSyntax.leaf (fixedTag kind) w certificate).conj
    (PureQuotationSyntax.formula (fixedFormula kind) w formula)

def table {m} (target : Bool) (w certificate formula : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin ((kinds target).map (fun kind => branch kind w certificate formula))

def rowTest {m} (target : Bool) (w row : Fin m) : Formula m := .ex (.ex
  ((SyntaxNodeSyntax.constructor 2 0 w.castSucc.castSucc (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1))) row.castSucc.castSucc).conj
    (table target w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def test (target : Bool) : Formula 1 := .ex
  ((omega (Fin.last 1)).conj (rowTest target (Fin.last 1) (0 : Fin 1).castSucc))

theorem branch_rename {m l} (kind : Fin 10) (w certificate formula : Fin m) (ρ : Fin m → Fin l) :
    (branch kind w certificate formula).rename ρ = branch kind (ρ w) (ρ certificate) (ρ formula) := by
  simp only [branch, Formula.rename, FixedAxiomPacketSyntax.leaf_rename, PureQuotationSyntax.formula_rename]

theorem table_rename {m l} (target : Bool) (w certificate formula : Fin m) (ρ : Fin m → Fin l) :
    (table target w certificate formula).rename ρ = table target (ρ w) (ρ certificate) (ρ formula) := by
  unfold table
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  apply congrArg LogicalAllPatterns.disjoin
  apply List.map_congr_left
  intro kind _
  exact branch_rename kind w certificate formula ρ

theorem rowTest_rename {m l} (target : Bool) (w row : Fin m) (ρ : Fin m → Fin l) :
    (rowTest target w row).rename ρ = rowTest target (ρ w) (ρ row) := by
  simp only [rowTest, Formula.rename, SyntaxNodeSyntax.constructor_rename, table_rename,
    ProofTreeEntryFacts.args2_map, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem test_at {m} (target : Bool) (row : Fin m) :
    AxiomTestSyntax.holds (test target) row = .ex
      ((omega (Fin.last m)).conj (rowTest target (Fin.last m) row.castSucc)) := by
  simp only [AxiomTestSyntax.holds, test, Formula.rename, omega_rename, rowTest_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem target_kind_mem (kind : Fin 10) : kind ∈ kinds true := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (0 : Fin 10) ∈ kinds true
    decide
  · change (1 : Fin 10) ∈ kinds true
    decide
  · change (2 : Fin 10) ∈ kinds true
    decide
  · change (3 : Fin 10) ∈ kinds true
    decide
  · change (4 : Fin 10) ∈ kinds true
    decide
  · change (5 : Fin 10) ∈ kinds true
    decide
  · change (6 : Fin 10) ∈ kinds true
    decide
  · change (7 : Fin 10) ∈ kinds true
    decide
  · change (8 : Fin 10) ∈ kinds true
    decide
  · change (9 : Fin 10) ∈ kinds true
    decide

theorem base_kind_mem (kind : Fin 7) : kind.castLE (by decide : 7 ≤ 10) ∈ kinds false := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (0 : Fin 10) ∈ kinds false
    decide
  · change (1 : Fin 10) ∈ kinds false
    decide
  · change (2 : Fin 10) ∈ kinds false
    decide
  · change (3 : Fin 10) ∈ kinds false
    decide
  · change (4 : Fin 10) ∈ kinds false
    decide
  · change (5 : Fin 10) ∈ kinds false
    decide
  · change (6 : Fin 10) ∈ kinds false
    decide

theorem fixed_counts : (kinds false).length = 7 ∧ (kinds true).length = 10 := by decide

end PPAC.Migration.Internal.FixedAxiomTableSyntax
