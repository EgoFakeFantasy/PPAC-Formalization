import PPAC.Migration.Internal.FixedAxiomTableFacts

/-! All actual fixed-test witnesses are introduced and eliminated inside the object derivation. -/
namespace PPAC.Migration.Internal.FixedAxiomTableExistence
open Source SourceAlgebra SourceLogic OmegaSyntax FixedAxiomTableSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NativeAxiomCertificateData (fixedFormula fixedTag)
attribute [local irreducible] FixedAxiomPacketSyntax.leaf PureQuotationSyntax.formula

def existsTest {m} (target : Bool) (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (AxiomTestSyntax.holds (test target) (Fin.last m)))

theorem existsTest_rename {m l} (target : Bool) (w : Fin m) (ρ : Fin m → Fin l) :
    (existsTest target w).rename ρ = existsTest target (ρ w) := by
  simp only [existsTest, Formula.rename, AxiomTestSyntax.holds_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exists_accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (kind : Fin 10)
    (hk : kind ∈ kinds target) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (existsTest target w) := by
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (FixedAxiomPacketSyntax.leaf (fixedTag kind) w.castSucc (Fin.last m))
  let Γ1 := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (FixedAxiomPacketExistence.exists_packet hZ (fixedTag kind) w hw)
  have hC : Derives Γ1 C := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ C
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula (fixedFormula kind) w.castSucc.castSucc (Fin.last (m+1)))
  let Γ2 := Context.add F (Context.image Formula.raise Γ1)
  have hfe : OriginalTreeQuotationSyntax.treeExists (PureSyntaxQuotation.formulaTree (fixedFormula kind)) w.castSucc = .ex F := by
    unfold OriginalTreeQuotationSyntax.treeExists F PureQuotationSyntax.formula
    rfl
  apply Derives.exE (p := F) (of_eq hfe (OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree (fixedFormula kind)) w.castSucc hw1))
  have hF : Derives Γ2 F := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 F
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 F)
  have hC2 : Derives Γ2 ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (FixedAxiomPacketSyntax.leaf (fixedTag kind) w.castSucc.castSucc (Fin.last m).castSucc)) :=
    of_eq (by simp only [C, Formula.raise, Formula.rename, FixedAxiomPacketSyntax.leaf_rename]) (under hC F)
  have ht := FixedAxiomTableFacts.intro_table target kind hk w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hC2) (.conjR hF)
  let xs := SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1))
  have hi : Derives Γ2 (SyntaxForestSyntax.inputs 2 w.castSucc.castSucc xs) := .conjI (.conjL hC2) (.conjI (.conjL hF) (.eqRefl _))
  let R := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 0 w.castSucc.castSucc.castSucc (fun i => (xs i).castSucc) (Fin.last (m+2)))
  let Γ3 := Context.add R (Context.image Formula.raise Γ2)
  apply Derives.exE (p := R) (SyntaxConstructors.exists_constructor hZ2 2 0 w.castSucc.castSucc xs hw2 hi)
  have hR : Derives Γ3 R := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 R
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 R)
  have ht3 := of_eq (table_rename target w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) Fin.castSucc) (under ht R)
  have hr3 : Derives Γ3 (SyntaxNodeSyntax.constructor 2 0 w.castSucc.castSucc.castSucc
      (SetLanguage.args2 (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) (Fin.last (m+2))) :=
    of_eq (by rw [ProofTreeEntryFacts.args2_map]) (.conjR hR)
  have hb := FixedAxiomTableFacts.intro_row target w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hr3 ht3
  have ha := Derives.impE (.conjR (FixedAxiomTableFacts.test_iff_row hZ3 target w.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3)) hb
  have ho : Derives Γ3 (existsTest target w.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, AxiomTestSyntax.holds_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hR) ha)
  exact of_eq (by simp only [Formula.raise, existsTest_rename]) ho

end PPAC.Migration.Internal.FixedAxiomTableExistence
