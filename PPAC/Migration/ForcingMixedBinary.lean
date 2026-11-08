import PPAC.Migration.Internal.SyntaxMixedFormulaOutputInduction
import PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints

/-! Constructor transport needed by both name reification and pointwise
opening. Reuse the existing binary endpoint, constructor existence and actual
output uniqueness; no new syntax, evaluator or recursion is defined. -/
namespace PPAC.Migration.ForcingMixedBinary
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Independent actual substitution outputs preserve each literal binary
constructor, including at all internal/nonstandard source and target scopes. -/
theorem binary_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n x y Q X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hn : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q))
    (hx : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y)) :
    Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y Q) := by
  have hX := Derives.conjL (FormulaCodeProperties.guards w X c d (SyntaxMixedFormulaJudgment.target_type w R S a b c d x X hx))
  have hY := Derives.conjL (FormulaCodeProperties.guards w Y c d (SyntaxMixedFormulaJudgment.target_type w R S a b c d y Y hy))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxLogicalSyntax.binaryCode kind w.castSucc X.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have he := SyntaxConstructors.exists_constructor hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two X Y) hw (.conjI hX (.conjI hY (.eqRefl w)))
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxLogicalSyntax.binaryCode, SyntaxAtomSyntax.two_map]) he
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hi1 := of_eq (SyntaxMixedFormulaOutputSyntax.input_rename w R S a b c d n Fin.castSucc) (under hi E)
  have hc1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n Fin.castSucc) (under hc E)
  have hx1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d x X Fin.castSucc) (under hx E)
  have hy1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d y Y Fin.castSucc) (under hy E)
  have hn1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d n Q Fin.castSucc) (under hn E)
  have hiff := SyntaxMixedFormulaEndpoints.binary_iff (ZFContext.under hZ E) kind w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc
    n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc hw1 hi1 hc1 (.conjR hE)
  have hnew := Derives.impE (.conjR hiff) (.conjI hx1 hy1)
  have eq := SyntaxMixedFormulaOutputInduction.unique (ZFContext.under hZ E) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc
    n.castSucc Q.castSucc (Fin.last m) hw1 hn1 hnew
  let P := SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last (m+1))
  have hout : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc X.castSucc Y.castSucc Q.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P (eq_symm eq) (of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hE)))
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w X Y Q Fin.castSucc).symm hout

end PPAC.Migration.ForcingMixedBinary
