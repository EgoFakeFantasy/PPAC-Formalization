import PPAC.Migration.Internal.SyntaxMixedFormulaOutputInduction
import PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints

/-! Actual unary constructor transport for reification and opening of forcing
fragments. Existing substitution endpoints, constructor existence and output
uniqueness are reused. Quantifiers use the ORIGINAL lifted environment and
its actual child judgment, including all internal/nonstandard scopes. -/
namespace PPAC.Migration.ForcingMixedUnary
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem at_child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x Q X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hn : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q))
    (hX : Derives Γ (.mem X w))
    (hx : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x R S a b c d X)) :
    Derives Γ (SyntaxLogicalSyntax.singleCode tag w X Q) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxLogicalSyntax.singleCode tag w.castSucc X.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have he := SyntaxConstructors.exists_constructor hZ 1 tag w (fun _ => X) hw (.conjI hX (.eqRefl w))
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxLogicalSyntax.singleCode]) he
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hi1 := of_eq (SyntaxMixedFormulaOutputSyntax.input_rename w R S a b c d n Fin.castSucc) (under hi E)
  have hc1 := of_eq (SyntaxLogicalSyntax.singleCode_rename tag w x n Fin.castSucc) (under hc E)
  have hn1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d n Q Fin.castSucc) (under hn E)
  have hx1 := of_eq (SyntaxMixedFormulaRecursiveSyntax.check_rename advance w x R S a b c d X Fin.castSucc) (under hx E)
  have hiff := SyntaxMixedFormulaEndpoints.single_iff (ZFContext.under hZ E) tag advance valid
    w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc hw1 hi1 hc1 (.conjR hE)
  have hnew := Derives.impE (.conjR hiff) hx1
  have eq := SyntaxMixedFormulaOutputInduction.unique (ZFContext.under hZ E) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc
    n.castSucc Q.castSucc (Fin.last m) hw1 hn1 hnew
  let P := SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc X.castSucc.castSucc (Fin.last (m+1))
  have hout : Derives Δ (SyntaxLogicalSyntax.singleCode tag w.castSucc X.castSucc Q.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P (eq_symm eq) (of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hE)))
  exact of_eq (SyntaxLogicalSyntax.singleCode_rename tag w X Q Fin.castSucc).symm hout

/-- Independent actual parent/child outputs preserve literal negation. -/
theorem negation_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n x Q X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    (hn : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q))
    (hx : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X)) :
    Derives Γ (SyntaxLogicalSyntax.singleCode 4 w X Q) :=
  at_child hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S a b c d n x Q X hw hi hc hn
    (.conjL (FormulaCodeProperties.guards w X c d (SyntaxMixedFormulaJudgment.target_type w R S a b c d x X hx))) hx

/-- Both quantifiers preserve their actual child under the ORIGINAL lifted
mixed environment; source and target successor scopes are independent. -/
theorem quantified_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w R S a b c d n x Q X A C K H : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hn : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hx : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X)) :
    Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X Q) := by
  have hX := Derives.conjL (FormulaCodeProperties.guards w X C d (SyntaxMixedFormulaJudgment.target_type w K H A b C d x X hx))
  have hchild := Derives.impE (.conjR (SyntaxMixedFormulaAdvancedOutput.at_lift hZ w x R S a b c d X A C K H hw hl)) hx
  have valid : ((SyntaxLogicalSyntax.quantifierTag universal) = 4 ∧ true = false) ∨
      ((SyntaxLogicalSyntax.quantifierTag universal) = 9 ∧ true = true) ∨
      ((SyntaxLogicalSyntax.quantifierTag universal) = 10 ∧ true = true) := by
    cases universal <;> simp only [SyntaxLogicalSyntax.quantifierTag] <;> simp
  exact at_child hZ (SyntaxLogicalSyntax.quantifierTag universal) true valid w R S a b c d n x Q X hw hi hc hn hX hchild

end PPAC.Migration.ForcingMixedUnary
