import PPAC.Migration.Internal.HornBinderRules
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

/-- Actual output child of a unary substitution. For quantifiers, check true
is the EXISTING advanced predicate: it internally quantifies the original
source/target successors, both lifted code tables and actual child judgment. -/
def singleOutput {m} (tag : Nat) (advance : Bool) (w R S a b c d x Q : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) Q.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)))

theorem singleOutput_rename {m l} (tag : Nat) (advance : Bool) (w R S a b c d x Q : Fin m) (r : Fin m → Fin l) :
    (singleOutput tag advance w R S a b c d x Q).rename r = singleOutput tag advance (r w) (r R) (r S) (r a) (r b) (r c) (r d) (r x) (r Q) := by
  simp only [singleOutput, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxMixedFormulaRecursiveSyntax.check_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Extract the actual target child from the actual parent output; no supplied
child code, lifting witness, local answer or external-standard scope. -/
theorem single_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x Q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hn : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q)) :
    Derives Γ (singleOutput tag advance w R S a b c d x Q) := by
  have hs := SyntaxMixedFormulaLogicalKnown.single_of_substituted hZ tag advance valid w R S a b c d n Q x hw hc hn
  let E := SyntaxMixedFormulaRecursiveSyntax.singleBody tag advance w R S a b c d n Q
  let Δ := Context.add E (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hs
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hw2 := of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw E)
  have hc2 := of_eq (SyntaxLogicalSyntax.singleCode_rename tag w x n (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hc E)
  have es := SyntaxLogicalFields.single_fields hZ2 tag (HornBinderSyntax.old 2 w) (HornBinderSyntax.slot 2 0) (HornBinderSyntax.old 2 x) (HornBinderSyntax.old 2 n) hw2 (.conjL hE) hc2
  have hchild := SyntaxMixedFormulaLogicalSubst.check_source advance (HornBinderSyntax.old 2 w) (HornBinderSyntax.slot 2 0)
    (HornBinderSyntax.old 2 R) (HornBinderSyntax.old 2 S) (HornBinderSyntax.old 2 a) (HornBinderSyntax.old 2 b)
    (HornBinderSyntax.old 2 c) (HornBinderSyntax.old 2 d) (HornBinderSyntax.slot 2 1) (HornBinderSyntax.old 2 x) es (.conjR (.conjR (.conjR hE)))
  have hout : Derives Δ (singleOutput tag advance (HornBinderSyntax.old 2 w) (HornBinderSyntax.old 2 R) (HornBinderSyntax.old 2 S)
      (HornBinderSyntax.old 2 a) (HornBinderSyntax.old 2 b) (HornBinderSyntax.old 2 c) (HornBinderSyntax.old 2 d) (HornBinderSyntax.old 2 x) (HornBinderSyntax.old 2 Q)) := by
    apply Derives.exI (HornBinderSyntax.slot 2 1)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
      SyntaxMixedFormulaRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjL (.conjR (.conjR hE))) hchild)
  exact of_eq (singleOutput_rename tag advance w R S a b c d x Q (HornBinderSyntax.old 2)).symm hout

private theorem from_single_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x Q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (ho : Derives Γ (singleOutput tag advance w R S a b c d x Q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q) := by
  let E := (SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) Q.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) ho
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hiff := SyntaxMixedFormulaEndpoints.single_iff (ZFContext.under hZ E) tag advance valid
    w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc Q.castSucc x.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E))
    (of_eq (SyntaxMixedFormulaOutputSyntax.input_rename w R S a b c d n Fin.castSucc) (under hi E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename tag w x n Fin.castSucc) (under hc E)) (.conjL hE)
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d n Q Fin.castSucc).symm
    (Derives.impE (.conjR hiff) (.conjR hE))

/-- Exact unary output equation, with all actual target children internally
quantified. The typed input is retained for the reverse direction. -/
theorem single_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x Q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n)) :
    Derives Γ ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n Q).iff (singleOutput tag advance w R S a b c d x Q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact single_output (ZFContext.add hZ _) tag advance valid w R S a b c d n x Q (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_single_output (ZFContext.add hZ _) tag advance valid w R S a b c d n x Q (add hw _) (add hi _) (add hc _) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingMixedUnary
