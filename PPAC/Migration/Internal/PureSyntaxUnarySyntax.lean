import PPAC.Migration.Internal.PureSyntaxBinaryComplete

/-! 三种原unary规则的固定索引及内部绑定界后继；不把内部上下文当宿主Nat。 -/
namespace PPAC.Migration.Internal.PureSyntaxUnarySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def tag (kind : Fin 3) : Nat := if kind.val = 0 then 4 else if kind.val = 1 then 9 else 10
def advance (kind : Fin 3) : Bool := kind.val != 0
def boundExpr (adv : Bool) : Expr 3 := if adv then .succ (.var 0) else .var 0
def input (kind : Fin 3) : Expr 3 := Expr.node (.literal (tag kind)) [.var 2]

theorem actual_head (kind : Fin 3) : (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)).head =
    PureSyntaxFormulaGraph.head (0 : Fin 3) 1 (input kind) := rfl

theorem actual_premises (kind : Fin 3) : (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)).premises =
    [PureSyntaxFormulaPremise.head (boundExpr (advance kind)) (1 : Fin 3) 2] := rfl

theorem rule_mem (kind : Fin 3) : ObjectFormulaSyntax.unaryRule (tag kind) (advance kind) ∈ PureSyntaxRules.rules := by
  rcases kind with ⟨k, hk⟩
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · change ObjectFormulaSyntax.unaryRule 4 false ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]
  · change ObjectFormulaSyntax.unaryRule 9 true ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]
  · change ObjectFormulaSyntax.unaryRule 10 true ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]

theorem known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.singleTypes (advance kind) w b f x)) := by
  rcases kind with ⟨k, hk⟩
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact FormulaCodeKnownLogical.negation_iff hZ w b f x n hw hc
  · exact FormulaCodeKnownLogical.forall_iff hZ w b f x n hw hc
  · exact FormulaCodeKnownLogical.exists_iff hZ w b f x n hw hc

theorem input_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((graph (input kind) w env n).iff (SyntaxLogicalSyntax.singleCode (tag kind) w (env 2) n)) := by
  simpa only [input, SyntaxLogicalSyntax.singleCode, List.ofFn_succ, List.ofFn_zero] using
    HornExprConstructor.constructor_iff hZ 1 (tag kind) (fun _ : Fin 1 => Expr.var (2 : Fin 3)) w n env (fun _ => env 2) hw hn
      (fun _ => Derives.conjI (environmentNat_at w env hn 2) (.eqRefl _))

theorem step_from_premise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (adv : Bool) (w n R : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hi : Derives Γ (allIH w n)) (hl : Derives Γ (.mem (env 2) n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise (PureSyntaxFormulaPremise.head (boundExpr adv) 1 2) w R env)) :
    Derives Γ (FormulaCodeRecursiveSyntax.stepCheck adv w (env 2) (env 0) (env 1)) := by
  cases adv with
  | false =>
    have hb : Derives Γ (graph (.var (0 : Fin 3)) w env (env 0)) := .conjI (environmentNat_at w env hn 0) (.eqRefl _)
    exact PureSyntaxFormulaPremise.typed_from_induction hZ (.var (0 : Fin 3)) 1 2 w n (env 0) R env hw hn hi hl hb hs hc hp
  | true =>
    let E : Expr 3 := .succ (.var 0)
    let A := (Formula.mem (Fin.last m) w.castSucc).conj (graph E w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ := Context.add A (Context.image Formula.raise Γ)
    apply Derives.exE (p := A) (HornExprExistence.exists_value hZ E w env hw hn)
    have hZ1 := ZFContext.under hZ A
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
    have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn A)
    have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi A)
    have hl1 : Derives Δ (.mem (env 2).castSucc n.castSucc) := under hl A
    have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs A)
    have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc A)
    have hp1 : Derives Δ (HornRuleSyntax.premise (PureSyntaxFormulaPremise.head E 1 2) w.castSucc R.castSucc (fun i => (env i).castSucc)) := of_eq
      (HornRuleSyntax.premise_rename _ w R env Fin.castSucc) (under hp A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hb := PureSyntaxArgumentPremises.succ_variable (0 : Fin 3) w.castSucc (Fin.last m) (fun i => (env i).castSucc) (.conjR hA)
    have ht := PureSyntaxFormulaPremise.typed_from_induction hZ1 E 1 2 w.castSucc n.castSucc (Fin.last m) R.castSucc (fun i => (env i).castSucc) hw1 hn1 hi1 hl1 (.conjR hA) hs1 hc1 hp1
    have hout := FormulaCodeRecursiveSyntax.intro_advanced w.castSucc (env 2).castSucc (env 0).castSucc (env 1).castSucc (Fin.last m) hb ht
    exact of_eq (FormulaCodeRecursiveSyntax.advancedCode_rename w (env 2) (env 0) (env 1) Fin.castSucc).symm hout

end PPAC.Migration.Internal.PureSyntaxUnarySyntax
