import PPAC.Migration.Internal.OriginalLookupDispatch

/-! 有限存在块逐原ex规则传输双条件；原后继搜索界的成员形式。 -/
namespace PPAC.Migration.Internal.HornApplicationBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax HornExprBounds HornRuleSyntax HornApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

def insideBody {m} (rule : Rule) (w row trace s : Fin m) : Formula (m+rule.arity) :=
  (environmentNat rule.arity (old rule.arity s) (slot rule.arity)).conj
    (matrix rule (old rule.arity w) (old rule.arity row) (old rule.arity trace) (slot rule.arity))

def boundedAt {m} (rule : Rule) (w row trace s : Fin m) : Formula m := existsMany rule.arity (insideBody rule w row trace s)

theorem insideBody_lift {m k} (rule : Rule) (w row trace s : Fin m) (ρ : Fin m → Fin k) :
    (insideBody rule w row trace s).rename (lift rule.arity ρ) = insideBody rule (ρ w) (ρ row) (ρ trace) (ρ s) := by
  simp only [insideBody, Formula.rename, environmentNat_rename, matrix_rename, lift_old, lift_slot]

theorem boundedAt_rename {m k} (rule : Rule) (w row trace s : Fin m) (ρ : Fin m → Fin k) :
    (boundedAt rule w row trace s).rename ρ = boundedAt rule (ρ w) (ρ row) (ρ trace) (ρ s) := by
  simp only [boundedAt, existsMany_rename, insideBody_lift]

theorem existsMany_congr {m} {Γ : Context m} (n : Nat) (B C : Formula (m+n))
    (he : Derives (raisedContext n Γ) (B.iff C)) : Derives Γ ((existsMany n B).iff (existsMany n C)) := by
  induction n with
  | zero => exact he
  | succ n ih => exact ih (.ex B) (.ex C) (FormulaCodeCongruence.ex_congr he)

theorem bound_iff_inside {m n} {Γ : Context m} (row s : Fin m) (env : Fin n → Fin m)
    (hs : Derives Γ (successor s row)) :
    Derives Γ ((environmentBound n row env).iff (environmentNat n s env)) := by
  induction n with
  | zero => exact SyntaxTypeLocalTransfer.iff_refl truth
  | succ n ih =>
    have hh := NaturalOrderBasic.successor_iff (env 0) row s hs
    exact FormulaCodeCongruence.conj_congr (.conjI (.conjR hh) (.conjL hh)) (ih (fun i => env i.succ))

theorem matrix_iff_inside {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (w row trace s : Fin m)
    (env : Fin rule.arity → Fin m) (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) (hs : Derives Γ (successor s row)) :
    Derives Γ ((boundedMatrix rule w row trace env).iff ((environmentNat rule.arity s env).conj (matrix rule w row trace env))) := by
  have hh := bound_iff_inside row s env hs
  apply Derives.conjI
  · apply Derives.impI
    have hb : Derives (Context.add (boundedMatrix rule w row trace env) Γ) (boundedMatrix rule w row trace env) := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjL hh) _) (.conjL (.conjR hb))) (.conjR (.conjR hb))
  · apply Derives.impI
    let I := (environmentNat rule.arity s env).conj (matrix rule w row trace env)
    have hi : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    have hb := Derives.impE (add (.conjR hh) I) (.conjL hi)
    exact .conjI (HornApplicationRules.natural_environment (ZFContext.add hZ I) w row env (add hw I) (add hr I) hb) (.conjI hb (.conjR hi))

theorem application_iff_boundedAt {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (w row trace s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) (hs : Derives Γ (successor s row)) :
    Derives Γ ((application rule w row trace).iff (boundedAt rule w row trace s)) := by
  apply existsMany_congr rule.arity
  have hw1 := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_many rule.arity hw)
  have hr1 : Derives (raisedContext rule.arity Γ) (.mem (old rule.arity row) (old rule.arity w)) := HornBinderRules.under_many rule.arity hr
  have hs1 := of_eq (successor_rename s row (old rule.arity)) (HornBinderRules.under_many rule.arity hs)
  exact matrix_iff_inside (HornBinderRules.zf_many rule.arity hZ) rule _ _ _ _ _ hw1 hr1 hs1

end PPAC.Migration.Internal.HornApplicationBounds
