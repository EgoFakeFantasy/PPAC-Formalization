import PPAC.Migration.Internal.LogicalInstantiateQueries
import PPAC.Migration.Internal.HornApplicationBounds

/-! 原零绑定界语法查询及任意固定有限查询合取；运行码全部属于对象层。 -/
namespace PPAC.Migration.Internal.LogicalStaticQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def query {a} (isTerm : Bool) (free input : Fin a) : Expr a :=
  (ObjectLogicalAxiom.grammar isTerm (.literal 0) (.var free) (.var input)).2

def typed {m} (isTerm : Bool) (w z free input : Fin m) : Formula m :=
  if isTerm then SyntaxTermSyntax.term w z free input else FormulaCodeSyntax.formulaCode w input z free

theorem query_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isTerm : Bool)
    (free input : Fin a) (w z : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query (query isTerm free input) w env).iff (typed isTerm w z (env free) (env input))) := by
  cases isTerm with
  | true => exact LogicalInstantiateQueries.term_iff hZ free input w z env hw hn hz
  | false =>
    have hv (i : Fin a) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
    exact PureSyntaxQueryTyping.formula_iff hZ (LogicalInstantiateQueries.fields 0 free input) w z (env free) (env input) env hw hn
      (fun i => Fin.cases hz (fun j => Fin.cases (hv free) (fun k => Fin.cases (hv input) (fun v => Fin.elim0 v) k) j) i)

def conjoin {m} : (n : Nat) → (Fin n → Formula m) → Formula m
  | 0, _ => HornRuleSyntax.truth
  | n+1, ps => (ps 0).conj (conjoin n (fun i => ps i.succ))

theorem conjoin_rename {m l} (n : Nat) (ps : Fin n → Formula m) (ρ : Fin m → Fin l) :
    (conjoin n ps).rename ρ = conjoin n (fun i => (ps i).rename ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [conjoin, Formula.rename, ih]

theorem conjoin_iff {m} {Γ : Context m} (n : Nat) (ps qs : Fin n → Formula m)
    (hs : ∀ i, Derives Γ ((ps i).iff (qs i))) : Derives Γ ((conjoin n ps).iff (conjoin n qs)) := by
  induction n with
  | zero => exact SyntaxTypeLocalTransfer.iff_refl HornRuleSyntax.truth
  | succ n ih => exact FormulaCodeCongruence.conj_congr (hs 0) (ih (fun i => ps i.succ) (fun i => qs i.succ) (fun i => hs i.succ))

def originalQueries (n : Nat) (isTerm : Bool) : List (Bool × Expr (n+1)) :=
  (List.finRange n).map (fun i => (false, query isTerm 0 i.succ))

def bundle {m} (n : Nat) (isTerm : Bool) (w : Fin m) (env : Fin (n+1) → Fin m) : Formula m :=
  conjoin n (fun i => PureSyntaxExprQuery.query (query isTerm 0 i.succ) w env)

def types {m} (n : Nat) (isTerm : Bool) (w z : Fin m) (env : Fin (n+1) → Fin m) : Formula m :=
  conjoin n (fun i => typed isTerm w z (env 0) (env i.succ))

theorem bundle_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (n : Nat) (isTerm : Bool)
    (w z : Fin m) (env : Fin (n+1) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat (n+1) w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle n isTerm w env).iff (types n isTerm w z env)) :=
  conjoin_iff n _ _ (fun i => query_iff hZ isTerm 0 i.succ w z env hw hn hz)

end PPAC.Migration.Internal.LogicalStaticQueries
