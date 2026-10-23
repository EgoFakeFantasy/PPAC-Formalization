import PPAC.Migration.Internal.OriginalLookupRuleMatrix

/-! 上游有限搜索的赋值界：固定真实表达式中每个出现变量的内部值不超过实际头行码。 -/
namespace PPAC.Migration.Internal.HornExprBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NaturalAdditionBounds (below below_rename)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def environmentBound {m} : (n : Nat) → Fin m → (Fin n → Fin m) → Formula m
  | 0, _, _ => .imp .bot .bot
  | n+1, row, env => (below (env 0) row).conj (environmentBound n row (fun i => env i.succ))

theorem environmentBound_rename {m k} (n : Nat) (row : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (environmentBound n row env).rename ρ = environmentBound n (ρ row) (fun i => ρ (env i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [environmentBound, Formula.rename, below_rename, ih]

theorem intro_environmentBound {m n} {Γ : Context m} (row : Fin m) (env : Fin n → Fin m)
    (hi : ∀ i, Derives Γ (below (env i) row)) : Derives Γ (environmentBound n row env) := by
  induction n with
  | zero => exact HornRuleSyntax.truth_proved
  | succ n ih => exact .conjI (hi 0) (ih (fun i => env i.succ) (fun i => hi i.succ))

theorem variable_bound {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (i : Fin n)
    (hi : i ∈ e.variables) (w y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hy : Derives Γ (graph e w env y)) :
    Derives Γ (below (env i) y) := by
  induction e generalizing m with
  | literal _ => simp only [Expr.variables, List.not_mem_nil] at hi
  | var j =>
    have he : i = j := List.mem_singleton.mp hi
    subst i
    exact .disjL (eq_symm (.conjR hy))
  | succ e ih =>
    let B := (graph e w.castSucc (fun j => (env j).castSucc) (Fin.last m)).conj (successor y.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise Γ)
    apply Derives.exE (p := B) hy
    have hZ1 := ZFContext.under hZ B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun j => (env j).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hx := HornExprRange.range hZ1 e _ _ _ hw1 hn1 (.conjL hB)
    have hY := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 hx (.conjR hB)
    exact .disjR (NaturalArithmeticBounds.below_mem_trans hZ1 _ _ _ _ hw1 hY (ih hZ1 hi _ _ _ hw1 hn1 (.conjL hB)) (InsertLogic.new_member _ _ _ (.conjR hB)))
  | pair e f ihe ihf =>
    let B := (graph e w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last m).castSucc).conj
      ((graph f w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last (m+1))).conj
        (GodelPairSyntax.code w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
    apply SyntaxRenameBinders.eliminate_2 B _ hy
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
    have hn2 : Derives Δ (environmentNat n w.castSucc.castSucc (fun j => (env j).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (SyntaxRenameBinders.under_2 hn B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hb := GodelPairBounds.components hZ2 _ _ _ _ hw2
      (HornExprRange.range hZ2 e _ _ _ hw2 hn2 (.conjL hB))
      (HornExprRange.range hZ2 f _ _ _ hw2 hn2 (.conjL (.conjR hB))) (.conjR (.conjR hB))
    have hY := GodelPairCore.range hZ2 _ _ _ _ hw2 (.conjR (.conjR hB))
    rcases List.mem_append.mp hi with he | hf
    · exact NaturalOrderBasic.transitive hZ2 _ _ _ _ hw2 hY (ihe hZ2 he _ _ _ hw2 hn2 (.conjL hB)) (.conjL hb)
    · exact NaturalOrderBasic.transitive hZ2 _ _ _ _ hw2 hY (ihf hZ2 hf _ _ _ hw2 hn2 (.conjL (.conjR hB))) (.conjR hb)

theorem lookup_head_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hy : Derives Γ (graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head w env row)) :
    Derives Γ (environmentBound 2 row env) := by
  have hi : ∀ i : Fin 2, i ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head.variables := by decide
  exact intro_environmentBound row env (fun i => variable_bound hZ _ i (hi i) w row env hw hn hy)

theorem lookup_tail_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hy : Derives Γ (graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head w env row)) :
    Derives Γ (environmentBound 4 row env) := by
  have hi : ∀ i : Fin 4, i ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head.variables := by decide
  exact intro_environmentBound row env (fun i => variable_bound hZ _ i (hi i) w row env hw hn hy)

end PPAC.Migration.Internal.HornExprBounds
