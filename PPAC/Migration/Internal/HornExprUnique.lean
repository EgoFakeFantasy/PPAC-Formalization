import PPAC.Migration.Internal.HornExprExistence

/-! 对齐所有隐藏子值，证明原Horn表达式的内部单值性；无宿主数值求值假设。 -/
namespace PPAC.Migration.Internal.HornExprUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem pair_left_subst {m} {Γ : Context m} (w a c b p : Fin m) (he : Derives Γ (.equal a c))
    (hp : Derives Γ (GodelPairSyntax.code w a b p)) : Derives Γ (GodelPairSyntax.code w c b p) := by
  let P := GodelPairSyntax.code w.castSucc (Fin.last m) b.castSucc p.castSucc
  have h0 : P.instantiate a = GodelPairSyntax.code w a b p := by simp only [P, Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate c = GodelPairSyntax.code w c b p := by simp only [P, Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem pair_right_subst {m} {Γ : Context m} (w a b c p : Fin m) (he : Derives Γ (.equal b c))
    (hp : Derives Γ (GodelPairSyntax.code w a b p)) : Derives Γ (GodelPairSyntax.code w a c p) := by
  let P := GodelPairSyntax.code w.castSucc a.castSucc (Fin.last m) p.castSucc
  have h0 : P.instantiate b = GodelPairSyntax.code w a b p := by simp only [P, Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate c = GodelPairSyntax.code w a c p := by simp only [P, Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem unique {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w y z : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hy : Derives Γ (graph e w env y)) (hz : Derives Γ (graph e w env z)) : Derives Γ (.equal y z) := by
  induction e generalizing m with
  | literal k => exact SyntaxNumerals.unique hZ k y z hy hz
  | var _ => exact eq_trans (.conjR hy) (eq_symm (.conjR hz))
  | succ e ih =>
    let C := (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (successor y.castSucc (Fin.last m))
    let Δ := Context.add C (Context.image Formula.raise Γ)
    apply Derives.exE (p := C) hy
    have hZ1 := ZFContext.under hZ C
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw C)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn C)
    have hz1 : Derives Δ (graph (.succ e) w.castSucc (fun i => (env i).castSucc) z.castSucc) := of_eq (graph_rename (.succ e) w z env Fin.castSucc) (under hz C)
    let D := (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj (successor z.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add D (Context.image Formula.raise Δ)
    apply Derives.exE (p := D) hz1
    have hZ2 := ZFContext.under hZ1 D
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 D)
    have hn2 : Derives Ξ (environmentNat n w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 D)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hC2 : Derives Ξ ((graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj (successor y.castSucc.castSucc (Fin.last m).castSucc)) := of_eq
      (by simp only [C, Formula.raise, Formula.rename, graph_rename, successor_rename]) (under hC D)
    have hD : Derives Ξ D := .hyp (Or.inl rfl)
    have he := ih hZ2 _ _ _ _ hw2 hn2 (.conjL hC2) (.conjL hD)
    exact OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ2).base.extensionality
      (GodelUnpairArithmetic.successor_base_subst _ _ _ he (.conjR hC2)) (.conjR hD)
  | pair e f ihe ihf =>
    let C := (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj
      ((graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj
        (GodelPairSyntax.code w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    apply SyntaxRenameBinders.eliminate_2 C _ hy
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hn2 : Derives Δ (environmentNat n w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (SyntaxRenameBinders.under_2 hn C)
    have hz2 : Derives Δ (graph (.pair e f) w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) z.castSucc.castSucc) := of_eq
      (by simp only [Formula.raise, graph_rename]) (SyntaxRenameBinders.under_2 hz C)
    let D := (graph e w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+2)).castSucc).conj
      ((graph f w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3))).conj
        (GodelPairSyntax.code w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) z.castSucc.castSucc.castSucc.castSucc))
    let Ξ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Δ))
    apply SyntaxRenameBinders.eliminate_2 D _ hz2
    have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 D
    have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 D)
    have hn4 : Derives Ξ (environmentNat n w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc)) := of_eq
      (by simp only [Formula.raise, environmentNat_rename]) (SyntaxRenameBinders.under_2 hn2 D)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hC4 : Derives Ξ ((graph e w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc).conj
      ((graph f w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc).conj
        (GodelPairSyntax.code w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc))) := of_eq
      (by simp only [C, Formula.raise, Formula.rename, graph_rename, GodelPairSyntax.code_rename]) (SyntaxRenameBinders.under_2 hC D)
    have hD : Derives Ξ D := .hyp (Or.inl rfl)
    have he := ihe hZ4 _ _ _ _ hw4 hn4 (.conjL hC4) (.conjL hD)
    have hf := ihf hZ4 _ _ _ _ hw4 hn4 (.conjL (.conjR hC4)) (.conjL (.conjR hD))
    have hp := pair_right_subst _ _ _ _ _ hf (pair_left_subst _ _ _ _ _ he (.conjR (.conjR hC4)))
    exact GodelPairCore.unique hZ4 _ _ _ _ _ hw4
      (HornExprRange.range hZ4 e _ _ _ hw4 hn4 (.conjL hD))
      (HornExprRange.range hZ4 f _ _ _ hw4 hn4 (.conjL (.conjR hD))) hp (.conjR (.conjR hD))

end PPAC.Migration.Internal.HornExprUnique
