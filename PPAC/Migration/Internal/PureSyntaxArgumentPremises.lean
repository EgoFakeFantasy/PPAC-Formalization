import PPAC.Migration.Internal.PureSyntaxListInductionSyntax

/-! 从原cons的真实EX前提行恢复头项类型及同一轨迹内的尾参数查询。 -/
namespace PPAC.Migration.Internal.PureSyntaxArgumentPremises
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxConsRule
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem succ_variable {m a} {Γ : Context m} (i : Fin a) (w y : Fin m) (env : Fin a → Fin m)
    (hg : Derives Γ (graph (.succ (.var i)) w env y)) : Derives Γ (successor y (env i)) := by
  let B := (graph (.var i) w.castSucc (fun j => (env j).castSucc) (Fin.last m)).conj (successor y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let P := successor y.castSucc.castSucc (Fin.last (m+1))
  have h0 : P.instantiate (Fin.last m) = successor y.castSucc (Fin.last m) := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate (env i).castSucc = successor y.castSucc (env i).castSucc := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hs := of_eq h1 (Derives.eqSubst P (.conjR (.conjL hB)) (of_eq h0.symm (.conjR hB)))
  exact of_eq (successor_rename y (env i) Fin.castSucc).symm hs

theorem head_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise (Expr.node (.literal 0) (List.ofFn headFields)) w R env)) :
    Derives Γ (SyntaxTermSyntax.term w (env 0) (env 1) (env 3)) := by
  let B := (graph (Expr.node (.literal 0) (List.ofFn headFields)) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 5 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 5 w env Fin.castSucc) (under hn B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc B)
  have hv (i : Fin 5) : Derives Δ (graph (.var i) w.castSucc (fun j => (env j).castSucc) (env i).castSucc) := .conjI (environmentNat_at _ _ hn1 i) (.eqRefl _)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornExprConstructor.constructor_iff hZ1 3 0 headFields w.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (SyntaxAtomSyntax.three (env 0).castSucc (env 1).castSucc (env 3).castSucc) hw1 hn1
    (fun j => Fin.cases (hv 0) (fun i => Fin.cases (hv 1) (fun l => Fin.cases (hv 3) (fun z => Fin.elim0 z) l) i) j)
  have hr := Derives.impE (.conjL hi) (.conjL hB)
  have ht := PureSyntaxTermMatrix.step_sound hZ1 _ _ _ _ _ _ hw1 hr
    (PureSyntaxTrace.closed_at _ _ _ hc1 (.conjR hB))
  exact of_eq (SyntaxTermSyntax.term_rename w (env 0) (env 1) (env 3) Fin.castSucc).symm ht

theorem tail_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise (Expr.node (.literal 1) (List.ofFn tailFields)) w R env)) :
    Derives Γ (PureSyntaxTrace.arguments w (env 0) (env 1) (env 2) (env 4)) := by
  let B := (graph (Expr.node (.literal 1) (List.ofFn tailFields)) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 5 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 5 w env Fin.castSucc) (under hn B)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc B)
  have hv (i : Fin 5) : Derives Δ (graph (.var i) w.castSucc (fun j => (env j).castSucc) (env i).castSucc) := .conjI (environmentNat_at _ _ hn1 i) (.eqRefl _)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornExprConstructor.constructor_iff hZ1 4 1 tailFields w.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (PureSyntaxTrace.four (env 0).castSucc (env 1).castSucc (env 2).castSucc (env 4).castSucc) hw1 hn1
    (fun j => Fin.cases (hv 0) (fun i => Fin.cases (hv 1) (fun l => Fin.cases (hv 2) (fun t => Fin.cases (hv 4) (fun z => Fin.elim0 z) t) l) i) j)
  have hr := Derives.impE (.conjL hi) (.conjL hB)
  have hcond := PureSyntaxTrace.intro_condition _ _ _ (.conjI hs1 (.conjI (.conjR hB) hc1))
  have hout := PureSyntaxNilComplete.intro_arguments _ _ _ _ _ _ hr hcond
  exact of_eq (PureSyntaxTrace.arguments_rename w (env 0) (env 1) (env 2) (env 4) Fin.castSucc).symm hout

end PPAC.Migration.Internal.PureSyntaxArgumentPremises
