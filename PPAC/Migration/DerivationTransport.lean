import PPAC.Migration.SyntaxTransport
import PPAC.Migration.SourceDerivation
import YesMetaZFC.Logic.FirstOrder.Derivation.Classical
import YesMetaZFC.Logic.FirstOrder.Derivation.Equality

/-! 按源19条规则归纳，直接返回原Hilbert核Derives；不经过模型语义或完备性。 -/
namespace PPAC.Migration.Compile
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory Syntax
attribute [local implicit_reducible] SetTheory.signature

theorem weaken_free {σ : Signature.{u, v, w}} {T : FirstOrder.Theory σ}
    {free : FirstOrder.SortContext σ} {sort : σ.SortSymbol}
    {Δ : FirstOrder.Context σ free} {p : FirstOrder.OpenFormula σ free}
    (h : FirstOrder.Derives T Δ p) :
    FirstOrder.Derives T (FreshVariable.extendContext sort Δ) (p.weakenFree sort) :=
  FirstOrder.Derives.free_renaming (VariableRenaming.weaken sort) h

theorem neg_as_imp {T : FirstOrder.Theory ℒ} {free : Ctx}
    {Δ : FirstOrder.Context ℒ free} {p : Fm [] free}
    (h : FirstOrder.Derives T Δ (.neg p)) :
    FirstOrder.Derives T Δ (.imp p .falsum) := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.neg_elim
    (FirstOrder.Derives.assumption List.mem_cons_self) h.context_weaken_cons

theorem supply_add {n} {Γ : Source.Context n} {T : FirstOrder.Theory ℒ}
    {free : Ctx} (ρ : Fin n → Tm [] free) (Δ : FirstOrder.Context ℒ free)
    (hΓ : ∀ q, Γ q → FirstOrder.Derives T Δ (formula ρ q)) (p : Source.Formula n) :
    ∀ q, Source.Context.add p Γ q →
      FirstOrder.Derives T (formula ρ p :: Δ) (formula ρ q) := by
  intro q hq
  rcases hq with rfl | hq
  · exact FirstOrder.Derives.assumption List.mem_cons_self
  · exact (hΓ q hq).context_weaken_cons

/-- 无限源假设由逐项可推导性提供；目标上下文Δ始终是有限列表。 -/
theorem derives {n} {Γ : Source.Context n} {p : Source.Formula n}
    (d : Source.Derives Γ p) {T : FirstOrder.Theory ℒ} {free : Ctx}
    (ρ : Fin n → Tm [] free) (Δ : FirstOrder.Context ℒ free)
    (hΓ : ∀ q, Γ q → FirstOrder.Derives T Δ (formula ρ q)) :
    FirstOrder.Derives T Δ (formula ρ p) := by
  induction d generalizing free with
  | hyp hp => exact hΓ _ hp
  | weaken hsub d ih => exact ih ρ Δ (fun q hq => hΓ q (hsub q hq))
  | @impI n Γ p q d ih =>
      exact FirstOrder.Derives.imp_intro (ih ρ (formula ρ p :: Δ) (supply_add ρ Δ hΓ p))
  | impE dpq dp ihpq ihp =>
      exact FirstOrder.Derives.imp_elim (ihpq ρ Δ hΓ) (ihp ρ Δ hΓ)
  | botE d ih => exact FirstOrder.Derives.falsum_elim (ih ρ Δ hΓ)
  | @classical n Γ p d ih =>
      apply FirstOrder.Derives.by_contradiction
      apply ih ρ (.neg (formula ρ p) :: Δ)
      intro q hq
      rcases hq with rfl | hq
      · exact neg_as_imp (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact (hΓ q hq).context_weaken_cons
  | conjI dp dq ihp ihq =>
      exact FirstOrder.Derives.conj_intro (ihp ρ Δ hΓ) (ihq ρ Δ hΓ)
  | conjL d ih => exact FirstOrder.Derives.conj_elim_left (ih ρ Δ hΓ)
  | conjR d ih => exact FirstOrder.Derives.conj_elim_right (ih ρ Δ hΓ)
  | disjL d ih => exact FirstOrder.Derives.disj_intro_left (ih ρ Δ hΓ)
  | disjR d ih => exact FirstOrder.Derives.disj_intro_right (ih ρ Δ hΓ)
  | @disjE n Γ p q r dpq dpr dqr ihpq ihpr ihqr =>
      exact FirstOrder.Derives.disj_elim (ihpq ρ Δ hΓ)
        (ihpr ρ (formula ρ p :: Δ) (supply_add ρ Δ hΓ p))
        (ihqr ρ (formula ρ q :: Δ) (supply_add ρ Δ hΓ q))
  | @allI n Γ p d ih =>
      have hb : FirstOrder.Derives T (FreshVariable.extendContext SetSort.set Δ)
          (formula (fresh ρ) p) := by
        apply ih (fresh ρ) (FreshVariable.extendContext SetSort.set Δ)
        rintro q ⟨r, hr, rfl⟩
        simpa only [fresh_raise] using weaken_free (sort := SetSort.set) (hΓ r hr)
      simpa only [forall_fresh] using FirstOrder.Derives.forall_intro hb
  | @allE n Γ p t d ih =>
      simpa only [formula, instantiate] using
        FirstOrder.Derives.forall_elim (ρ t) (ih ρ Δ hΓ)
  | @exI n Γ p t d ih =>
      apply FirstOrder.Derives.exists_intro (body := formula (lift ρ) p) (ρ t)
      simpa only [instantiate] using ih ρ Δ hΓ
  | @exE n Γ p q dex dcase ihex ihcase =>
      apply FirstOrder.Derives.exists_elim (body := formula (fresh ρ) p)
      · simpa only [exists_fresh] using ihex ρ Δ hΓ
      · have hb : FirstOrder.Derives T
            (formula (fresh ρ) p :: FreshVariable.extendContext SetSort.set Δ)
            (formula (fresh ρ) q.raise) := by
          apply ihcase (fresh ρ) (formula (fresh ρ) p :: FreshVariable.extendContext SetSort.set Δ)
          intro r hr
          rcases hr with rfl | ⟨s, hs, rfl⟩
          · exact FirstOrder.Derives.assumption List.mem_cons_self
          · have hs' : FirstOrder.Derives T (FreshVariable.extendContext SetSort.set Δ)
                  (formula (fresh ρ) s.raise) := by
                simpa only [fresh_raise] using weaken_free (sort := SetSort.set) (hΓ s hs)
            exact hs'.context_weaken_cons
        simpa only [fresh_raise] using hb
  | eqRefl t => exact FirstOrder.Derives.eq_refl (ρ t)
  | @eqSubst n Γ s t p deq dp iheq ihp =>
      have hb : FirstOrder.Derives T Δ ((formula (lift ρ) p).instantiateTop (ρ s)) := by
        simpa only [instantiate] using ihp ρ Δ hΓ
      simpa only [instantiate] using
        FirstOrder.Derives.eq_subst (body := formula (lift ρ) p) (iheq ρ Δ hΓ) hb
  | @rename n m Γ p r d ih =>
      rw [Syntax.rename]
      apply ih (fun i => ρ (r i)) Δ
      intro q hq
      simpa only [Syntax.rename] using hΓ (Source.Formula.rename r q) ⟨q, hq, rfl⟩
end PPAC.Migration.Compile
