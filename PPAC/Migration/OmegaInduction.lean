import PPAC.Migration.OmegaInductionCut

/-! 完整对象ω归纳模式：任意参数与任意公式的每个实例有正式推导。 -/
namespace PPAC.Migration.OmegaInduction
open Source SourceAlgebra SourceLogic OmegaSyntax MinimalPredicates OmegaInductionSyntax
open ReplacementPredicates (paramsUp)

theorem induction_on_omega {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hb : Derives Γ (base p ρ)) (ht : Derives Γ (step p ρ w)) :
    Derives Γ (holds p ρ w) := by
  have he := MinimalInstances.separation_instance p ρ w hs
  let S := separated p (paramsUp ρ) w.castSucc (Fin.last m)
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at he
  apply Derives.exE (p := S) he
  have hwS : Derives Γs (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw S
  have hbS : Derives Γs (base p (paramsUp ρ)) := by
    simpa only [Formula.raise, base_rename] using under hb S
  have htS : Derives Γs (step p (paramsUp ρ) w.castSucc) := by
    simpa only [Formula.raise, step_rename] using under ht S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hr := OmegaInductionCut.holds_from_separated p (paramsUp ρ) w.castSucc (Fin.last m) hwS hS hbS htS
  simpa only [Formula.raise, holds_rename] using hr

def assumptions {n} (p : Formula (n+1)) : Theory := fun q => q = Source.SetLanguage.separation p

theorem source_induction {n} (p : Formula (n+1)) :
    Derives ((assumptions p).at 0) (OmegaInductionSyntax.sentence p) := by
  apply close_derives
  apply Derives.allI
  rw [theory_at_raise]
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hs : Derives ((assumptions p).at (n+1)) ((Source.SetLanguage.separation p).rename Fin.elim0) :=
    .hyp ⟨_, rfl, rfl⟩
  exact induction_on_omega p Fin.castSucc (Fin.last n) (add (add (add hs _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory (assumptions p)) []
      (Translation.sentence (OmegaInductionSyntax.sentence p)) := TheoryTransport.sentence (source_induction p)

theorem source_ZF_induction {n} (p : Formula (n+1)) :
    Derives (Source.SetLanguage.ZF.at 0) (OmegaInductionSyntax.sentence p) := by
  refine Derives.weaken ?_ (source_induction p)
  rintro q ⟨_, rfl, rfl⟩
  exact ⟨_, Source.SetLanguage.IsZFAxiom.separation p, rfl⟩

theorem native_induction {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (OmegaInductionSyntax.sentence p)) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate p)
  rintro q ⟨_, rfl, rfl⟩
  exact SeparationSyntax.source_separation p
end PPAC.Migration.OmegaInduction
