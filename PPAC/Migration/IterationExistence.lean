import PPAC.Migration.IterationExtensionExistence

/-! 全部内部ω长度的实际有限轨迹存在；不是仅外部标准有限长度的实例。 -/
namespace PPAC.Migration.IterationExistence
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax IterationSyntax FiniteIterationSyntax

def existenceMatrix : Formula 3 := existsTrack 2 0 1

theorem existence_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) :
    MinimalPredicates.pred existenceMatrix ρ x = existsTrack x (ρ 0) (ρ 1) := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, existenceMatrix, existsTrack_rename, h0, h1, h2]

theorem subst_length {m} {Γ : Context m} (n x z a : Fin m)
    (he : Derives Γ (.equal n x)) (hn : Derives Γ (existsTrack n z a)) : Derives Γ (existsTrack x z a) := by
  have hi : Derives Γ ((existsTrack (Fin.last m) z.castSucc a.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, existsTrack_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have h := Derives.eqSubst (existsTrack (Fin.last m) z.castSucc a.castSucc) he hi
  simpa only [Formula.instantiate, existsTrack_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem subst_domain {m} {Γ : Context m} (f d s z a : Fin m)
    (he : Derives Γ (.equal d s)) (hf : Derives Γ (track f d z a)) : Derives Γ (track f s z a) := by
  have hi : Derives Γ ((track f.castSucc (Fin.last m) z.castSucc a.castSucc).instantiate d) := by
    simpa only [Formula.instantiate, track_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  have h := Derives.eqSubst (track f.castSucc (Fin.last m) z.castSucc a.castSucc) he hi
  simpa only [Formula.instantiate, track_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem at_zero {m} {Γ : Context m} (x z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hx : Derives Γ (empty x)) : Derives Γ (existsTrack x z a) :=
  subst_length z x z a (OmegaUniversal.empty_unique z x he hz hx) (IterationBaseExistence.exists_base z a hp he hz)

theorem eliminate_track {m} {Γ : Context m} (n z a : Fin m) (q : Formula m)
    (h : Derives Γ (existsTrack n z a))
    (hc : Derives (Context.add (witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE h
  apply Derives.exE (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨t, ht, het⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨t, Or.inr ht, het⟩

theorem step_from_exists {m} {Γ : Context m} (n s z a w : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfound : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem n w)) (hs : Derives Γ (successor s n))
    (hold : Derives Γ (existsTrack n z a)) : Derives Γ (existsTrack s z a) := by
  have htn := OmegaStructureAlgebra.element_transitive_at w n (OmegaStructureInduction.elements_transitive w hsep hw) hx
  have hts := OmegaElementary.successor_transitive s n hs htn
  have hnon := ObjectIrreflexivity.no_self_member n hfound hp
  have hnos := ObjectIrreflexivity.no_self_member s hfound hp
  let B := witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_track n z a _ hold
  have hpB : Derives Γb (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hp B
  have huB : Derives Γb (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hu B
  have heB : Derives Γb (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two he B
  have htnB : Derives Γb (transitive n.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using OrderedPairElimination.under_two htn B
  have htsB : Derives Γb (transitive s.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using OrderedPairElimination.under_two hts B
  have hnonB : Derives Γb ((Formula.mem n.castSucc.castSucc n.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using OrderedPairElimination.under_two hnon B
  have hnosB : Derives Γb ((Formula.mem s.castSucc.castSucc s.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using OrderedPairElimination.under_two hnos B
  have hsB : Derives Γb (successor s.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hs B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hds := OmegaUniversal.successor_unique (Fin.last m).castSucc s.castSucc.castSucc n.castSucc.castSucc heB (.conjL hB) hsB
  have htrack := subst_domain (Fin.last (m+1)) (Fin.last m).castSucc s.castSucc.castSucc
    z.castSucc.castSucc a.castSucc.castSucc hds (.conjR hB)
  have hr := IterationExtensionExistence.exists_successor (Fin.last (m+1)) n.castSucc.castSucc s.castSucc.castSucc
    z.castSucc.castSucc a.castSucc.castSucc hpB huB heB htrack htnB htsB hnonB hnosB hsB
  simpa only [Formula.raise, existsTrack_rename] using hr

theorem induction_base {m} {Γ : Context m} (z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hz : Derives Γ (empty z)) :
    Derives Γ (OmegaInductionSyntax.base existenceMatrix (Source.SetLanguage.args2 z a)) := by
  simp only [OmegaInductionSyntax.base, existence_pred, ReplacementPredicates.paramsUp]
  change Derives Γ (.all ((empty (Fin.last m)).imp (existsTrack (Fin.last m) z.castSucc a.castSucc)))
  apply Derives.allI
  have hp' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hp
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact at_zero (Fin.last m) z.castSucc a.castSucc (add hp' _) (add he' _) (add hz' _) (.hyp (Or.inl rfl))

theorem induction_step {m} {Γ : Context m} (z a w : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfound : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.step existenceMatrix (Source.SetLanguage.args2 z a) w) := by
  simp only [OmegaInductionSyntax.step, existence_pred, ReplacementPredicates.paramsUp]
  change Derives Γ (.all (.all ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).imp
    ((existsTrack (Fin.last m).castSucc z.castSucc.castSucc a.castSucc.castSucc).imp
      ((successor (Fin.last (m+1)) (Fin.last m).castSucc).imp
        (existsTrack (Fin.last (m+1)) z.castSucc.castSucc a.castSucc.castSucc))))))
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hp' : Derives Δ (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  have hu' : Derives Δ (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hu)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hfound' : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hfound)
  have hsep' : Derives Δ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hsep)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_from_exists (Fin.last m).castSucc (Fin.last (m+1)) z.castSucc.castSucc a.castSucc.castSucc w.castSucc.castSucc
    (add (add (add hp' _) _) _) (add (add (add hu' _) _) _) (add (add (add he' _) _) _)
    (add (add (add hfound' _) _) _) (add (add (add hsep' _) _) _) (add (add (add hw' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_exists {m} {Γ : Context m} (z a w : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfound : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0))
    (hexsep : Derives Γ ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (existsTrack (Fin.last m) z.castSucc a.castSucc))) := by
  have hi := OmegaInduction.induction_on_omega existenceMatrix (Source.SetLanguage.args2 z a) w hexsep hw
    (induction_base z a hp he hz) (induction_step z a w hp hu he hfound hsep hw)
  simpa only [OmegaInductionSyntax.holds, existence_pred, ReplacementPredicates.paramsUp,
    PairSyntax.args2_first, PairSyntax.args2_second] using hi
end PPAC.Migration.IterationExistence
