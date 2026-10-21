import PPAC.Migration.OmegaInductionSyntax

/-! 归纳公式的分离结果包含空元并对后继封闭，完全在对象演算内。 -/
namespace PPAC.Migration.OmegaInductionCut
open Source SourceAlgebra SourceLogic OmegaSyntax MinimalPredicates OmegaInductionSyntax
open ReplacementPredicates (paramsUp)

theorem filtered_zero {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w s : Fin m)
    (hw : Derives Γ (isInductive w)) (hs : Derives Γ (separated p ρ w s)) (hb : Derives Γ (base p ρ)) :
    Derives Γ (zeroIn s) := by
  have hz := Derives.conjL hw
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Γz := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hsZ : Derives Γz (separated p (paramsUp ρ) w.castSucc s.castSucc) := by
    simpa only [Formula.raise, separated_rename] using under hs Z
  have hbZ : Derives Γz (base p (paramsUp ρ)) := by
    simpa only [Formula.raise, base_rename] using under hb Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have hp := Derives.impE (base_at p (paramsUp ρ) (Fin.last m) hbZ) (.conjR hZ)
  have hm := Derives.impE (.conjR (specialize_separated p (paramsUp ρ) w.castSucc s.castSucc (Fin.last m) hsZ))
    (.conjI (.conjL hZ) hp)
  have hr : Derives Γz (zeroIn s.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, empty_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hm (Derives.conjR hZ)
  simpa only [Formula.raise, zeroIn_rename] using hr

theorem filtered_step {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w s x : Fin m)
    (hw : Derives Γ (isInductive w)) (hs : Derives Γ (separated p ρ w s))
    (ht : Derives Γ (step p ρ w)) (hx : Derives Γ (.mem x s)) : Derives Γ (stepIn s x) := by
  have hxp := Derives.impE (.conjL (specialize_separated p ρ w s x hs)) hx
  have he := Derives.impE (OmegaSyntax.step_at w x hw) (.conjL hxp)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) x.castSucc)
  let Γt := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at he
  apply Derives.exE (p := T) he
  have hsT : Derives Γt (separated p (paramsUp ρ) w.castSucc s.castSucc) := by
    simpa only [Formula.raise, separated_rename] using under hs T
  have htT : Derives Γt (step p (paramsUp ρ) w.castSucc) := by
    simpa only [Formula.raise, step_rename] using under ht T
  have hxT : Derives Γt (.mem x.castSucc w.castSucc) := under (Derives.conjL hxp) T
  have hpT : Derives Γt (pred p (paramsUp ρ) x.castSucc) := by
    simpa only [Formula.raise, pred_rename] using under (Derives.conjR hxp) T
  have hT : Derives Γt T := .hyp (Or.inl rfl)
  have hpNew := Derives.impE (.impE (.impE (OmegaInductionSyntax.step_at p (paramsUp ρ) w.castSucc x.castSucc (Fin.last m) htT)
    hxT) hpT) (.conjR hT)
  have hm := Derives.impE (.conjR (specialize_separated p (paramsUp ρ) w.castSucc s.castSucc (Fin.last m) hsT))
    (.conjI (.conjL hT) hpNew)
  have hr : Derives Γt (stepIn s.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, successor_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hm (Derives.conjR hT)
  simpa only [Formula.raise, stepIn_rename] using hr

theorem filtered_inductive {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w s : Fin m)
    (hw : Derives Γ (isInductive w)) (hs : Derives Γ (separated p ρ w s))
    (hb : Derives Γ (base p ρ)) (ht : Derives Γ (step p ρ w)) : Derives Γ (isInductive s) := by
  apply Derives.conjI (filtered_zero p ρ w s hw hs hb)
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (isInductive w.castSucc) := by
    simpa only [Formula.raise, isInductive_rename] using Derives.rename Fin.castSucc hw
  have hs' : Derives (Context.image Formula.raise Γ) (separated p (paramsUp ρ) w.castSucc s.castSucc) := by
    simpa only [Formula.raise, separated_rename] using Derives.rename Fin.castSucc hs
  have ht' : Derives (Context.image Formula.raise Γ) (step p (paramsUp ρ) w.castSucc) := by
    simpa only [Formula.raise, step_rename] using Derives.rename Fin.castSucc ht
  apply Derives.impI
  exact filtered_step p (paramsUp ρ) w.castSucc s.castSucc (Fin.last m) (add hw' _) (add hs' _) (add ht' _) (.hyp (Or.inl rfl))

theorem holds_from_separated {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w s : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (separated p ρ w s))
    (hb : Derives Γ (base p ρ)) (ht : Derives Γ (step p ρ w)) : Derives Γ (holds p ρ w) := by
  have hi := filtered_inductive p ρ w s (.conjL hw) hs hb ht
  have hsub := Derives.impE (omega_at w s hw) hi
  apply Derives.allI
  have hsub' : Derives (Context.image Formula.raise Γ) (RestrictionSyntax.subset w.castSucc s.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.subset_rename] using Derives.rename Fin.castSucc hsub
  have hs' : Derives (Context.image Formula.raise Γ) (separated p (paramsUp ρ) w.castSucc s.castSucc) := by
    simpa only [Formula.raise, separated_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  have hm := Derives.impE (RestrictionSyntax.subset_at w.castSucc s.castSucc (Fin.last m) (add hsub' M)) (.hyp (Or.inl rfl))
  exact .conjR (.impE (.conjL (specialize_separated p (paramsUp ρ) w.castSucc s.castSucc (Fin.last m) (add hs' M))) hm)
end PPAC.Migration.OmegaInductionCut
