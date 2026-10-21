import PPAC.Migration.OmegaUniversal

/-! 在一个实际归纳集中分离“属于每个归纳集”的对象，得到最小归纳集。 -/
namespace PPAC.Migration.OmegaCut
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaUniversal

theorem zero_cut {m} {Γ : Context m} (w i : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (isInductive i)) (hc : Derives Γ (cut w i)) : Derives Γ (zeroIn w) := by
  have hz := Derives.conjL hi
  let Z := (Formula.mem (Fin.last m) i.castSucc).conj (empty (Fin.last m))
  let Γz := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have heZ : Derives Γz (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Z
  have hcZ : Derives Γz (cut w.castSucc i.castSucc) := by
    simpa only [Formula.raise, cut_rename] using under hc Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have hu := empty_universal (Fin.last m) heZ (.conjR hZ)
  have hw := Derives.impE (.conjR (cut_at w.castSucc i.castSucc (Fin.last m) hcZ)) (.conjI (.conjL hZ) hu)
  have hr : Derives Γz (zeroIn w.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, empty_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hw (Derives.conjR hZ)
  simpa only [Formula.raise, zeroIn_rename] using hr

theorem step_cut {m} {Γ : Context m} (w i x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (isInductive i)) (hc : Derives Γ (cut w i)) (hx : Derives Γ (.mem x w)) :
    Derives Γ (stepIn w x) := by
  have hix := Derives.impE (.conjL (cut_at w i x hc)) hx
  have ht := Derives.impE (step_at i x hi) (.conjL hix)
  let T := (Formula.mem (Fin.last m) i.castSucc).conj (successor (Fin.last m) x.castSucc)
  let Γt := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have heT : Derives Γt (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he T
  have hcT : Derives Γt (cut w.castSucc i.castSucc) := by
    simpa only [Formula.raise, cut_rename] using under hc T
  have hxT : Derives Γt (universal x.castSucc) := by
    simpa only [Formula.raise, universal_rename] using under (Derives.conjR hix) T
  have hT : Derives Γt T := .hyp (Or.inl rfl)
  have hu := successor_universal (Fin.last m) x.castSucc heT (.conjR hT) hxT
  have hw := Derives.impE (.conjR (cut_at w.castSucc i.castSucc (Fin.last m) hcT)) (.conjI (.conjL hT) hu)
  have hr : Derives Γt (stepIn w.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, successor_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hw (Derives.conjR hT)
  simpa only [Formula.raise, stepIn_rename] using hr

theorem cut_is_inductive {m} {Γ : Context m} (w i : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (isInductive i)) (hc : Derives Γ (cut w i)) : Derives Γ (isInductive w) := by
  apply Derives.conjI (zero_cut w i he hi hc)
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hi' : Derives (Context.image Formula.raise Γ) (isInductive i.castSucc) := by
    simpa only [Formula.raise, isInductive_rename] using Derives.rename Fin.castSucc hi
  have hc' : Derives (Context.image Formula.raise Γ) (cut w.castSucc i.castSucc) := by
    simpa only [Formula.raise, cut_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  exact step_cut w.castSucc i.castSucc (Fin.last m) (add he' _) (add hi' _) (add hc' _) (.hyp (Or.inl rfl))

theorem cut_member {m} {Γ : Context m} (w i x j : Fin m)
    (hc : Derives Γ (cut w i)) (hj : Derives Γ (isInductive j)) (hx : Derives Γ (.mem x w)) :
    Derives Γ (.mem x j) :=
  .impE (universal_at x j (.conjR (.impE (.conjL (cut_at w i x hc)) hx))) hj

theorem cut_subset {m} {Γ : Context m} (w i j : Fin m)
    (hc : Derives Γ (cut w i)) (hj : Derives Γ (isInductive j)) : Derives Γ (RestrictionSyntax.subset w j) := by
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (cut w.castSucc i.castSucc) := by
    simpa only [Formula.raise, cut_rename] using Derives.rename Fin.castSucc hc
  have hj' : Derives (Context.image Formula.raise Γ) (isInductive j.castSucc) := by
    simpa only [Formula.raise, isInductive_rename] using Derives.rename Fin.castSucc hj
  apply Derives.impI
  exact cut_member w.castSucc i.castSucc (Fin.last m) j.castSucc (add hc' _) (add hj' _) (.hyp (Or.inl rfl))

theorem from_cut {m} {Γ : Context m} (w i : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (isInductive i)) (hc : Derives Γ (cut w i)) : Derives Γ (omega w) := by
  apply Derives.conjI (cut_is_inductive w i he hi hc)
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (cut w.castSucc i.castSucc) := by
    simpa only [Formula.raise, cut_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  exact cut_subset w.castSucc i.castSucc (Fin.last m) (add hc' _) (.hyp (Or.inl rfl))
end PPAC.Migration.OmegaCut
