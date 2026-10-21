import PPAC.Migration.OrdinalLeastSyntax

/-! 成员极小的序数性质见证在所有内部候选序数中最小，且该最小序数唯一。 -/
namespace PPAC.Migration.OrdinalLeastLogic
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalLeastSyntax
open MinimalPredicates (pred pred_neg)
open ReplacementPredicates (paramsUp)

theorem least_of_minimal {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hm : Derives Γ (GlobalMinimalSyntax.minimal (matrix p) ρ a)) : Derives Γ (least p ρ a) := by
  have hp : Derives Γ (property p ρ a) := by
    simpa only [matrix_pred] using Derives.conjL hm
  apply Derives.conjI hp
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  have hs' : Derives Δ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hs
  have hm' : Derives Δ (GlobalMinimalSyntax.minimal (matrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, GlobalMinimalSyntax.minimal_rename] using Derives.rename Fin.castSucc hm
  have hp' : Derives Δ (property p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, property_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  let P := property p (paramsUp ρ) (Fin.last m)
  let Ξ := Context.add P Δ
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hc := OrdinalComparison.compare a.castSucc (Fin.last m) (add he' P) (add hf' P) (add hs' P)
    (.conjL (add hp' P)) (.conjL hP)
  have hbelow : Derives Ξ ((Formula.mem (Fin.last m) a.castSucc).imp
      (property p (paramsUp ρ) (Fin.last m)).neg) := by
    simpa only [pred_neg, matrix_pred] using
      SetInductionSyntax.below_at (matrix p).neg (paramsUp ρ) a.castSucc (Fin.last m) (.conjR (add hm' P))
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (Derives.hyp (Or.inl rfl))
    · exact .disjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.impE (add (add hbelow _) _) (.hyp (Or.inl rfl))) (add (add hP _) _))

theorem least_values_equal {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a b : Fin m)
    (ha : Derives Γ (least p ρ a)) (hb : Derives Γ (least p ρ b)) : Derives Γ (.equal a b) := by
  have hc := Derives.impE (least_at p ρ a b ha) (.conjL hb)
  have hd := Derives.impE (least_at p ρ b a hb) (.conjL ha)
  apply Derives.disjE hc
  · exact .hyp (Or.inl rfl)
  · apply Derives.disjE (add hd _)
    · exact eq_symm (.hyp (Or.inl rfl))
    · have hab : Derives (Context.add (.mem b a) (Context.add (.mem a b) Γ)) (.mem a b) := .hyp (Or.inr (Or.inl rfl))
      exact .botE (.impE (OrdinalComparison.asymmetric a b (.conjL (.conjL (add (add ha _) _))) hab) (.hyp (Or.inl rfl)))

theorem unique_formula {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (ha : Derives Γ (least p ρ a)) : Derives Γ (uniqueLeast p ρ a) := by
  apply Derives.allI
  have ha' : Derives (Context.image Formula.raise Γ) (least p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, least_rename] using Derives.rename Fin.castSucc ha
  apply Derives.impI
  exact least_values_equal p (paramsUp ρ) (Fin.last m) a.castSucc (.hyp (Or.inl rfl)) (add ha' _)

theorem fiber_of_exists {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (hx : Derives Γ (leastExists p ρ)) : Derives Γ (fiber p ρ) := by
  let A := least p (paramsUp ρ) (Fin.last m)
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hx
  apply Derives.exE (p := A) hx
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hu := unique_formula p (paramsUp ρ) (Fin.last m) hA
  have hout : Derives Ξ (fiber p (paramsUp ρ)) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, least_rename, uniqueLeast_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hA hu
  simpa only [Formula.raise, fiber_rename] using hout
theorem least_subset {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a b : Fin m)
    (ha : Derives Γ (least p ρ a)) (hb : Derives Γ (property p ρ b)) :
    Derives Γ (RestrictionSyntax.subset a b) := by
  have hc := Derives.impE (least_at p ρ a b ha) hb
  apply Derives.disjE hc
  · apply Derives.allI
    have he0 : Derives (Context.add (.equal a b) Γ) (.equal a b) := .hyp (Or.inl rfl)
    have he : Derives (Context.image Formula.raise (Context.add (.equal a b) Γ)) (.equal a.castSucc b.castSucc) :=
      Derives.rename Fin.castSucc he0
    apply Derives.impI
    exact UnorderedPairLogic.mem_container_subst a.castSucc b.castSucc (Fin.last m) (add he _) (.hyp (Or.inl rfl))
  · exact OrdinalTransitivity.subset_of_member b a (.conjL (.conjL (add hb _))) (.hyp (Or.inl rfl))
end PPAC.Migration.OrdinalLeastLogic
