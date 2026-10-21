import PPAC.Migration.SetInductionSyntax

/-! 传递覆盖把集合内归纳提升为全体集合归纳，始终返回原规则推导。 -/
namespace PPAC.Migration.SetInductionLogic
open Source SourceAlgebra SourceLogic MinimalPredicates SetInductionSyntax OmegaStructureSyntax RestrictionSyntax TransitiveCoverSyntax
open ReplacementPredicates (paramsUp)

theorem bounded_below_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (b x y : Fin m)
    (h : Derives Γ (BoundedInduction.below p ρ b x)) :
    Derives Γ ((Formula.mem y b).imp ((Formula.mem y x).imp (pred p ρ y))) := by
  have hi := Derives.allE y h
  simpa only [Formula.instantiate, Formula.rename, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem bounded_holds_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (b x : Fin m)
    (h : Derives Γ (BoundedInduction.holds p ρ b)) : Derives Γ ((Formula.mem x b).imp (pred p ρ x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem below_on_transitive {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (b x : Fin m)
    (ht : Derives Γ (transitive b)) (hx : Derives Γ (.mem x b))
    (hb : Derives Γ (BoundedInduction.below p ρ b x)) : Derives Γ (below p ρ x) := by
  have hs := Derives.impE (transitive_at b x ht) hx
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (subset x.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hb' : Derives (Context.image Formula.raise Γ) (BoundedInduction.below p (paramsUp ρ) b.castSucc x.castSucc) := by
    simpa only [Formula.raise, BoundedInduction.below_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  have hyb : Derives (Context.add (.mem (Fin.last m) x.castSucc) (Context.image Formula.raise Γ)) (.mem (Fin.last m) b.castSucc) :=
    .impE (add (subset_at x.castSucc b.castSucc (Fin.last m) hs') _) (.hyp (Or.inl rfl))
  exact .impE (.impE (add (bounded_below_at p (paramsUp ρ) b.castSucc x.castSucc (Fin.last m) hb') _) hyb) (.hyp (Or.inl rfl))

theorem bounded_progressive {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (b : Fin m)
    (ht : Derives Γ (transitive b)) (hp : Derives Γ (progressive p ρ)) : Derives Γ (BoundedInduction.progressive p ρ b) := by
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise Γ) (transitive b.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using Derives.rename Fin.castSucc ht
  have hp' : Derives (Context.image Formula.raise Γ) (progressive p (paramsUp ρ)) := by
    simpa only [Formula.raise, progressive_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  apply Derives.impI
  exact .impE (add (add (progressive_at p (paramsUp ρ) (Fin.last m) hp') _) _)
    (below_on_transitive p (paramsUp ρ) b.castSucc (Fin.last m) (add (add ht' _) _)
      (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))

theorem below_from_cover {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (b a : Fin m)
    (hs : Derives Γ (subset a b)) (hh : Derives Γ (BoundedInduction.holds p ρ b)) : Derives Γ (below p ρ a) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (subset a.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hh' : Derives (Context.image Formula.raise Γ) (BoundedInduction.holds p (paramsUp ρ) b.castSucc) := by
    simpa only [Formula.raise, BoundedInduction.holds_rename] using Derives.rename Fin.castSucc hh
  apply Derives.impI
  exact .impE (add (bounded_holds_at p (paramsUp ρ) b.castSucc (Fin.last m) hh') _)
    (.impE (add (subset_at a.castSucc b.castSucc (Fin.last m) hs') _) (.hyp (Or.inl rfl)))

theorem at_element {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p.neg).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hc : Derives Γ (coverExists a)) (hp : Derives Γ (progressive p ρ)) : Derives Γ (pred p ρ a) := by
  let B := cover (Fin.last m) a.castSucc
  let Γb := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hc
  apply Derives.exE (p := B) hc
  have hsB : Derives Γb ((Source.SetLanguage.separation p.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs B
  have hfB : Derives Γb (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf B
  have hpB : Derives Γb (progressive p (paramsUp ρ)) := by
    simpa only [Formula.raise, progressive_rename] using under hp B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hh := BoundedInduction.induction_on_set p (paramsUp ρ) (Fin.last m) hsB hfB
    (bounded_progressive p (paramsUp ρ) (Fin.last m) (.conjR hB) hpB)
  have hb := below_from_cover p (paramsUp ρ) (Fin.last m) a.castSucc (.conjL hB) hh
  have hr := Derives.impE (progressive_at p (paramsUp ρ) a.castSucc hpB) hb
  simpa only [Formula.raise, pred_rename] using hr
end PPAC.Migration.SetInductionLogic
