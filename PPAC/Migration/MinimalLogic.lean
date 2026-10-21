import PPAC.Migration.MinimalPredicates

/-! 分离集与原正则极小元之间的实际19规则推导，无模型语义。 -/
namespace PPAC.Migration.MinimalLogic
open Source SourceAlgebra SourceLogic MinimalPredicates
open ReplacementPredicates (paramsUp)

theorem separated_inhabited {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a c : Fin m) (hs : Derives Γ (separated p ρ a c)) (he : Derives Γ (has p ρ a)) :
    Derives Γ (inhabited c) := by
  let X : Formula (m+1) := satisfying p (paramsUp ρ) a.castSucc (Fin.last m)
  let Γx := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at he
  apply Derives.exE (p := X) he
  have hs' : Derives Γx (separated p (paramsUp ρ) a.castSucc c.castSucc) := by
    simpa only [Formula.raise, separated_rename] using under hs X
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  have hmem := Derives.impE (.conjR (specialize_separated p (paramsUp ρ)
    a.castSucc c.castSucc (Fin.last m) hs')) hx
  have hi : Derives Γx (inhabited c.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hmem
  simpa only [Formula.raise, inhabited_rename] using hi

/-- 分离集的正则极小元满足原谓词，而且不存在界内满足者作为其成员。 -/
theorem transfer_minimal {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a c x : Fin m) (hs : Derives Γ (separated p ρ a c)) (hx : Derives Γ (setMinimal c x)) :
    Derives Γ (minimal p ρ a x) := by
  apply Derives.conjI
  · exact .impE (.conjL (specialize_separated p ρ a c x hs)) (.conjL hx)
  · apply Derives.allI
    let Γ' := Context.image Formula.raise Γ
    have hs' : Derives Γ' (separated p (paramsUp ρ) a.castSucc c.castSucc) := by
      simpa only [Formula.raise, separated_rename] using Derives.rename Fin.castSucc hs
    have hx' : Derives Γ' (setMinimal c.castSucc x.castSucc) := by
      simpa only [Formula.raise, setMinimal_rename] using Derives.rename Fin.castSucc hx
    apply Derives.impI
    have hyc : Derives (Context.add (satisfying p (paramsUp ρ) a.castSucc (Fin.last m)) Γ')
        (.mem (Fin.last m) c.castSucc) :=
      .impE (.conjR (add (specialize_separated p (paramsUp ρ) a.castSucc c.castSucc (Fin.last m) hs') _))
        (.hyp (Or.inl rfl))
    apply Derives.impI
    have hn := specialize_setMinimal c.castSucc x.castSucc (Fin.last m) hx'
    exact .impE (.impE (add (add hn _) _) (.hyp (Or.inl rfl))) (add hyc _)

theorem minimal_from_regular {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a c : Fin m) (hs : Derives Γ (separated p ρ a c)) (hr : Derives Γ (regular c)) :
    Derives Γ (minimalExists p ρ a) := by
  let X := setMinimal c.castSucc (Fin.last m)
  let Γx := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at hr
  apply Derives.exE (p := X) hr
  have hs' : Derives Γx (separated p (paramsUp ρ) a.castSucc c.castSucc) := by
    simpa only [Formula.raise, separated_rename] using under hs X
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  have hm := transfer_minimal p (paramsUp ρ) a.castSucc c.castSucc (Fin.last m) hs' hx
  have he : Derives Γx (minimalExists p (paramsUp ρ) a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, minimal_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hm
  simpa only [Formula.raise, minimalExists_rename] using he
end PPAC.Migration.MinimalLogic
