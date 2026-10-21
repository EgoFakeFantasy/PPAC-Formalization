import PPAC.Migration.BoundedMinimal

/-! 任意集合内的成员归纳模式；不冒充无界集合归纳或内部递归定理。 -/
namespace PPAC.Migration.BoundedInduction
open Source SourceAlgebra SourceLogic MinimalPredicates
open ReplacementPredicates (paramsUp)

def below {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp
    ((Formula.mem (Fin.last m) x.castSucc).imp (pred p (paramsUp ρ) (Fin.last m))))

def progressive {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp
    ((below p (paramsUp ρ) a.castSucc (Fin.last m)).imp (pred p (paramsUp ρ) (Fin.last m))))

def holds {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp (pred p (paramsUp ρ) (Fin.last m)))

theorem below_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m) (r : Fin m → Fin k) :
    (below p ρ a x).rename r = below p (fun i => r (ρ i)) (r a) (r x) := by
  simp only [below, Formula.rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (progressive p ρ a).rename r = progressive p (fun i => r (ρ i)) (r a) := by
  simp only [progressive, Formula.rename, below_rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem holds_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (holds p ρ a).rename r = holds p (fun i => r (ρ i)) (r a) := by
  simp only [holds, Formula.rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m)
    (h : Derives Γ (progressive p ρ a)) :
    Derives Γ ((Formula.mem x a).imp ((below p ρ a x).imp (pred p ρ x))) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, below_rename, pred_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

/-- 极小反例的所有界内成员均非反例，再用进步性导出矛盾。 -/
theorem no_minimal_counterexample {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a x : Fin m) (hp : Derives Γ (progressive p ρ a)) (hx : Derives Γ (minimal p.neg ρ a x)) :
    Derives Γ .bot := by
  have hb : Derives Γ (below p ρ a x) := by
    apply Derives.allI
    let Γ' := Context.image Formula.raise Γ
    have hx' : Derives Γ' (minimal p.neg (paramsUp ρ) a.castSucc x.castSucc) := by
      simpa only [Formula.raise, minimal_rename] using Derives.rename Fin.castSucc hx
    apply Derives.impI
    apply Derives.impI
    apply Derives.classical
    have he := specialize_minimal p.neg (paramsUp ρ) a.castSucc x.castSucc (Fin.last m) hx'
    have hy : Derives
        (Context.add (pred p (paramsUp ρ) (Fin.last m)).neg
          (Context.add (.mem (Fin.last m) x.castSucc) (Context.add (.mem (Fin.last m) a.castSucc) Γ')))
        (satisfying p.neg (paramsUp ρ) a.castSucc (Fin.last m)) := by
      apply Derives.conjI
      · exact .hyp (Or.inr (Or.inr (Or.inl rfl)))
      · exact .hyp (Or.inl rfl)
    exact .impE (.impE (add (add (add he _) _) _) hy) (.hyp (Or.inr (Or.inl rfl)))
  have hpx := Derives.impE (.impE (progressive_at p ρ a x hp) (.conjL (.conjL hx))) hb
  exact .impE (.conjR (.conjL hx)) hpx

theorem induction_on_set {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p.neg).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (progressive p ρ a)) : Derives Γ (holds p ρ a) := by
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have hs' : Derives Γ' ((Source.SetLanguage.separation p.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hs
  have hf' : Derives Γ' (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  have hp' : Derives Γ' (progressive p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, progressive_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  apply Derives.classical
  let Δ := Context.add (pred p (paramsUp ρ) (Fin.last m)).neg
    (Context.add (.mem (Fin.last m) a.castSucc) Γ')
  have hex : Derives Δ (has p.neg (paramsUp ρ) a.castSucc) := by
    apply Derives.exI (Fin.last m)
    have hx : Derives Δ (satisfying p.neg (paramsUp ρ) a.castSucc (Fin.last m)) :=
      .conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
    simpa only [Formula.instantiate, satisfying_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  have hm := BoundedMinimal.minimal_exists p.neg (paramsUp ρ) a.castSucc
    (add (add hs' _) _) (add (add hf' _) _) hex
  let X := minimal p.neg (paramsUp (paramsUp ρ)) a.castSucc.castSucc (Fin.last (m+1))
  let Δx := Context.add X (Context.image Formula.raise Δ)
  change Derives Δ (.ex X) at hm
  apply Derives.exE (p := X) hm
  have hp'' : Derives Δx (progressive p (paramsUp (paramsUp ρ)) a.castSucc.castSucc) := by
    simpa only [Formula.raise, progressive_rename] using under (add (add hp' _) _) X
  exact no_minimal_counterexample p (paramsUp (paramsUp ρ)) a.castSucc.castSucc (Fin.last (m+1))
    hp'' (.hyp (Or.inl rfl))

/-- 对每个任意矩阵都构造全参数、全界集合量化的对象句子。 -/
def sentence {n} (p : Formula (n+1)) : Source.Sentence :=
  (Formula.all ((progressive p Fin.castSucc (Fin.last n)).imp
    (holds p Fin.castSucc (Fin.last n)))).close

theorem source_induction {n} (p : Formula (n+1)) :
    Derives ((BoundedMinimal.assumptions p.neg).at 0) (sentence p) := by
  apply close_derives
  apply Derives.allI
  rw [theory_at_raise]
  apply Derives.impI
  have hf : Derives ((BoundedMinimal.assumptions p.neg).at (n+1))
      (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives ((BoundedMinimal.assumptions p.neg).at (n+1))
      ((Source.SetLanguage.separation p.neg).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact induction_on_set p Fin.castSucc (Fin.last n) (add hs _) (add hf _) (.hyp (Or.inl rfl))

theorem kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory (BoundedMinimal.assumptions p.neg)) []
      (Translation.sentence (sentence p)) := TheoryTransport.sentence (source_induction p)

theorem source_ZF_induction {n} (p : Formula (n+1)) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence p) := by
  refine Derives.weaken ?_ (source_induction p)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation p.neg, rfl⟩

theorem native_induction {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate p)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation p.neg
end PPAC.Migration.BoundedInduction
