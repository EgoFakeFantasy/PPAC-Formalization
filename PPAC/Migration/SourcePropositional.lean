import PPAC.Migration.SourceLogic

/-! 原27逻辑模式的命题部分，仅由原19源规则派生。 -/
namespace PPAC.Migration.SourcePropositional
open Source SourceLogic
variable {n : Nat} {Γ : Context n}

theorem imp_distribution (p q r : Formula n) :
    Derives Γ ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact .impE (p := q)
    (.impE (p := p) (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add])))
    (.impE (p := p) (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add])))

theorem self_implication (p : Formula n) : Derives Γ (p.imp (p.imp p)) :=
  .impI (.impI (.hyp (Or.inl rfl)))

theorem weakening (p q : Formula n) : Derives Γ (p.imp (q.imp p)) :=
  .impI (.impI (.hyp (Or.inr (Or.inl rfl))))

theorem contradiction (p q : Formula n) : Derives Γ (p.imp (p.neg.imp q)) :=
  .impI (.impI (.botE (.impE (p := p) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl))))))

theorem classical (p : Formula n) : Derives Γ ((p.neg.imp p).imp p) := by
  apply Derives.impI
  apply Derives.classical
  exact .impE (p := p) (.hyp (Or.inl rfl))
    (.impE (p := p.neg) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))

theorem explosion (p q : Formula n) : Derives Γ (p.neg.imp (p.imp q)) :=
  .impI (.impI (.botE (.impE (p := p) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))))

theorem by_cases (p q : Formula n) (hp : Derives (Context.add p Γ) q)
    (hn : Derives (Context.add p.neg Γ) q) : Derives Γ q := by
  have hpq : Derives Γ (p.imp q) := .impI hp
  have hnq : Derives Γ (p.neg.imp q) := .impI hn
  apply Derives.classical
  have hnp : Derives (Context.add q.neg Γ) p.neg := by
    apply Derives.impI
    exact .impE (p := q) (.hyp (Or.inr (Or.inl rfl)))
      (.impE (p := p) (add (add hpq _) _) (.hyp (Or.inl rfl)))
  exact .impE (p := q) (.hyp (Or.inl rfl)) (.impE (add hnq _) hnp)

theorem case_analysis (p q : Formula n) : Derives Γ ((p.imp q).imp ((p.neg.imp q).imp q)) := by
  apply Derives.impI
  apply Derives.impI
  apply by_cases p q
  · exact .impE (p := p) (.hyp (by simp [Context.add])) (.hyp (Or.inl rfl))
  · exact .impE (p := p.neg) (.hyp (by simp [Context.add])) (.hyp (Or.inl rfl))

theorem truth_intro : Derives Γ ((Formula.bot : Formula n).imp .bot) := .impI (.hyp (Or.inl rfl))

theorem falsum_elimination (p : Formula n) : Derives Γ (Formula.bot.imp p) :=
  .impI (.botE (.hyp (Or.inl rfl)))

theorem negation_intro (p : Formula n) : Derives Γ (p.neg.imp p.neg) := .impI (.hyp (Or.inl rfl))

theorem negation_elimination (p : Formula n) : Derives Γ (p.imp (p.neg.imp .bot)) :=
  .impI (.impI (.impE (p := p) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))))

theorem conjunction_intro (p q : Formula n) : Derives Γ (p.imp (q.imp (p.conj q))) :=
  .impI (.impI (.conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))))

theorem conjunction_elim_left (p q : Formula n) : Derives Γ ((p.conj q).imp p) :=
  .impI (.conjL (.hyp (Or.inl rfl)))

theorem conjunction_elim_right (p q : Formula n) : Derives Γ ((p.conj q).imp q) :=
  .impI (.conjR (.hyp (Or.inl rfl)))

theorem disjunction_intro_left (p q : Formula n) : Derives Γ (p.imp (p.disj q)) :=
  .impI (.disjL (.hyp (Or.inl rfl)))

theorem disjunction_intro_right (p q : Formula n) : Derives Γ (q.imp (p.disj q)) :=
  .impI (.disjR (.hyp (Or.inl rfl)))

theorem disjunction_elimination (p q r : Formula n) :
    Derives Γ ((p.imp r).imp ((q.imp r).imp ((p.disj q).imp r))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.disjE (.hyp (Or.inl rfl))
  · exact .impE (p := p) (.hyp (by simp [Context.add])) (.hyp (Or.inl rfl))
  · exact .impE (p := q) (.hyp (by simp [Context.add])) (.hyp (Or.inl rfl))
end PPAC.Migration.SourcePropositional
