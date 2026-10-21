import PPAC.Migration.GlobalMinimalSyntax

/-! 非空任意可定义性质具有成员极小元，使用对象全体集合归纳而非宿主良基性。 -/
namespace PPAC.Migration.GlobalMinimal
open Source SourceAlgebra SourceLogic GlobalMinimalSyntax
open MinimalPredicates (pred pred_rename)
open ReplacementPredicates (paramsUp)

theorem progressive_negation {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (hno : Derives Γ (minimalExists p ρ).neg) : Derives Γ (SetInductionSyntax.progressive p.neg ρ) := by
  apply Derives.allI
  have hno' : Derives (Context.image Formula.raise Γ) (minimalExists p (paramsUp ρ)).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, minimalExists_rename] using Derives.rename Fin.castSucc hno
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (pred p (paramsUp ρ) (Fin.last m))
    (Context.add (SetInductionSyntax.below p.neg (paramsUp ρ) (Fin.last m)) (Context.image Formula.raise Γ))
  have hm : Derives Δ (minimal p (paramsUp ρ) (Fin.last m)) :=
    .conjI (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))
  have he : Derives Δ (minimalExists p (paramsUp ρ)) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, minimal_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hm
  exact .impE (add (add hno' _) _) he

theorem minimal_exists {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p.neg.neg).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hc : Derives Γ (ObjectTransitiveCover.coverSentence.rename Fin.elim0))
    (hh : Derives Γ (has p ρ)) : Derives Γ (minimalExists p ρ) := by
  apply Derives.classical
  let Δ := Context.add (minimalExists p ρ).neg Γ
  have hno : Derives Δ (minimalExists p ρ).neg := .hyp (Or.inl rfl)
  have hp := progressive_negation p ρ hno
  have hall := SetInduction.all_holds p.neg ρ (add hs _) (add hf _) (add hc _) hp
  have hh' : Derives Δ (has p ρ) := add hh _
  let X := pred p (paramsUp ρ) (Fin.last m)
  let Γx := Context.add X (Context.image Formula.raise Δ)
  change Derives Δ (.ex X) at hh'
  apply Derives.exE (p := X) hh'
  have hallX : Derives Γx (SetInductionSyntax.holds p.neg (paramsUp ρ)) := by
    simpa only [Formula.raise, SetInductionSyntax.holds_rename] using under hall X
  exact .impE (SetInductionSyntax.holds_at p.neg (paramsUp ρ) (Fin.last m) hallX) (.hyp (Or.inl rfl))

theorem source_minimal {n} (p : Formula (n+1)) : Derives (Source.SetLanguage.ZF.at 0) (sentence p) := by
  apply close_derives
  apply Derives.impI
  have hs : Derives (Source.SetLanguage.ZF.at n) ((Source.SetLanguage.separation p.neg.neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation p.neg.neg, rfl⟩
  have hf : Derives (Source.SetLanguage.ZF.at n) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  have hc := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover n
  exact minimal_exists p id (add hs _) (add hf _) (add hc _) (.hyp (Or.inl rfl))

theorem kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (sentence p)) := TheoryTransport.sentence (source_minimal p)

theorem native_minimal {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) :=
  ZFReplay.replay (kernel_certificate p)
end PPAC.Migration.GlobalMinimal
