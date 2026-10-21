import PPAC.Migration.SetInductionLogic

/-! 每个任意参数公式的无界集合归纳闭句，在源ZF及原YesMetaZFC核中推导。 -/
namespace PPAC.Migration.SetInduction
open Source SourceAlgebra SourceLogic MinimalPredicates SetInductionSyntax TransitiveCoverSyntax
open ReplacementPredicates (paramsUp)

theorem all_holds {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p.neg).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hc : Derives Γ (ObjectTransitiveCover.coverSentence.rename Fin.elim0))
    (hp : Derives Γ (progressive p ρ)) : Derives Γ (holds p ρ) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) ((Source.SetLanguage.separation p.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hs
  have hf' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  have hc' : Derives (Context.image Formula.raise Γ) (ObjectTransitiveCover.coverSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hp' : Derives (Context.image Formula.raise Γ) (progressive p (paramsUp ρ)) := by
    simpa only [Formula.raise, progressive_rename] using Derives.rename Fin.castSucc hp
  have hcov : Derives (Context.image Formula.raise Γ) (coverExists (Fin.last m)) := by
    have hi := specialize_close (coverExists (0 : Fin 1)) (fun _ => Fin.last m) hc'
    simpa only [coverExists_rename] using hi
  exact SetInductionLogic.at_element p (paramsUp ρ) (Fin.last m) hs' hf' hcov hp'

theorem source_induction {n} (p : Formula (n+1)) : Derives (Source.SetLanguage.ZF.at 0) (sentence p) := by
  apply close_derives
  apply Derives.impI
  have hs : Derives (Source.SetLanguage.ZF.at n) ((Source.SetLanguage.separation p.neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation p.neg, rfl⟩
  have hf : Derives (Source.SetLanguage.ZF.at n) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  have hc := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover n
  exact all_holds p id (add hs _) (add hf _) (add hc _) (.hyp (Or.inl rfl))

theorem kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (sentence p)) := TheoryTransport.sentence (source_induction p)

theorem native_induction {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) :=
  ZFReplay.replay (kernel_certificate p)
end PPAC.Migration.SetInduction
