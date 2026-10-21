import PPAC.Migration.Internal.NaturalRecursionLaws

/-! 真实后继关系实际满足总单值义务；全部内部自然索引上的后继迭代已有唯一真实末值。 -/
namespace PPAC.Migration.Internal.SuccessorRecursion
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def stepMatrix : Formula 2 := successor 1 0

theorem empty_parameters {m} (ρ : Fin 0 → Fin m) : ρ = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem step_rel {m} (ρ : Fin 0 → Fin m) (x y : Fin m) : rel stepMatrix ρ x y = successor y x := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 2) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 0).castSucc = x
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 2) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 1) = y
    exact Fin.lastCases_last
  simp only [rel, Source.SetLanguage.relation, stepMatrix, successor_rename, h0, h1]

theorem total {m} {Γ : Context m} (ρ : Fin 0 → Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0)) : Derives Γ (relationTotal stepMatrix ρ) := by
  simp only [relationTotal, step_rel]
  apply Derives.allI
  have hp' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hp
  have hu' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hu
  simpa only [successor, InsertSyntax.insertExists] using InsertExistence.exists_insert (Fin.last m) (Fin.last m) hp' hu'

theorem functional {m} {Γ : Context m} (ρ : Fin 0 → Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) : Derives Γ (relationFunctional stepMatrix ρ) := by
  simp only [relationFunctional, step_rel]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
      (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrdinalRestriction.raise_three he
  apply Derives.impI
  apply Derives.impI
  exact OmegaUniversal.successor_unique (Fin.last (m+1)).castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc
    (add (add he' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def sentence : Source.Sentence := ((omega (0 : Fin 2)).imp (.all
  ((Formula.mem (Fin.last 2) (0 : Fin 2).castSucc).imp (uniqueValue stepMatrix Fin.elim0 (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2))))).close

def zeroSentence : Source.Sentence := ((empty (2 : Fin 4)).imp
  ((evaluation stepMatrix Fin.elim0 0 1 2 3).imp (.equal 3 1))).close

theorem source_proof : Derives (Source.SetLanguage.ZF.at 0) sentence := by
  apply close_derives
  apply Derives.impI
  let Δ := Context.add (omega (0 : Fin 2)) (Source.SetLanguage.ZF.at 2)
  have hw : Derives Δ (omega (0 : Fin 2)) := .hyp (Or.inl rfl)
  have hA := SequenceContext.add (SequenceContext.source_ZF 2) (omega (0 : Fin 2))
  have ht := total (Fin.elim0 : Fin 0 → Fin 2) hA.pairing hA.union
  have hf := functional (Fin.elim0 : Fin 0 → Fin 2) hA.extensionality
  have hc : Derives Δ ((NaturalRecursion.uniquenessSentence stepMatrix).rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at (NaturalRecursion.source_uniqueness stepMatrix) 2) _
  have hall := ObjectNaturalRecursion.instantiate_unique stepMatrix Fin.elim0 0 1 hc hw ht hf
  have hs : Derives Δ ((Source.SetLanguage.separation OmegaOrdinals.matrix).rename Fin.elim0) :=
    add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaOrdinals.matrix, rfl⟩) _
  have hord := OmegaOrdinals.elements 0 hA.foundation hs hw
  apply Derives.allI
  let Δr := Context.image Formula.raise Δ
  have he' : Derives Δr (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hA.extensionality
  have hw' : Derives Δr (omega (0 : Fin 2).castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hord' : Derives Δr (.all ((Formula.mem (Fin.last 3) (0 : Fin 2).castSucc.castSucc).imp (ordinal (Fin.last 3)))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using Derives.rename Fin.castSucc hord
  have hall' : Derives Δr (OrdinalRecursionExistenceSyntax.allUnique (matrix stepMatrix) (extend (Fin.elim0 : Fin 0 → Fin 3) (0 : Fin 2).castSucc (1 : Fin 2).castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, empty_parameters] using Derives.rename Fin.castSucc hall
  apply Derives.impI
  exact NaturalEvaluationFiber.at_natural stepMatrix Fin.elim0 (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)
    (add he' _) (add hw' _) (.hyp (Or.inl rfl)) (add hord' _) (add hall' _)

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact NaturalRecursionLaws.evaluation_zero stepMatrix Fin.elim0 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence sentence) := TheoryTransport.sentence source_proof

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_proof : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sentence) := ZFReplay.replay kernel_certificate

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) := ZFReplay.replay zero_kernel_certificate
end PPAC.Migration.Internal.SuccessorRecursion
