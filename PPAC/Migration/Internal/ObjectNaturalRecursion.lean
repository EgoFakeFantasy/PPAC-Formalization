import PPAC.Migration.Internal.NaturalEvaluationFiber

/-! 全内部自然索引的递推末值存在唯一；每个任意参数步进公式返回完整原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectNaturalRecursion
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def sentence {n} (p : Formula (n+2)) : Source.Sentence :=
  ((omega (Fin.last n).castSucc).imp ((relationTotal p NaturalRecursion.params2).imp
    ((relationFunctional p NaturalRecursion.params2).imp (.all
      ((Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).imp
        (uniqueValue p (paramsUp NaturalRecursion.params2) (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))))))).close

theorem standard_extend {n} : extend (NaturalRecursion.params2 : Fin n → Fin (n+2))
    (Fin.last n).castSucc (Fin.last (n+1)) = id := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extend, Fin.lastCases_last, id_eq]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [extend, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    · simp only [extend, Fin.lastCases_castSucc, NaturalRecursion.params2, id_eq]

theorem extend_old {n m} (ρ : Fin n → Fin m) (w a : Fin m) (i : Fin n) : extend ρ w a i.castSucc.castSucc = ρ i := by
  simp only [extend, Fin.lastCases_castSucc]
theorem extend_w {n m} (ρ : Fin n → Fin m) (w a : Fin m) : extend ρ w a (Fin.last n).castSucc = w := by
  simp only [extend, Fin.lastCases_castSucc, Fin.lastCases_last]
theorem extend_a {n m} (ρ : Fin n → Fin m) (w a : Fin m) : extend ρ w a (Fin.last (n+1)) = a := by
  simp only [extend, Fin.lastCases_last]

theorem instantiate_unique {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence p).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ht : Derives Γ (relationTotal p ρ)) (hf : Derives Γ (relationFunctional p ρ)) :
    Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a)) := by
  have hc' : Derives Γ (((omega (Fin.last n).castSucc).imp ((relationTotal p NaturalRecursion.params2).imp
      ((relationFunctional p NaturalRecursion.params2).imp (OrdinalRecursionExistenceSyntax.allUnique (matrix p) id)))).close.rename Fin.elim0) := by
    simpa only [NaturalRecursion.uniquenessSentence, standard_extend] using hc
  have hi := specialize_close
    ((omega (Fin.last n).castSucc).imp ((relationTotal p NaturalRecursion.params2).imp ((relationFunctional p NaturalRecursion.params2).imp
      (OrdinalRecursionExistenceSyntax.allUnique (matrix p) id)))) (extend ρ w a) hc'
  have hi' : Derives Γ ((omega w).imp ((relationTotal p ρ).imp ((relationFunctional p ρ).imp
      (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a))))) := by
    simpa only [Formula.rename, omega_rename, relationTotal_rename, relationFunctional_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, NaturalRecursion.params2, extend_old, extend_w, extend_a, id_eq] using hi
  exact .impE (.impE (.impE hi' hw) ht) hf

theorem source_proof {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (sentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (relationFunctional p NaturalRecursion.params2) (Context.add (relationTotal p NaturalRecursion.params2)
    (Context.add (omega (Fin.last n).castSucc) (Source.SetLanguage.ZF.at (n+2))))
  have hw : Derives Δ (omega (Fin.last n).castSucc) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have ht : Derives Δ (relationTotal p NaturalRecursion.params2) := .hyp (Or.inr (Or.inl rfl))
  have hf : Derives Δ (relationFunctional p NaturalRecursion.params2) := .hyp (Or.inl rfl)
  have he : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    add (add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩) _) _) _
  have hfound : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) :=
    add (add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩) _) _) _
  have hs : Derives Δ ((Source.SetLanguage.separation OmegaOrdinals.matrix).rename Fin.elim0) :=
    add (add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaOrdinals.matrix, rfl⟩) _) _) _
  have hc : Derives Δ ((NaturalRecursion.uniquenessSentence p).rename Fin.elim0) :=
    add (add (add (ObjectTransitiveCover.closed_at (NaturalRecursion.source_uniqueness p) (n+2)) _) _) _
  have hall := instantiate_unique p NaturalRecursion.params2 (Fin.last n).castSucc (Fin.last (n+1)) hc hw ht hf
  have hord := OmegaOrdinals.elements (Fin.last n).castSucc hfound hs hw
  apply Derives.allI
  let Δr := Context.image Formula.raise Δ
  have he' : Derives Δr (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hw' : Derives Δr (omega (Fin.last n).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hord' : Derives Δr (.all ((Formula.mem (Fin.last (n+3)) (Fin.last n).castSucc.castSucc.castSucc).imp (ordinal (Fin.last (n+3))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using Derives.rename Fin.castSucc hord
  have hall' : Derives Δr (OrdinalRecursionExistenceSyntax.allUnique (matrix p)
      (extend (paramsUp NaturalRecursion.params2) (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using Derives.rename Fin.castSucc hall
  apply Derives.impI
  exact NaturalEvaluationFiber.at_natural p (paramsUp NaturalRecursion.params2) (Fin.last n).castSucc.castSucc
    (Fin.last (n+1)).castSucc (Fin.last (n+2)) (add he' _) (add hw' _) (.hyp (Or.inl rfl)) (add hord' _) (add hall' _)

theorem kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sentence p)) := TheoryTransport.sentence (source_proof p)

theorem native_proof {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) :=
  ZFReplay.replay (kernel_certificate p)
end PPAC.Migration.Internal.ObjectNaturalRecursion
