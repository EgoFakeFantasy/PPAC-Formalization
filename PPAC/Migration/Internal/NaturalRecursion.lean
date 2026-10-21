import PPAC.Migration.Internal.NaturalRecursionDeterminism

/-! 实际消去自然递推算子的总单值义务，再实例化已证全对象超限递归。 -/
namespace PPAC.Migration.Internal.NaturalRecursion
open Source SourceAlgebra SourceLogic ReplacementPredicates NaturalRecursionSyntax

def params2 {n} : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc

def totalSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  ((relationTotal p params2).imp (OrdinalRecursionTotal.total (matrix p)
    (extend params2 (Fin.last n).castSucc (Fin.last (n+1))))).close

def deterministicSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  ((OmegaSyntax.omega (Fin.last n).castSucc).imp ((relationFunctional p params2).imp
    (OrdinalRecursionDeterminism.deterministic (matrix p)
      (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))))).close

def existenceSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  ((OmegaSyntax.omega (Fin.last n).castSucc).imp ((relationTotal p params2).imp ((relationFunctional p params2).imp
    (OrdinalRecursionExistenceSyntax.holds (matrix p)
      (extend params2 (Fin.last n).castSucc (Fin.last (n+1))))))).close

def uniquenessSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  ((OmegaSyntax.omega (Fin.last n).castSucc).imp ((relationTotal p params2).imp ((relationFunctional p params2).imp
    (OrdinalRecursionExistenceSyntax.allUnique (matrix p)
      (extend params2 (Fin.last n).castSucc (Fin.last (n+1))))))).close

theorem source_total {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (totalSentence p) := by
  apply close_derives
  apply Derives.impI
  exact NaturalRecursionTotal.operator_total p params2 (Fin.last n).castSucc (Fin.last (n+1)) (.hyp (Or.inl rfl))

theorem source_deterministic {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (deterministicSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hs : Derives (Source.SetLanguage.ZF.at (n+2))
      ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.transitiveMatrix, rfl⟩
  exact NaturalRecursionDeterminism.operator_deterministic
    (SequenceContext.add (SequenceContext.add (SequenceContext.source_ZF (n+2)) _) _)
    p params2 (Fin.last n).castSucc (Fin.last (n+1)) (add (add hs _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_existence {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (existenceSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (relationFunctional p params2) (Context.add (relationTotal p params2)
    (Context.add (OmegaSyntax.omega (Fin.last n).castSucc) (Source.SetLanguage.ZF.at (n+2))))
  have hs : Derives Δ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) :=
    add (add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.transitiveMatrix, rfl⟩) _) _) _
  have hw : Derives Δ (OmegaSyntax.omega (Fin.last n).castSucc) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have ht : Derives Δ (relationTotal p params2) := .hyp (Or.inr (Or.inl rfl))
  have hf : Derives Δ (relationFunctional p params2) := .hyp (Or.inl rfl)
  have hA : SequenceContext.Evidence Δ := SequenceContext.add (SequenceContext.add (SequenceContext.add (SequenceContext.source_ZF (n+2)) _) _) _
  have hopT := NaturalRecursionTotal.operator_total p params2 (Fin.last n).castSucc (Fin.last (n+1)) ht
  have hopF := NaturalRecursionDeterminism.operator_deterministic hA p params2 (Fin.last n).castSucc (Fin.last (n+1)) hs hw hf
  have hclosed : Derives Δ ((ObjectTransfiniteRecursion.existenceSentence (matrix p)).rename Fin.elim0) :=
    add (add (add (ObjectTransitiveCover.closed_at (ObjectTransfiniteRecursion.source_existence (matrix p)) (n+2)) _) _) _
  have hi := specialize_close
    ((OrdinalRecursionTotal.total (matrix p) id).imp ((OrdinalRecursionDeterminism.deterministic (matrix p) id).imp
      (OrdinalRecursionExistenceSyntax.holds (matrix p) id)))
    (extend params2 (Fin.last n).castSucc (Fin.last (n+1))) hclosed
  have hi' : Derives Δ ((OrdinalRecursionTotal.total (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))).imp
      ((OrdinalRecursionDeterminism.deterministic (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))).imp
        (OrdinalRecursionExistenceSyntax.holds (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.holds_rename, id_eq] using hi
  exact .impE (.impE hi' hopT) hopF

theorem source_uniqueness {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (uniquenessSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (relationFunctional p params2) (Context.add (relationTotal p params2)
    (Context.add (OmegaSyntax.omega (Fin.last n).castSucc) (Source.SetLanguage.ZF.at (n+2))))
  have hs : Derives Δ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) :=
    add (add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.transitiveMatrix, rfl⟩) _) _) _
  have hw : Derives Δ (OmegaSyntax.omega (Fin.last n).castSucc) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have ht : Derives Δ (relationTotal p params2) := .hyp (Or.inr (Or.inl rfl))
  have hf : Derives Δ (relationFunctional p params2) := .hyp (Or.inl rfl)
  have hA : SequenceContext.Evidence Δ := SequenceContext.add (SequenceContext.add (SequenceContext.add (SequenceContext.source_ZF (n+2)) _) _) _
  have hopT := NaturalRecursionTotal.operator_total p params2 (Fin.last n).castSucc (Fin.last (n+1)) ht
  have hopF := NaturalRecursionDeterminism.operator_deterministic hA p params2 (Fin.last n).castSucc (Fin.last (n+1)) hs hw hf
  have hclosed : Derives Δ ((ObjectTransfiniteRecursion.uniquenessSentence (matrix p)).rename Fin.elim0) :=
    add (add (add (ObjectTransitiveCover.closed_at (ObjectTransfiniteRecursion.source_uniqueness (matrix p)) (n+2)) _) _) _
  have hi := specialize_close
    ((OrdinalRecursionTotal.total (matrix p) id).imp ((OrdinalRecursionDeterminism.deterministic (matrix p) id).imp
      (OrdinalRecursionExistenceSyntax.allUnique (matrix p) id)))
    (extend params2 (Fin.last n).castSucc (Fin.last (n+1))) hclosed
  have hi' : Derives Δ ((OrdinalRecursionTotal.total (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))).imp
      ((OrdinalRecursionDeterminism.deterministic (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))).imp
        (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend params2 (Fin.last n).castSucc (Fin.last (n+1)))))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, id_eq] using hi
  exact .impE (.impE hi' hopT) hopF


theorem total_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (totalSentence p)) := TheoryTransport.sentence (source_total p)
theorem native_total {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (totalSentence p)) :=
  ZFReplay.replay (total_kernel_certificate p)


theorem deterministic_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (deterministicSentence p)) := TheoryTransport.sentence (source_deterministic p)
theorem native_deterministic {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (deterministicSentence p)) :=
  ZFReplay.replay (deterministic_kernel_certificate p)


theorem existence_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existenceSentence p)) := TheoryTransport.sentence (source_existence p)
theorem native_existence {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence p)) :=
  ZFReplay.replay (existence_kernel_certificate p)


theorem uniqueness_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniquenessSentence p)) := TheoryTransport.sentence (source_uniqueness p)
theorem native_uniqueness {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p)) :=
  ZFReplay.replay (uniqueness_kernel_certificate p)
end PPAC.Migration.Internal.NaturalRecursion
