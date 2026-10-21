import PPAC.Migration.OrdinalRecursionUnique

/-! 任意参数递推公式在全部内部原序数上的实际递归图存在唯一；原ZF中的完整对象模式。 -/
namespace PPAC.Migration.ObjectTransfiniteRecursion
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionTotal OrdinalRecursionDeterminism OrdinalRecursionFamilySyntax OrdinalRecursionExistenceSyntax

def params1 {n} : Fin n → Fin (n+1) := Fin.castSucc

def params2 {n} : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc

def collectionSentence {n} (p : Formula (n+3)) : Source.Sentence := ((total p params1).imp ((deterministic p params1).imp
  ((ordinal (Fin.last n)).imp ((predecessors p params1 (Fin.last n)).imp (familyExists p params1 (Fin.last n)))))).close

def unionSentence {n} (p : Formula (n+3)) : Source.Sentence := ((deterministic p params2).imp
  ((ordinal (Fin.last (n+1))).imp ((family p params2 (Fin.last n).castSucc (Fin.last (n+1))).imp
    (recursorExists p params2 (Fin.last (n+1)))))).close

def existenceSentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((total p id).imp ((deterministic p id).imp (holds p id))).close

def uniquenessSentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((total p id).imp ((deterministic p id).imp (allUnique p id))).close

theorem source_collection {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (collectionSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hr : Derives (Source.SetLanguage.ZF.at (n+1))
      ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p), rfl⟩
  exact OrdinalRecursionCollection.exists_family
    (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add
      (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF (n+1)) _) _) _) _)
    p params1 (Fin.last n) (add (add (add (add hr _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_union {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (unionSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionUnion.exists_union
    (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add
      (OrdinalRecursionContext.source_ZF (n+2)) _) _) _)
    p params2 (Fin.last n).castSucc (Fin.last (n+1)) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_existence {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (existenceSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hr : Derives (Source.SetLanguage.ZF.at n)
      ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p), rfl⟩
  have hs : Derives (Source.SetLanguage.ZF.at n)
      ((Source.SetLanguage.separation (existenceMatrix p).neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation (existenceMatrix p).neg, rfl⟩
  have hc := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover n
  let Δ := Context.add (deterministic p (id : Fin n → Fin n))
    (Context.add (total p (id : Fin n → Fin n)) (Source.SetLanguage.ZF.at n))
  have hA : OrdinalRecursionContext.Evidence Δ :=
    OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF n) _) _
  have ht : Derives Δ (total p id) := .hyp (Or.inr (Or.inl rfl))
  have hdet : Derives Δ (deterministic p id) := .hyp (Or.inl rfl)
  exact OrdinalRecursionExistence.all_exists hA p id (add (add hr _) _) (add (add hs _) _) (add (add hc _) _) ht hdet

theorem source_uniqueness {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (uniquenessSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hr : Derives (Source.SetLanguage.ZF.at n)
      ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p), rfl⟩
  have hs : Derives (Source.SetLanguage.ZF.at n)
      ((Source.SetLanguage.separation (existenceMatrix p).neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation (existenceMatrix p).neg, rfl⟩
  have hc := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover n
  let Δ := Context.add (deterministic p (id : Fin n → Fin n))
    (Context.add (total p (id : Fin n → Fin n)) (Source.SetLanguage.ZF.at n))
  have hA : OrdinalRecursionContext.Evidence Δ :=
    OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF n) _) _
  have ht : Derives Δ (total p id) := .hyp (Or.inr (Or.inl rfl))
  have hdet : Derives Δ (deterministic p id) := .hyp (Or.inl rfl)
  have hAll := OrdinalRecursionExistence.all_exists hA p id (add (add hr _) _) (add (add hs _) _) (add (add hc _) _) ht hdet
  exact OrdinalRecursionUnique.all_unique hA p id hdet hAll

theorem collection_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (collectionSentence p)) := TheoryTransport.sentence (source_collection p)

theorem native_collection {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (collectionSentence p)) :=
  ZFReplay.replay (collection_kernel_certificate p)

theorem union_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (unionSentence p)) := TheoryTransport.sentence (source_union p)

theorem native_union {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (unionSentence p)) :=
  ZFReplay.replay (union_kernel_certificate p)

theorem existence_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (existenceSentence p)) := TheoryTransport.sentence (source_existence p)

theorem native_existence {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence p)) :=
  ZFReplay.replay (existence_kernel_certificate p)

theorem uniqueness_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (uniquenessSentence p)) := TheoryTransport.sentence (source_uniqueness p)

theorem native_uniqueness {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p)) :=
  ZFReplay.replay (uniqueness_kernel_certificate p)
end PPAC.Migration.ObjectTransfiniteRecursion
