import PPAC.Migration.OrdinalRecursionSuccessorUnique

/-! 任意参数递推矩阵的实际下一值、后继扩展和唯一后继图纤维；完整原核模式。 -/
namespace PPAC.Migration.ObjectOrdinalRecursionSuccessor
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionTotal OrdinalRecursionDeterminism OrdinalRecursionSuccessorSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.foundation ∨
  q = Source.SetLanguage.pairing ∨ q = Source.SetLanguage.union ∨ q = Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg

def params1 {n} : Fin n → Fin (n+1) := Fin.castSucc

def params2 {n} : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc

def params3 {n} : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc

def params6 {n} : Fin n → Fin (n+6) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc

def evaluationSentence {n} (p : Formula (n+3)) : Source.Sentence := ((total p params2).imp
  ((ordinal (Fin.last n).castSucc).imp ((recursor p params2 (Fin.last (n+1)) (Fin.last n).castSucc).imp (hasValue p params2 (Fin.last n).castSucc (Fin.last (n+1)))))).close

def preservationSentence {n} (p : Formula (n+3)) : Source.Sentence := ((ordinal (Fin.last (n+4)).castSucc).imp
  ((recursor p params6 (Fin.last (n+3)).castSucc.castSucc (Fin.last (n+4)).castSucc).imp ((GraphInsertSyntax.witness (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc.castSucc.castSucc (Fin.last (n+3)).castSucc.castSucc (Fin.last (n+4)).castSucc (Fin.last (n+4)).castSucc (Fin.last (n+5))).imp
    ((operator p params6 (Fin.last (n+4)).castSucc (Fin.last (n+3)).castSucc.castSucc (Fin.last (n+5))).imp (recursor p params6 (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc))))).close

def extensionSentence {n} (p : Formula (n+3)) : Source.Sentence := ((total p params2).imp
  ((ordinal (Fin.last n).castSucc).imp ((recursor p params2 (Fin.last (n+1)) (Fin.last n).castSucc).imp (extensionExists p params2 (Fin.last (n+1)) (Fin.last n).castSucc)))).close

def successorSentence {n} (p : Formula (n+3)) : Source.Sentence := ((total p params1).imp
  ((ordinal (Fin.last n)).imp ((recursorExists p params1 (Fin.last n)).imp (successorExists p params1 (Fin.last n))))).close

def uniqueSentence {n} (p : Formula (n+3)) : Source.Sentence := ((deterministic p params3).imp
  ((ordinal (Fin.last n).castSucc.castSucc).imp ((successorGraph p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
    ((successorGraph p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+2))).imp (.equal (Fin.last (n+1)).castSucc (Fin.last (n+2))))))).close

def fiberSentence {n} (p : Formula (n+3)) : Source.Sentence := ((total p params1).imp ((deterministic p params1).imp
  ((ordinal (Fin.last n)).imp ((recursorExists p params1 (Fin.last n)).imp (OrdinalRecursionSuccessorUnique.uniqueFiber p params1 (Fin.last n)))))).close

theorem ext_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩

theorem foundation_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem pairing_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩

theorem union_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩

theorem separation_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

theorem source_evaluation {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (evaluationSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact evaluate p params2 (Fin.last n).castSucc (Fin.last (n+1)) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_preservation {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (preservationSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionExtension.recursor_preserved p params6 (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc.castSucc.castSucc (Fin.last (n+3)).castSucc.castSucc (Fin.last (n+4)).castSucc (Fin.last (n+5))
    (add (add (add (add (ext_at (n+6)) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_extension {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (extensionSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionSuccessorExistence.exists_extension p params2 (Fin.last (n+1)) (Fin.last n).castSucc
    (add (add (add (ext_at (n+2)) _) _) _)
    (add (add (add (foundation_at (n+2)) _) _) _)
    (add (add (add (pairing_at (n+2)) _) _) _)
    (add (add (add (union_at (n+2)) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_successor {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (successorSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionSuccessorExistence.successor_of_exists p params1 (Fin.last n)
    (add (add (add (ext_at (n+1)) _) _) _)
    (add (add (add (foundation_at (n+1)) _) _) _)
    (add (add (add (pairing_at (n+1)) _) _) _)
    (add (add (add (union_at (n+1)) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_unique {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (uniqueSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionSuccessorUnique.graphs_unique p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
    (add (add (add (add (ext_at (n+3)) _) _) _) _)
    (add (add (add (add (foundation_at (n+3)) _) _) _) _)
    (add (add (add (add (separation_at (n+3)) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_fiber {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (fiberSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionSuccessorUnique.exists_unique_successor p params1 (Fin.last n)
    (add (add (add (add (ext_at (n+1)) _) _) _) _)
    (add (add (add (add (foundation_at (n+1)) _) _) _) _)
    (add (add (add (add (pairing_at (n+1)) _) _) _) _)
    (add (add (add (add (union_at (n+1)) _) _) _) _)
    (add (add (add (add (separation_at (n+1)) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationSyntax.agreementMatrix.neg, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_foundation
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_union
  · exact SeparationSyntax.source_separation IterationSyntax.agreementMatrix.neg

theorem evaluation_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (evaluationSentence p)) := TheoryTransport.sentence (source_evaluation p)

theorem source_ZF_evaluation {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (evaluationSentence p) := source_ZF_replay (source_evaluation p)

theorem native_evaluation {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationSentence p)) :=
  native_replay (evaluation_kernel_certificate p)

theorem preservation_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (preservationSentence p)) := TheoryTransport.sentence (source_preservation p)

theorem source_ZF_preservation {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (preservationSentence p) := source_ZF_replay (source_preservation p)

theorem native_preservation {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (preservationSentence p)) :=
  native_replay (preservation_kernel_certificate p)

theorem extension_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (extensionSentence p)) := TheoryTransport.sentence (source_extension p)

theorem source_ZF_extension {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (extensionSentence p) := source_ZF_replay (source_extension p)

theorem native_extension {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (extensionSentence p)) :=
  native_replay (extension_kernel_certificate p)

theorem successor_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (successorSentence p)) := TheoryTransport.sentence (source_successor p)

theorem source_ZF_successor {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (successorSentence p) := source_ZF_replay (source_successor p)

theorem native_successor {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (successorSentence p)) :=
  native_replay (successor_kernel_certificate p)

theorem unique_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (uniqueSentence p)) := TheoryTransport.sentence (source_unique p)

theorem source_ZF_unique {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence p) := source_ZF_replay (source_unique p)

theorem native_unique {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence p)) :=
  native_replay (unique_kernel_certificate p)

theorem fiber_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (fiberSentence p)) := TheoryTransport.sentence (source_fiber p)

theorem source_ZF_fiber {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (fiberSentence p) := source_ZF_replay (source_fiber p)

theorem native_fiber {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (fiberSentence p)) :=
  native_replay (fiber_kernel_certificate p)
end PPAC.Migration.ObjectOrdinalRecursionSuccessor
