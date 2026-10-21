import PPAC.Migration.OmegaStructureAlgebra

/-! ω结构的完整闭句及源ZF/原YesMetaZFC核证书。 -/
namespace PPAC.Migration.ObjectOmegaStructure
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax OmegaStructureAlgebra

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨
  q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.pairing ∨
  q = Source.SetLanguage.separation splitMatrix ∨ q = Source.SetLanguage.separation subsetMatrix ∨
  q = Source.SetLanguage.separation transitiveMatrix

def decompositionSentence : Source.Sentence := ((omega (0 : Fin 1)).imp
  (.all ((Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).imp (split (0 : Fin 1).castSucc (Fin.last 1))))).close

def transitiveSentence : Source.Sentence := ((omega (0 : Fin 1)).imp (transitive 0)).close

def elementsSentence : Source.Sentence := ((omega (0 : Fin 1)).imp
  (.all ((Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).imp (transitive (Fin.last 1))))).close

def zeroSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((empty 1).imp (.mem 1 0))).close

def successorSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp ((successor 2 1).imp (.mem 2 0)))).close

def nonzeroSentence : Source.Sentence := ((omega (0 : Fin 2)).imp
  ((Formula.mem 1 0).imp ((empty 1).neg.imp (predecessor 0 1)))).close

def injectiveSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp ((successor 3 1).imp ((successor 3 2).imp (.equal 1 2))))).close

def freshSuccessor {m} (w x : Fin m) : Formula m := .ex ((Formula.mem (Fin.last m) w.castSucc).conj
  ((successor (Fin.last m) x.castSucc).conj (Formula.mem (Fin.last m) (Fin.last m)).neg))

def freshSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (freshSuccessor 0 1))).close

theorem freshSuccessor_rename {m k} (w x : Fin m) (r : Fin m → Fin k) :
    (freshSuccessor w x).rename r = freshSuccessor (r w) (r x) := by
  simp only [freshSuccessor, Formula.rename, Formula.neg, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fresh_successor {m} {Γ : Context m} (w x : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) : Derives Γ (freshSuccessor w x) := by
  have he := Derives.impE (step_at w x (.conjL hw)) hx
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) x.castSucc)
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at he
  apply Derives.exE (p := S) he
  have hfS : Derives Γs (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf S
  have hpS : Derives Γs (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hn := ObjectIrreflexivity.no_self_member (Fin.last m) hfS hpS
  have hr : Derives Γs (freshSuccessor w.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using Derives.conjI (.conjL hS) (Derives.conjI (.conjR hS) hn)
  simpa only [Formula.raise, freshSuccessor_rename] using hr

theorem source_decomposition : Derives (assumptions.at 0) decompositionSentence := by
  apply close_derives
  apply Derives.impI
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation splitMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  exact OmegaStructureInduction.decomposition 0 (add hs _) (.hyp (Or.inl rfl))

theorem source_transitive : Derives (assumptions.at 0) transitiveSentence := by
  apply close_derives
  apply Derives.impI
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation subsetMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  exact OmegaStructureInduction.omega_transitive 0 (add hs _) (.hyp (Or.inl rfl))

theorem source_elements : Derives (assumptions.at 0) elementsSentence := by
  apply close_derives
  apply Derives.impI
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), rfl⟩
  exact OmegaStructureInduction.elements_transitive 0 (add hs _) (.hyp (Or.inl rfl))

theorem source_zero : Derives (assumptions.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact zero_member 0 1 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_successor : Derives (assumptions.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact successor_member 0 2 1 (add (add (add he _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_nonzero : Derives (assumptions.at 0) nonzeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hs : Derives (assumptions.at 2) ((Source.SetLanguage.separation splitMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  exact nonzero_predecessor 0 1
    (decomposition_at 0 1 (OmegaStructureInduction.decomposition 0 (add (add (add hs _) _) _)
      (.hyp (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl))

theorem source_injective : Derives (assumptions.at 0) injectiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hs : Derives (assumptions.at 4) ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), rfl⟩
  have hf : Derives (assumptions.at 4) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have hp : Derives (assumptions.at 4) (Source.SetLanguage.pairing.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  apply successor_injective 3 1 2
  · exact element_transitive_at 0 1 (OmegaStructureInduction.elements_transitive 0 (add (add (add (add hs _) _) _) _)
        (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  · exact ObjectIrreflexivity.no_self_member 1 (add (add (add (add hf _) _) _) _) (add (add (add (add hp _) _) _) _)
  · exact .hyp (Or.inr (Or.inl rfl))
  · exact .hyp (Or.inl rfl)

theorem source_fresh : Derives (assumptions.at 0) freshSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hf : Derives (assumptions.at 2) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have hp : Derives (assumptions.at 2) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  exact fresh_successor 0 1 (add (add hf _) _) (add (add hp _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation splitMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation subsetMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation transitiveMatrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_foundation
  · exact ZFEquivalence.source_pairing
  · exact SeparationSyntax.source_separation splitMatrix
  · exact SeparationSyntax.source_separation subsetMatrix
  · exact SeparationSyntax.source_separation transitiveMatrix

theorem decomposition_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence decompositionSentence) := TheoryTransport.sentence source_decomposition

theorem source_ZF_decomposition : Derives (Source.SetLanguage.ZF.at 0) decompositionSentence := source_ZF_replay source_decomposition

theorem native_decomposition : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence decompositionSentence) :=
  native_replay decomposition_kernel_certificate

theorem transitive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence transitiveSentence) := TheoryTransport.sentence source_transitive

theorem source_ZF_transitive : Derives (Source.SetLanguage.ZF.at 0) transitiveSentence := source_ZF_replay source_transitive

theorem native_transitive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence transitiveSentence) :=
  native_replay transitive_kernel_certificate

theorem elements_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence elementsSentence) := TheoryTransport.sentence source_elements

theorem source_ZF_elements : Derives (Source.SetLanguage.ZF.at 0) elementsSentence := source_ZF_replay source_elements

theorem native_elements : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence elementsSentence) :=
  native_replay elements_kernel_certificate

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem source_ZF_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := source_ZF_replay source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  native_replay zero_kernel_certificate

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem source_ZF_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := source_ZF_replay source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  native_replay successor_kernel_certificate

theorem nonzero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence nonzeroSentence) := TheoryTransport.sentence source_nonzero

theorem source_ZF_nonzero : Derives (Source.SetLanguage.ZF.at 0) nonzeroSentence := source_ZF_replay source_nonzero

theorem native_nonzero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence nonzeroSentence) :=
  native_replay nonzero_kernel_certificate

theorem injective_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence injectiveSentence) := TheoryTransport.sentence source_injective

theorem source_ZF_injective : Derives (Source.SetLanguage.ZF.at 0) injectiveSentence := source_ZF_replay source_injective

theorem native_injective : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence injectiveSentence) :=
  native_replay injective_kernel_certificate

theorem fresh_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence freshSentence) := TheoryTransport.sentence source_fresh

theorem source_ZF_fresh : Derives (Source.SetLanguage.ZF.at 0) freshSentence := source_ZF_replay source_fresh

theorem native_fresh : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence freshSentence) :=
  native_replay fresh_kernel_certificate
end PPAC.Migration.ObjectOmegaStructure
