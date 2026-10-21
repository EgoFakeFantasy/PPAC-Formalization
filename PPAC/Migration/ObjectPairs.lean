import PPAC.Migration.OrderedPairLogic
import PPAC.Migration.ZFEquivalence

/-! 纯对象Kuratowski对的全量词存在唯一性及分量刻画，输出原Hilbert核Derives。 -/
namespace PPAC.Migration.ObjectPairs
open Source SourceAlgebra SourceLogic PairSyntax OrderedPairElimination

def uniqueAt {m} (p x y : Fin m) : Formula m :=
  (ordered p x y).conj (.all ((ordered (Fin.last m) x.castSucc y.castSucc).imp
    (.equal (Fin.last m) p.castSucc)))

def existsUnique {m} (x y : Fin m) : Formula m := .ex (uniqueAt (Fin.last m) x.castSucc y.castSucc)

theorem uniqueAt_rename {m k} (p x y : Fin m) (r : Fin m → Fin k) :
    (uniqueAt p x y).rename r = uniqueAt (r p) (r x) (r y) := by
  simp only [uniqueAt, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsUnique_rename {m k} (x y : Fin m) (r : Fin m → Fin k) :
    (existsUnique x y).rename r = existsUnique (r x) (r y) := by
  simp only [existsUnique, Formula.rename, uniqueAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exists_unique {m} {Γ : Context m} (x y : Fin m)
    (hpair : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hext : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) :
    Derives Γ (existsUnique x y) := by
  have hp := OrderedPairExistence.exists_pair x y hpair
  let P := ordered (Fin.last m) x.castSucc y.castSucc
  let Γp := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have heP : Derives Γp (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hext P
  have hpP : Derives Γp P := .hyp (Or.inl rfl)
  have hu : Derives Γp (uniqueAt (Fin.last m) x.castSucc y.castSucc) := by
    apply Derives.conjI hpP
    apply Derives.allI
    have heQ : Derives (Context.image Formula.raise Γp)
        (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc heP
    have hpQ : Derives (Context.image Formula.raise Γp)
        (ordered (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
      simpa only [Formula.raise, P, ordered_rename] using Derives.rename Fin.castSucc hpP
    apply Derives.impI
    exact OrderedPairLogic.unique (Fin.last (m+1)) (Fin.last m).castSucc
      x.castSucc.castSucc y.castSucc.castSucc (add heQ _) (.hyp (Or.inl rfl)) (add hpQ _)
  have hr : Derives Γp (existsUnique x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, uniqueAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hu
  simpa only [Formula.raise, existsUnique_rename] using hr

/-- 只含原始配对与外延公理，无Replacement/Collection/AC输入。 -/
def assumptions : Theory := fun q => q = Source.SetLanguage.pairing ∨ q = Source.SetLanguage.extensionality

def existenceSentence : Source.Sentence := (existsUnique (0 : Fin 2) 1).close

def characterizationSentence : Source.Sentence :=
  ((ordered (0 : Fin 6) 2 3).imp ((ordered 1 4 5).imp
    ((Formula.equal 0 1).iff ((Formula.equal 2 4).conj (.equal 3 5))))).close

theorem source_exists_unique : Derives (assumptions.at 0) existenceSentence := by
  apply close_derives
  exact exists_unique 0 1 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)

theorem source_characterization : Derives (assumptions.at 0) characterizationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 6) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact OrderedPairLogic.characterization 0 1 2 3 4 5 (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem existence_kernel_certificate :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence existenceSentence) := TheoryTransport.sentence source_exists_unique

theorem characterization_kernel_certificate :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence characterizationSentence) := TheoryTransport.sentence source_characterization

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) :
    Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩

theorem source_ZF_exists_unique : Derives (Source.SetLanguage.ZF.at 0) existenceSentence :=
  source_ZF_replay source_exists_unique

theorem source_ZF_characterization : Derives (Source.SetLanguage.ZF.at 0) characterizationSentence :=
  source_ZF_replay source_characterization

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_extensionality

theorem native_exists_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existenceSentence) := native_replay existence_kernel_certificate

theorem native_characterization : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence characterizationSentence) := native_replay characterization_kernel_certificate
end PPAC.Migration.ObjectPairs
