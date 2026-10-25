import PPAC.Migration.Relativization
import PPAC.Migration.ReverseZFReplay

/-!
Reuse the accepted full ZF presentation equivalence inside a domain interpretation.
The source uses Replacement; YesMetaZFC uses Collection. Neither schema is reproved.
This is the stage-6 consumer of stages 2-3: once the source ZF axioms hold in D,
every native ZF theorem has its translated certificate in the same interpretation.
The domain-nonempty antecedent and interpreted background remain explicit.
This does not assert that a particular L domain satisfies those premises, and
external proof transport is not an internal Proof/Con theorem.
-/
namespace PPAC.Migration.InterpretedZF
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

/-- Transport an already proved source-language sentence without rebuilding its proof. -/
theorem source_sentence (D : Source.Formula 1) {p : Source.Sentence}
    (h : FirstOrder.Derives nativeZF [] (Translation.sentence p)) :
    FirstOrder.Derives (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp (Relativization.formula D p))) :=
  Relativization.kernel_certificate D (ReverseZFReplay.source_sentence h)

/-- The native formula is decoded by the already verified original-kernel compiler. -/
theorem native_sentence (D : Source.Formula 1) {p : FirstOrder.Sentence ℒ}
    (h : FirstOrder.Derives nativeZF [] p) :
    FirstOrder.Derives (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp
        (Relativization.formula D (Reverse.sentence p)))) :=
  Relativization.kernel_certificate D (ReverseZFReplay.source_native_sentence h)

/-- All native ZF axioms, including arbitrary Separation/Collection instances. -/
theorem project_axiom (D : Source.Formula 1) {p : Definitional.Project.Sentence}
    (hp : SetTheory.ZF p) :
    FirstOrder.Derives (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp
        (Relativization.formula D (Reverse.sentence (Definitional.Project.fo_sentence p))))) := by
  apply native_sentence D
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := nativeZF) (Γ := []) (free := [])
      (sentence := Definitional.Project.fo_sentence p) ⟨p, hp, rfl⟩)

/-- Full Collection is inherited from the source Replacement proof in every domain.
The formula and parameter count are unrestricted external schema indices. -/
theorem collection (D : Source.Formula 1) {n : Nat} (p : Source.Formula (n+2)) :
    FirstOrder.Derives (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp
        (Relativization.formula D (CollectionSyntax.collection p)))) :=
  source_sentence D (CollectionFromReplacement.native_source_matrix p)

end PPAC.Migration.InterpretedZF
