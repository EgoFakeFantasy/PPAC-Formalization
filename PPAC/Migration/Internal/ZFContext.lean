import PPAC.Migration.Internal.ObjectNaturalAdditionOrder

/-! 仅映射原ZF公理假设的上下文接口；不把任何算术结论作为字段或新公理。 -/
namespace PPAC.Migration.Internal.ZFContext
open Source SourceAlgebra SourceLogic

def Evidence {m} (Γ : Context m) : Prop := ∀ q, Source.SetLanguage.ZF.at m q → Γ q

theorem source_ZF (m : Nat) : Evidence (Source.SetLanguage.ZF.at m) := fun _ h => h

theorem add {m} {Γ : Context m} (hZ : Evidence Γ) (p : Formula m) : Evidence (Context.add p Γ) :=
  fun q h => Or.inr (hZ q h)

theorem rename {m k} {Γ : Context m} (hZ : Evidence Γ) (r : Fin m → Fin k) :
    Evidence (Context.image (Formula.rename r) Γ) := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q.rename Fin.elim0, hZ _ ⟨q, hq, rfl⟩, closed_rename q r⟩

theorem under {m} {Γ : Context m} (hZ : Evidence Γ) (p : Formula (m+1)) :
    Evidence (Context.add p (Context.image Formula.raise Γ)) := add (rename hZ Fin.castSucc) p

theorem under_two {m} {Γ : Context m} (hZ : Evidence Γ) (p : Formula (m+2)) :
    Evidence (Context.add p (Context.image Formula.raise (Context.image Formula.raise Γ))) :=
  add (rename (rename hZ Fin.castSucc) Fin.castSucc) p

theorem closed {m} {Γ : Context m} (hZ : Evidence Γ) {q : Source.Sentence}
    (h : Derives (Source.SetLanguage.ZF.at 0) q) : Derives Γ (q.rename Fin.elim0) :=
  .weaken hZ (ObjectTransitiveCover.closed_at h m)

theorem separation {n m} {Γ : Context m} (hZ : Evidence Γ) (p : Formula (n+1)) :
    Derives Γ ((Source.SetLanguage.separation p).rename Fin.elim0) :=
  .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.separation p, rfl⟩)

theorem arithmetic {m} {Γ : Context m} (hZ : Evidence Γ) : ArithmeticContext.Evidence Γ := by
  have hA := ArithmeticContext.source_ZF m
  constructor
  · exact ⟨.weaken hZ hA.base.extensionality, .weaken hZ hA.base.pairing,
      .weaken hZ hA.base.union, .weaken hZ hA.base.foundation⟩
  · exact .weaken hZ hA.ordinalSeparation
  · exact .weaken hZ hA.transitiveSeparation
  · exact .weaken hZ hA.restrictionSeparation

theorem recAdd {m} {Γ : Context m} (hZ : Evidence Γ) :
    Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) :=
  closed hZ (NaturalRecursion.source_uniqueness NaturalSuccessorStep.matrix)

theorem recMul {m} {Γ : Context m} (hZ : Evidence Γ) :
    Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) :=
  closed hZ (NaturalRecursion.source_uniqueness NaturalMultiplicationStep.matrix)
end PPAC.Migration.Internal.ZFContext
