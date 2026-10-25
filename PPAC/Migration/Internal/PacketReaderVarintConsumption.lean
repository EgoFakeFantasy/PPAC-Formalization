import PPAC.Migration.Internal.PacketReaderVarintSegmentInduction
import PPAC.Migration.Internal.StructuralListSpliceTotal

/-! Every actual canonical varint has a unique actual splice with arbitrary valid trailing input, and that splice consumes the whole token on all internal return candidates. -/
namespace PPAC.Migration.Internal.PacketReaderVarintConsumption
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderVarintSegmentSyntax
open SyntaxRenameQuerySyntax (of_eq)

def allOutputs {m} (w B z o L T v s a c : Fin m) : Formula m := .all
  (agreement w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc T.castSucc v.castSucc s.castSucc a.castSucc c.castSucc (Fin.last m))

def law {m} (w B z o C T v s a c L : Fin m) : Formula m :=
  (Formula.mem L w).conj ((StructuralListSpliceSyntax.splice w C T L).conj (allOutputs w B z o L T v s a c))

def complete {m} (w B z o C T v s a c : Fin m) : Formula m := .ex
  ((law w.castSucc B.castSucc z.castSucc o.castSucc C.castSucc T.castSucc v.castSucc s.castSucc a.castSucc c.castSucc (Fin.last m)).conj
    (StructuralListSpliceTotalSyntax.uniqueAt w.castSucc C.castSucc T.castSucc (Fin.last m)))

theorem allOutputs_rename {m k} (w B z o L T v s a c : Fin m) (ρ : Fin m → Fin k) :
    (allOutputs w B z o L T v s a c).rename ρ = allOutputs (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ T) (ρ v) (ρ s) (ρ a) (ρ c) := by
  simp only [allOutputs,Formula.rename,agreement_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem law_rename {m k} (w B z o C T v s a c L : Fin m) (ρ : Fin m → Fin k) :
    (law w B z o C T v s a c L).rename ρ = law (ρ w) (ρ B) (ρ z) (ρ o) (ρ C) (ρ T) (ρ v) (ρ s) (ρ a) (ρ c) (ρ L) := by
  simp only [law,Formula.rename,StructuralListSpliceSyntax.splice_rename,allOutputs_rename]

theorem complete_rename {m k} (w B z o C T v s a c : Fin m) (ρ : Fin m → Fin k) :
    (complete w B z o C T v s a c).rename ρ = complete (ρ w) (ρ B) (ρ z) (ρ o) (ρ C) (ρ T) (ρ v) (ρ s) (ρ a) (ρ c) := by
  simp only [complete,Formula.rename,law_rename,StructuralListSpliceTotalSyntax.uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem all_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T L v s a u c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hCanonical : Derives Γ (PacketVarintSyntax.canonical w n C)) (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a)) (hG : Derives Γ (guard o n s))
    (hu : Derives Γ (PacketAffineSyntax.equation w n v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ (allOutputs w B z o L T v s a c) := by
  apply Derives.allI
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (Derives.rename Fin.castSucc hB)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (Derives.rename Fin.castSucc hz)
  have hCanon1 := of_eq (PacketVarintSyntax.canonical_rename w n C Fin.castSucc) (Derives.rename Fin.castSucc hCanonical)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w C T L Fin.castSucc) (Derives.rename Fin.castSucc hSp)
  have hT1 := of_eq (PacketReaderStepSyntax.state_rename w T v s a Fin.castSucc) (Derives.rename Fin.castSucc hT)
  have hG1 := of_eq (guard_rename o n s Fin.castSucc) (Derives.rename Fin.castSucc hG)
  have hu1 := of_eq (PacketAffineSyntax.equation_rename w n v s u Fin.castSucc) (Derives.rename Fin.castSucc hu)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w u a c Fin.castSucc) (Derives.rename Fin.castSucc hc)
  exact PacketReaderVarintSegmentInduction.segment hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc C.castSucc T.castSucc L.castSucc v.castSucc s.castSucc a.castSucc u.castSucc c.castSucc (Fin.last m)
    hw1 hB1 hz1 (Derives.rename Fin.castSucc ho) hCanon1 hSp1 hT1 hG1 hu1 hc1

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T v s a u c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hCanonical : Derives Γ (PacketVarintSyntax.canonical w n C)) (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a))
    (hG : Derives Γ (guard o n s)) (hu : Derives Γ (PacketAffineSyntax.equation w n v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ (complete w B z o C T v s a c) := by
  have hPrefix := Derives.conjL (.conjR (PacketVarintDomain.domain w n C hCanonical))
  let R := StructuralListSpliceTotalSyntax.fiberBody w C T
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSpliceTotal.exists_unique hZ w C T hw hPrefix (.conjL hT))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have hCanon1 := of_eq (PacketVarintSyntax.canonical_rename w n C Fin.castSucc) (under hCanonical R)
  have hT1 := of_eq (PacketReaderStepSyntax.state_rename w T v s a Fin.castSucc) (under hT R)
  have hG1 := of_eq (guard_rename o n s Fin.castSucc) (under hG R)
  have hu1 := of_eq (PacketAffineSyntax.equation_rename w n v s u Fin.castSucc) (under hu R)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w u a c Fin.castSucc) (under hc R)
  have hAll := all_outputs hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc C.castSucc T.castSucc (Fin.last m) v.castSucc s.castSucc a.castSucc u.castSucc c.castSucc
    hw1 hB1 hz1 (under ho R) hCanon1 (.conjR (.conjL hR)) hT1 hG1 hu1 hc1
  have hLaw : Derives Δ (law w.castSucc B.castSucc z.castSucc o.castSucc C.castSucc T.castSucc v.castSucc s.castSucc a.castSucc c.castSucc (Fin.last m)) := .conjI (.conjL (.conjL hR)) (.conjI (.conjR (.conjL hR)) hAll)
  have hout : Derives Δ (complete w.castSucc B.castSucc z.castSucc o.castSucc C.castSucc T.castSucc v.castSucc s.castSucc a.castSucc c.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,law_rename,StructuralListSpliceTotalSyntax.uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hLaw (.conjR hR))
  simpa only [Formula.raise,complete_rename] using hout

end PPAC.Migration.Internal.PacketReaderVarintConsumption
