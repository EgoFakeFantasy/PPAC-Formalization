/- Pinned LocalQuotients.labelSet_subsetBound:247 and
normalized_subset_labelSet:270. Consume the actual labelSet and the existing
PowerName bound/atomic forcing equations; no rank or support restriction. -/
import PPAC.Migration.ForcingLabelSet

namespace PPAC.Migration.ForcingLabelBound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingLabelNames (Label)
open ForcingLabelSet (LabelSet)
open ForcingPowerName (Bound Subset SubsetF)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source-language adapter for the existing, unchanged PowerName.Bound. -/
def bound {k : Nat} (W sigma B : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) B.castSucc).iff (.ex (.ex (.ex
    ((Source.SetLanguage.edge sigma.castSucc.castSucc.castSucc.castSucc
      (Fin.last (k+1)).castSucc.castSucc (Fin.last (k+2)).castSucc).conj
      ((Formula.mem (Fin.last (k+3)) W.castSucc.castSucc.castSucc.castSucc).conj
        (PairSyntax.ordered (Fin.last k).castSucc.castSucc.castSucc
          (Fin.last (k+1)).castSucc.castSucc (Fin.last (k+3)))))))))

theorem bound_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W sigma B : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (bound W sigma B) ↔
      Bound (env W) (env sigma) (env B) := by
  simp only [bound,Bound,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,KuratowskiZF.source_code,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨fun hz => by
    obtain ⟨child,c,p,he,hp,hcode⟩ := (h z).1 hz
    exact ⟨child,c,he,p,hp,hcode⟩,fun hz => by
      obtain ⟨child,c,he,p,hp,hcode⟩ := hz
      exact (h z).2 ⟨child,c,p,he,hp,hcode⟩⟩,
    fun h z => ⟨fun hz => by
      obtain ⟨child,c,he,p,hp,hcode⟩ := (h z).mp hz
      exact ⟨child,c,p,he,hp,hcode⟩,fun hz => by
        obtain ⟨child,c,p,he,hp,hcode⟩ := hz
        exact (h z).mpr ⟨child,c,he,p,hp,hcode⟩⟩⟩

def Entry (W I K c t b z : M.Carrier .set) : Prop :=
  ∃ child j p, (Project.FirstOrderSemantics.reduct M).mem j I ∧ Label W K c t j b child ∧
    (Project.FirstOrderSemantics.reduct M).mem p W ∧ PureKuratowski.Code M z child p

def entry {k : Nat} (W I K c t b z : Fin k) : Formula k :=
  .ex (.ex (.ex ((Formula.mem (Fin.last (k+1)).castSucc I.castSucc.castSucc.castSucc).conj
    ((ForcingLabelNames.label W.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc
      c.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc
      b.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc).conj
        ((Formula.mem (Fin.last (k+2)) W.castSucc.castSucc.castSucc).conj
          (PairSyntax.ordered z.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc (Fin.last (k+2))))))))

theorem entry_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W I K c t b z : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (entry W I K c t b z) ↔
      Entry (env W) (env I) (env K) (env c) (env t) (env b) (env z) := by
  simp only [entry,Entry,Formula.Realize,ForcingLabelNames.label_semantics (M := M),KuratowskiZF.source_code,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Exact raw collect of every label with every condition, without a rank cutoff. -/
def LabelBound (W I K c t b B : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z B ↔ Entry W I K c t b z

def labelBound {k : Nat} (W I K c t b B : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) B.castSucc).iff
    (entry W.castSucc I.castSucc K.castSucc c.castSucc t.castSucc b.castSucc (Fin.last k)))

theorem labelBound_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W I K c t b B : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (labelBound W I K c t b B) ↔
      LabelBound (env W) (env I) (env K) (env c) (env t) (env b) (env B) := by
  simp only [labelBound,LabelBound,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1,(h z).2⟩,fun h z => ⟨(h z).mp,(h z).mpr⟩⟩

theorem bound_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {W I K c t b sigma B : M.Carrier .set} (hs : LabelSet W I K c t b sigma) :
    Bound W sigma B ↔ LabelBound W I K c t b B := by
  constructor
  · intro hb z
    constructor
    · intro hz
      obtain ⟨child,d,he,p,hp,hcode⟩ := (hb z).mp hz
      obtain ⟨_,j,hj,hl⟩ := (ForcingLabelSet.edge_labelSet hM hs child d).mp he
      exact ⟨child,j,p,hj,hl,hp,hcode⟩
    · rintro ⟨child,j,p,hj,hl,hp,hcode⟩
      exact (hb z).mpr ⟨child,t,(ForcingLabelSet.edge_labelSet hM hs child t).mpr ⟨rfl,j,hj,hl⟩,p,hp,hcode⟩
  · intro hb z
    constructor
    · intro hz
      obtain ⟨child,j,p,hj,hl,hp,hcode⟩ := (hb z).mp hz
      exact ⟨child,t,(ForcingLabelSet.edge_labelSet hM hs child t).mpr ⟨rfl,j,hj,hl⟩,p,hp,hcode⟩
    · rintro ⟨child,d,he,p,hp,hcode⟩
      obtain ⟨_,j,hj,hl⟩ := (ForcingLabelSet.edge_labelSet hM hs child d).mp he
      exact (hb z).mpr ⟨child,j,p,hj,hl,hp,hcode⟩

theorem edge_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {W I K c t b B : M.Carrier .set} (hb : LabelBound W I K c t b B) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p B ↔ (Project.FirstOrderSemantics.reduct M).mem p W ∧
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j I ∧ Label W K c t j b child := by
  constructor
  · rintro ⟨z,hcode,hz⟩
    obtain ⟨x,j,q,hj,hl,hq,hcode'⟩ := (hb z).mp hz
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨hq,j,hj,hl⟩
  · rintro ⟨hp,j,hj,hl⟩
    obtain ⟨z,hcode⟩ := KuratowskiZF.exists_code hM child p
    exact ⟨z,hcode,(hb z).mpr ⟨child,j,p,hj,hl,hp,hcode⟩⟩

/-- Source normalized_subset_labelSet, for every raw subset of the actual bound.
The stronger statement does not need an extra HS or rank hypothesis. -/
theorem normalized_subset (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    {W I K c t b sigma B nu p : M.Carrier .set}
    (hs : LabelSet W I K c t b sigma) (hb : LabelBound W I K c t b B) (hnu : Subset nu B)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t W)
    (hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q t) :
    SubsetF R H env W p nu sigma := by
  intro tau _ q hq _ hm
  apply (ForcingAtomicRelations.mem_iff hM R env W tau sigma q).mpr
  refine ⟨hq,?_⟩
  intro r hr hrq
  obtain ⟨s,child,d,hsW,hsr,_,he,_,heq⟩ :=
    ((ForcingAtomicRelations.mem_iff hM R env W tau nu q).mp hm).2 r hr hrq
  have heB : PureKuratowski.PairMember M child d B := by
    obtain ⟨z,hcode,hz⟩ := he
    exact ⟨z,hcode,hnu z hz⟩
  obtain ⟨_,j,hj,hl⟩ := (edge_bound hM hb child d).mp heB
  exact ⟨s,child,t,hsW,hsr,ht,(ForcingLabelSet.edge_labelSet hM hs child t).mpr ⟨rfl,j,hj,hl⟩,
    hTop s hsW,heq⟩

def equationSentence : Source.Sentence :=
  ((ForcingLabelSet.labelSet (0 : Fin 8) 1 2 3 4 5 6).imp
    ((bound 0 6 7).iff (labelBound 0 1 2 3 4 5 7))).close

theorem equation_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence equationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hs
  have h := bound_iff (B := env 7) hM ((ForcingLabelSet.labelSet_semantics (M := M) env 0 1 2 3 4 5 6).mp hs)
  exact ⟨fun hb => (labelBound_semantics (M := M) env 0 1 2 3 4 5 7).mpr
    (h.mp ((bound_semantics (M := M) env 0 6 7).mp hb)),
    fun hb => (bound_semantics (M := M) env 0 6 7).mpr
      (h.mpr ((labelBound_semantics (M := M) env 0 1 2 3 4 5 7).mp hb))⟩

theorem equation_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence equationSentence) :=
  ModelTransfer.derives (fun _ hM => equation_models hM)

def subsetSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K c t b sigma B nu p G F mul : Fin k) : Source.Sentence :=
  ((ForcingLabelSet.labelSet (rho 6) I K c t b sigma).imp
    ((labelBound (rho 6) I K c t b B).imp
      ((Source.SetLanguage.subset nu B).imp
        ((ForcingWithTopCarrier.empty t).imp
          ((Formula.mem t (rho 6)).imp
            (ForcingPowerName.subsetF (ForcingProductSymmetry.orderFormula (rho 0) mul)
              (ForcingPairUnion.domain rho G F) id (rho 6) p nu sigma)))))).close

theorem subset_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K c t b sigma B nu p G F mul : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (subsetSentence rho I K c t b sigma B nu p G F mul)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hs hb hn ht htW
  apply (ForcingPowerName.subsetF_semantics (M := M) env (ForcingProductSymmetry.orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) id (rho 6) p nu sigma).mpr
  exact normalized_subset hM (ForcingProductSymmetry.orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env
    ((ForcingLabelSet.labelSet_semantics (M := M) env (rho 6) I K c t b sigma).mp hs)
    ((labelBound_semantics (M := M) env (rho 6) I K c t b B).mp hb)
    ((ForcingLabelPermutations.subset_semantics (M := M) env nu B).mp hn) htW
    (fun q _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q (env t)).mpr
      (Or.inl ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)))

theorem subset_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K c t b sigma B nu p G F mul : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (subsetSentence rho I K c t b sigma B nu p G F mul)) :=
  ModelTransfer.derives (fun _ hM => subset_models rho I K c t b sigma B nu p G F mul hM)

end PPAC.Migration.ForcingLabelBound
