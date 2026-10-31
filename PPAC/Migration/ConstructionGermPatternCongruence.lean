/- Pinned GermSelectors.rawPattern_congr:416-427.
Consume actual detector eventual agreement and the exact Eventual projection.
This is equality of the actual internal rawPattern graphs, not just their
cardinalities or an external function equality. Consumer: pattern/pattern_mk. -/
import PPAC.Migration.ConstructionGermRawPattern
import PPAC.Migration.ConstructionGermDetectors

namespace PPAC.Migration.ConstructionGermPatternCongruence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ConstructionGermRawPattern (Value Slice Sequence At RawPattern)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem value_congr {det g h R delta n b v : M.Carrier .set}
    (he : ∀ t x y, PureKuratowski.Code M t delta n → PureKuratowski.PairMember M t x det →
      (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h)) :
    Value det g R delta n b v ↔ Value det h R delta n b v := by
  constructor
  · rintro ⟨t,x,y,a,ht,htx,hxy,ha,hav⟩
    exact ⟨t,x,y,a,ht,htx,(he t x y ht htx).mp hxy,ha,hav⟩
  · rintro ⟨t,x,y,a,ht,htx,hxy,ha,hav⟩
    exact ⟨t,x,y,a,ht,htx,(he t x y ht htx).mpr hxy,ha,hav⟩

theorem slice_congr {alpha B det g h R delta n F : M.Carrier .set}
    (he : ∀ t x y, PureKuratowski.Code M t delta n → PureKuratowski.PairMember M t x det →
      (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h)) :
    Slice alpha B det g R delta n F ↔ Slice alpha B det h R delta n F := by
  constructor
  · rintro ⟨hF,hEdge⟩
    exact ⟨hF,fun b v => (hEdge b v).trans (and_congr Iff.rfl (value_congr he))⟩
  · rintro ⟨hF,hEdge⟩
    exact ⟨hF,fun b v => (hEdge b v).trans (and_congr Iff.rfl (value_congr he).symm)⟩

theorem sequence_same {w alpha B A det g h R delta s t : M.Carrier .set}
    (he : ∃ bound, (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ n a x y,
      PureKuratowski.Code M a delta n → PureKuratowski.PairMember M a x det → NatLe bound n →
        (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h))
    (hs : Sequence w alpha B A det g R delta s) (ht : Sequence w alpha B A det h R delta t) :
    ConstructionGermEventual.Same w s t := by
  obtain ⟨bound,hbound,he⟩ := he
  refine ⟨bound,hbound,?_⟩
  intro n _ hbn F
  exact (hs.2 n F).trans ((and_congr Iff.rfl (slice_congr (fun a x y ha hx => he n a x y ha hx hbn))).trans (ht.2 n F).symm)

theorem at_congr {w alpha B A det g h R pr delta E F : M.Carrier .set}
    (hExact : ConstructionGermEventual.Exact w pr)
    (he : ∃ bound, (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ n a x y,
      PureKuratowski.Code M a delta n → PureKuratowski.PairMember M a x det → NatLe bound n →
        (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h))
    (hE : At w alpha B A det g R pr delta E) (hF : At w alpha B A det h R pr delta F) : E = F := by
  obtain ⟨s,hs,hsE⟩ := hE
  obtain ⟨t,ht,htF⟩ := hF
  exact (hExact s t E F hsE htF).mpr (sequence_same he hs ht)

theorem rawPattern_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {w N alpha B A Q det g h R pr P T : M.Carrier .set}
    (hExact : ConstructionGermEventual.Exact w pr)
    (he : ∃ bound, (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ delta n a x y,
      PureKuratowski.Code M a delta n → PureKuratowski.PairMember M a x det → NatLe bound n →
        (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h))
    (hP : RawPattern w N alpha B A Q det g R pr P) (hT : RawPattern w N alpha B A Q det h R pr T) : P = T := by
  obtain ⟨bound,hbound,he⟩ := he
  have hDelta delta : ∃ bound, (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ n a x y,
      PureKuratowski.Code M a delta n → PureKuratowski.PairMember M a x det → NatLe bound n →
        (PureKuratowski.PairMember M x y g ↔ PureKuratowski.PairMember M x y h) := ⟨bound,hbound,he delta⟩
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM N Q P).mp hP.1).1.1
    ((ForcingSupportSize.native_mapsTo hM N Q T).mp hT.1).1.1
  intro delta E
  constructor
  · intro hdE
    obtain ⟨hd,hAt⟩ := (hP.2 delta E).mp hdE
    obtain ⟨F,hdF,_⟩ := hT.1.1.2 delta hd
    have e := at_congr hExact (hDelta delta) hAt ((hT.2 delta F).mp hdF).2
    exact e.symm ▸ hdF
  · intro hdE
    obtain ⟨hd,hAt⟩ := (hT.2 delta E).mp hdE
    obtain ⟨F,hdF,_⟩ := hP.1.1.2 delta hd
    have e := at_congr hExact (hDelta delta) ((hP.2 delta F).mp hdF).2 hAt
    exact e ▸ hdF

theorem rawPattern_congr (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T : M.Carrier .set}
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hSame : ConstructionGermCosets.Same w D chain g h)
    (hExact : ConstructionGermEventual.Exact w pr)
    (hP : RawPattern w N alpha B A Q det g R pr P) (hT : RawPattern w N alpha B A Q det h R pr T) : P = T :=
  rawPattern_eq hM hExact (ConstructionGermDetectors.same_eventually hChain hDet hSame) hP hT

def congruenceSentence {m : Nat} (w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ConstructionGermCosets.same w D chain g h) (.imp (ConstructionGermEventual.exactProjection w pr) (.imp (ConstructionGermRawPattern.rawPattern w N alpha B A Q det g R pr P) (.imp (ConstructionGermRawPattern.rawPattern w N alpha B A Q det h R pr T) (Project.Formula.extensionalEq (.bound P) (.bound T))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionGermDetectors.detectors_freeClosed,
      ConstructionGermCosets.same_freeClosed,ConstructionGermEventual.exactProjection_freeClosed,
      ConstructionGermRawPattern.rawPattern_freeClosed]

theorem congruence_models {m : Nat} (w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (congruenceSentence w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (congruenceSentence w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,ConstructionComponentCofinal.chain_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,ConstructionGermCosets.same_semantics hM,
    ConstructionGermEventual.exactProjection_semantics hM,ConstructionGermRawPattern.rawPattern_semantics hM]
  exact rawPattern_congr hM

theorem congruence_kernel_certificate {m : Nat} (w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (congruenceSentence w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T)) :=
  ModelTransfer.derives (fun _ hM => congruence_models w D I mul q zero root vertices chain X reps det N alpha B A Q g h R pr P T hM)

end PPAC.Migration.ConstructionGermPatternCongruence
