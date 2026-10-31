/- Pinned StableSelectors.Complete.pattern_eq:109-116 and Good.mono:140-143.
Complete assigned rows force literal equality of the whole internal pattern
under extensions. Reuse the SAME sequence quotient and SAME pattern graph;
no new representative selection or quotient recoding. -/
import PPAC.Migration.ConstructionGermGoodDense

namespace PPAC.Migration.ConstructionGermPatternStability
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionGermRawPattern (Value Slice Sequence At RawPattern)
open ConstructionGermEventual (Space)
open ConstructionGermComplete (Complete)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem rows_extend (hM : FirstOrder.Theory.Models M nativeZF) {C B S w lo hi p R : M.Carrier .set}
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hS : Cartesian C B S) (hp : Condition S w p) (hR : ConstructionCohenRows.Rows C B lo hi p R) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset p R := by
  intro t ht
  obtain ⟨a,ha,b,hb,htab⟩ := (hS t).mp (hp.1 t ht)
  obtain ⟨v,hv,hvR⟩ := ConstructionCohenRows.rows_of_mem hM hlo hhi hB hp.2.1 hR ha hb ⟨t,htab,ht⟩
  exact KuratowskiZF.code_unique hM hv htab ▸ hvR

theorem slice_eq_of_common (hM : FirstOrder.Theory.Models M nativeZF)
    {alpha B det g R U delta n F G : M.Carrier .set}
    (hF : Slice alpha B det g R delta n F) (hG : Slice alpha B det g U delta n G)
    (hc : ∀ b, (Project.FirstOrderSemantics.reduct M).mem b alpha →
      ∃ v, Value det g R delta n b v ∧ Value det g U delta n b v) : F = G := by
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM alpha B F).mp hF.1).1.1
    ((ForcingSupportSize.native_mapsTo hM alpha B G).mp hG.1).1.1
  intro b v
  constructor
  · intro hv
    have hb := ((hF.2 b v).mp hv).1
    obtain ⟨c,hcR,hcU⟩ := hc b hb
    have e := ForcingConditionGraphs.function_unique hF.1.1 hv ((hF.2 b c).mpr ⟨hb,hcR⟩)
    exact e.symm ▸ (hG.2 b c).mpr ⟨hb,hcU⟩
  · intro hv
    have hb := ((hG.2 b v).mp hv).1
    obtain ⟨c,hcR,hcU⟩ := hc b hb
    have e := ForcingConditionGraphs.function_unique hG.1.1 hv ((hG.2 b c).mpr ⟨hb,hcU⟩)
    exact e.symm ▸ (hF.2 b c).mpr ⟨hb,hcR⟩

theorem sequence_same (hM : FirstOrder.Theory.Models M nativeZF)
    {w H N alpha B A det g R U p delta s t : M.Carrier .set}
    (hComplete : Complete w H N det alpha p)
    (hg : (Project.FirstOrderSemantics.reduct M).mem g H) (hd : (Project.FirstOrderSemantics.reduct M).mem delta N)
    (hR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hs : Sequence w alpha B A det g R delta s) (ht : Sequence w alpha B A det g U delta t) :
    ConstructionGermEventual.Same w s t := by
  obtain ⟨bound,hbound,hAssigned⟩ := hComplete g hg delta hd
  apply (ConstructionGermEventual.same_iff_values hs.1 ht.1).mpr
  refine ⟨bound,hbound,?_⟩
  intro n hn hbn F G hnF hnG
  apply slice_eq_of_common hM ((hs.2 n F).mp hnF).2 ((ht.2 n G).mp hnG).2
  intro b hb
  obtain ⟨d,x,y,v,hdn,hdx,hxy,a,ha,z,hz,hzp⟩ := hAssigned n hn hbn b hb
  exact ⟨v,⟨d,x,y,a,hdn,hdx,hxy,ha,z,hz,hR z hzp⟩,⟨d,x,y,a,hdn,hdx,hxy,ha,z,hz,hU z hzp⟩⟩

theorem rawPattern_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {w H N alpha B A E det g R U p pr P Q : M.Carrier .set}
    (hComplete : Complete w H N det alpha p) (hg : (Project.FirstOrderSemantics.reduct M).mem g H)
    (hR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hExact : ConstructionGermEventual.Exact w pr)
    (hP : RawPattern w N alpha B A E det g R pr P) (hQ : RawPattern w N alpha B A E det g U pr Q) : P = Q := by
  have compare delta (hd : (Project.FirstOrderSemantics.reduct M).mem delta N) e f
      (he : At w alpha B A det g R pr delta e) (hf : At w alpha B A det g U pr delta f) : e = f := by
    obtain ⟨s,hs,hse⟩ := he
    obtain ⟨t,ht,htf⟩ := hf
    exact (hExact s t e f hse htf).mpr (sequence_same hM hComplete hg hd hR hU hs ht)
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM N E P).mp hP.1).1.1
    ((ForcingSupportSize.native_mapsTo hM N E Q).mp hQ.1).1.1
  intro delta e
  constructor
  · intro he
    obtain ⟨hd,hAt⟩ := (hP.2 delta e).mp he
    obtain ⟨f,hf,_⟩ := hQ.1.1.2 delta hd
    exact (compare delta hd e f hAt ((hQ.2 delta f).mp hf).2).symm ▸ hf
  · intro he
    obtain ⟨hd,hAt⟩ := (hQ.2 delta e).mp he
    obtain ⟨f,hf,_⟩ := hP.1.1.2 delta hd
    exact compare delta hd f e ((hP.2 delta f).mp hf).2 hAt ▸ hf

theorem at_transfer (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H N X K C B alpha A Seq E det p R U pr c P : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hDet : MapsTo X I det)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hU : MapsTo C B U)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hSeq : Space w A Seq) (hpr : MapsTo Seq E pr)
    (hExact : ConstructionGermEventual.Exact w pr) (hComplete : Complete w H N det alpha p)
    (hExtendR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExtendU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hAt : ConstructionGermPattern.At w D chain H N alpha B A E det R pr c P) :
    ConstructionGermPattern.At w D chain H N alpha B A E det U pr c P := by
  obtain ⟨g,hg,hClass,hP⟩ := hAt
  obtain ⟨Q,hQ⟩ := ConstructionGermRawPattern.exists_rawPattern hM hX hC hDet ((hH g).mp hg).1.1
    hU hAlpha hA hSeq hpr
  have e := rawPattern_eq hM hComplete hg hExtendR hExtendU hExact hP hQ
  subst Q
  exact ⟨g,hg,hClass,hQ⟩

theorem pattern_preserved (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hDet : MapsTo X I det)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hR : MapsTo C B R) (hU : MapsTo C B U)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hSeq : Space w A Seq) (hpr : MapsTo Seq E pr)
    (hExact : ConstructionGermEventual.Exact w pr) (hComplete : Complete w H N det alpha p)
    (hExtendR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExtendU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hF : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F) :
    ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det U pr F := by
  refine ⟨hF.1,fun c P => (hF.2 c P).trans (and_congr Iff.rfl ?_)⟩
  exact ⟨at_transfer hM hX hC hDet hH hU hAlpha hA hSeq hpr hExact hComplete hExtendR hExtendU,
    at_transfer hM hX hC hDet hH hR hAlpha hA hSeq hpr hExact hComplete hExtendU hExtendR⟩

theorem pattern_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hDet : MapsTo X I det)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hR : MapsTo C B R) (hU : MapsTo C B U)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hSeq : Space w A Seq) (hpr : MapsTo Seq E pr)
    (hExact : ConstructionGermEventual.Exact w pr) (hComplete : Complete w H N det alpha p)
    (hExtendR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExtendU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hF : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F)
    (hQ : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det U pr Q) : F = Q := by
  have hF' := pattern_preserved hM hX hC hDet hH hR hU hAlpha hA hSeq hpr hExact hComplete hExtendR hExtendU hF
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM G T F).mp hF'.1).1.1
    ((ForcingSupportSize.native_mapsTo hM G T Q).mp hQ.1).1.1
  exact fun c P => (hF'.2 c P).trans (hQ.2 c P).symm

theorem good_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B S lo hi det p r : M.Carrier .set}
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hDet : MapsTo X I det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hp : Condition S w p) (hr : Condition S w r)
    (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p r)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p) :
    ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det r := by
  obtain ⟨alpha,R,A,Seq,E,pr,T,F,hAlpha,hRows,hA,hSeq,hpr,hE,hProj,hExact,hT,hF,hInj,hComplete⟩ := hGood
  obtain ⟨U,hRowsU,hExtendU⟩ := ConstructionCohenRows.construction hM hlo hhi hB hS hr
  have hF' := pattern_preserved hM hX hC hDet hH hRows.1 hRowsU.1 (hK.transitive alpha hAlpha)
    hA hSeq hpr hExact hComplete (rows_extend hM hlo hhi hB hS hp hRows) (fun z hz => hExtendU z (hle z hz)) hF
  exact ⟨alpha,U,A,Seq,E,pr,T,F,hAlpha,hRowsU,hA,hSeq,hpr,hE,hProj,hExact,hT,hF',hInj,ConstructionGermComplete.mono hComplete hle⟩

def preservationSentence {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo U C B)) (.imp (Project.Formula.subset (.bound alpha) (.bound K)) (.imp (ConstructionGermEventual.space alpha B A) (.imp (ConstructionGermEventual.space w A Seq) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr Seq E)) (.imp (ConstructionGermEventual.exactProjection w pr) (.imp (ConstructionGermComplete.complete w H N det alpha p) (.imp (Project.Formula.subset (.bound p) (.bound R)) (.imp (Project.Formula.subset (.bound p) (.bound U)) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det U pr F))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermEventual.space_freeClosed,
      ConstructionGermEventual.exactProjection_freeClosed,ConstructionGermComplete.complete_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem preservation_models {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (preservationSentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (preservationSentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,
    ConstructionGermComplete.complete_semantics hM,ConstructionGermPattern.pattern_semantics hM]
  exact pattern_preserved hM

theorem preservation_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (preservationSentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F)) :=
  ModelTransfer.derives (fun _ hM => preservation_models w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F hM)

def equalitySentence {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo U C B)) (.imp (Project.Formula.subset (.bound alpha) (.bound K)) (.imp (ConstructionGermEventual.space alpha B A) (.imp (ConstructionGermEventual.space w A Seq) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr Seq E)) (.imp (ConstructionGermEventual.exactProjection w pr) (.imp (ConstructionGermComplete.complete w H N det alpha p) (.imp (Project.Formula.subset (.bound p) (.bound R)) (.imp (Project.Formula.subset (.bound p) (.bound U)) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det U pr Q) (Project.Formula.extensionalEq (.bound F) (.bound Q))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,Project.Formula.extensionalEq,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermEventual.space_freeClosed,
      ConstructionGermEventual.exactProjection_freeClosed,ConstructionGermComplete.complete_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem equality_models {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (equalitySentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (equalitySentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,
    ConstructionGermComplete.complete_semantics hM,ConstructionGermPattern.pattern_semantics hM]
  exact pattern_eq hM

theorem equality_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (equalitySentence w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q)) :=
  ModelTransfer.derives (fun _ hM => equality_models w D I mul q root chain H G N X K C B alpha A Seq E T det p R U pr F Q hM)

def monotonicitySentence {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r)) (.imp (Project.Formula.subset (.bound p) (.bound r)) (.imp (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det r))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,Project.Formula.isOrdinal,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.extensionalEq,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermGoodDense.good_freeClosed]

theorem monotonicity_models {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det p r)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det p r)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ConstructionGermCosets.carrier_semantics hM,ConstructionGermGoodDense.good_semantics hM]
  exact good_mono hM

theorem monotonicity_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det p r)) :=
  ModelTransfer.derives (fun _ hM => monotonicity_models w D I mul q root chain H G N X K C B S lo hi det p r hM)

end PPAC.Migration.ConstructionGermPatternStability
