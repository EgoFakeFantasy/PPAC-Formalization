/- Pinned StableSelectors.rows_permute/Complete.permute and
GermSelectors.rawPattern_moveRows:442. Transport actual graphs through
the existing coordinate action; use the existing component stabilizer
inverse/composition proofs. No new action or quotient kernel. -/
import PPAC.Migration.ConstructionGermPatternStability

namespace PPAC.Migration.ConstructionGermRowCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingCohenCoordinates (Cartesian)
open ConstructionCohenCompatibility (Entry Moved)
open ConstructionGermRawPattern (Value Slice Sequence At RawPattern)
open ConstructionGermComplete (Complete)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem entry_at_code (hM : FirstOrder.Theory.Models M nativeZF) {p i k b a : M.Carrier .set}
    (ha : PureKuratowski.Code M a i k) : Entry p i k b ↔ PureKuratowski.PairMember M a b p := by
  constructor
  · rintro ⟨a',ha',h⟩
    exact KuratowskiZF.code_unique hM ha' ha ▸ h
  · intro h
    exact ⟨a,ha,h⟩

theorem entry_moved_iff {I pi p q i j k b : M.Carrier .set}
    (hpi : Permutation I pi) (hMove : Moved pi p q) (hij : PureKuratowski.PairMember M i j pi) :
    Entry q j k b ↔ Entry p i k b := by
  constructor
  · intro h
    obtain ⟨i',hi',hp⟩ := (hMove j k b).mp h
    have e := hpi.2.1 i i' j hij hi'
    subst i'
    exact hp
  · intro h
    exact (hMove j k b).mpr ⟨i,hij,h⟩

theorem row_value_moved (hM : FirstOrder.Theory.Models M nativeZF) {I pi p q lo hi i j k a c b : M.Carrier .set}
    (hpi : Permutation I pi) (hMove : Moved pi p q) (hij : PureKuratowski.PairMember M i j pi)
    (ha : PureKuratowski.Code M a i k) (hc : PureKuratowski.Code M c j k) :
    ConstructionCohenRows.Value lo hi p a b ↔ ConstructionCohenRows.Value lo hi q c b := by
  have he : PureKuratowski.PairMember M a hi p ↔ PureKuratowski.PairMember M c hi q :=
    (entry_at_code hM ha).symm.trans ((entry_moved_iff hpi hMove hij).symm.trans (entry_at_code hM hc))
  exact or_congr (and_congr he Iff.rfl) (and_congr (not_congr he) Iff.rfl)

theorem rows_permute (hM : FirstOrder.Theory.Models M nativeZF) {I K C B lo hi pi p q R U : M.Carrier .set}
    (hC : Cartesian I K C) (hpi : Permutation I pi) (hMove : Moved pi p q)
    (hR : ConstructionCohenRows.Rows C B lo hi p R) (hU : ConstructionCohenRows.Rows C B lo hi q U) : Moved pi R U := by
  intro j k b
  constructor
  · rintro ⟨c,hc,hcb⟩
    obtain ⟨hcC,hval⟩ := (hU.2 c b).mp hcb
    obtain ⟨j',hj,k',hk,hc'⟩ := (hC c).mp hcC
    obtain ⟨ej,ek⟩ := PureKuratowski.code_injective hc' hc
    subst j'
    subst k'
    obtain ⟨i,hi,hij⟩ := hpi.2.2 j hj
    obtain ⟨a,ha⟩ := KuratowskiZF.exists_code hM i k
    exact ⟨i,hij,a,ha,(hR.2 a b).mpr ⟨(hC a).mpr ⟨i,hi,k,hk,ha⟩,(row_value_moved hM hpi hMove hij ha hc).mpr hval⟩⟩
  · rintro ⟨i,hij,a,ha,hab⟩
    obtain ⟨haC,hval⟩ := (hR.2 a b).mp hab
    obtain ⟨i',_,k',hk,ha'⟩ := (hC a).mp haC
    obtain ⟨ei,ek⟩ := PureKuratowski.code_injective ha' ha
    subst i'
    subst k'
    obtain ⟨c,hc⟩ := KuratowskiZF.exists_code hM j k
    exact ⟨c,hc,(hU.2 c b).mpr ⟨(hC c).mpr ⟨j,hpi.1.2 i j hij,k,hk,hc⟩,
      (row_value_moved hM hpi hMove hij ha hc).mp hval⟩⟩

theorem value_moved
    {X I det pi g product R U delta n b v : M.Carrier .set}
    (hDet : MapsTo X I det) (hpi : Permutation I pi) (hg : MapsTo I I g)
    (hComp : CompositionGraph I pi g product) (hMove : Moved pi R U) :
    Value det g R delta n b v ↔ Value det product U delta n b v := by
  constructor
  · rintro ⟨d,x,y,a,hd,hdx,hxy,ha,hav⟩
    obtain ⟨z,hyz,_⟩ := hpi.1.1.2 y (hg.2 x y hxy)
    obtain ⟨c,hc,hcv⟩ := (hMove z b v).mpr ⟨y,hyz,a,ha,hav⟩
    exact ⟨d,x,z,c,hd,hdx,(hComp x z).mpr ⟨hDet.2 d x hdx,y,hxy,hyz⟩,hc,hcv⟩
  · rintro ⟨d,x,z,c,hd,hdx,hxz,hc,hcv⟩
    obtain ⟨_,y,hxy,hyz⟩ := (hComp x z).mp hxz
    obtain ⟨y',hy'z,a,ha,hav⟩ := (hMove z b v).mp ⟨c,hc,hcv⟩
    have e := hpi.2.1 y y' z hyz hy'z
    subst y'
    exact ⟨d,x,y,a,hd,hdx,hxy,ha,hav⟩

theorem slice_moved
    {X I alpha B det pi g product R U delta n F : M.Carrier .set}
    (hDet : MapsTo X I det) (hpi : Permutation I pi) (hg : MapsTo I I g)
    (hComp : CompositionGraph I pi g product) (hMove : Moved pi R U) :
    Slice alpha B det g R delta n F ↔ Slice alpha B det product U delta n F := by
  constructor
  · rintro ⟨hF,hEdge⟩
    exact ⟨hF,fun b v => (hEdge b v).trans (and_congr Iff.rfl (value_moved hDet hpi hg hComp hMove))⟩
  · rintro ⟨hF,hEdge⟩
    exact ⟨hF,fun b v => (hEdge b v).trans (and_congr Iff.rfl (value_moved hDet hpi hg hComp hMove).symm)⟩

theorem sequence_moved
    {w X I alpha B A det pi g product R U delta s : M.Carrier .set}
    (hDet : MapsTo X I det) (hpi : Permutation I pi) (hg : MapsTo I I g)
    (hComp : CompositionGraph I pi g product) (hMove : Moved pi R U) :
    Sequence w alpha B A det g R delta s ↔ Sequence w alpha B A det product U delta s := by
  constructor
  · rintro ⟨hs,hEdge⟩
    exact ⟨hs,fun n F => (hEdge n F).trans (and_congr Iff.rfl (slice_moved hDet hpi hg hComp hMove))⟩
  · rintro ⟨hs,hEdge⟩
    exact ⟨hs,fun n F => (hEdge n F).trans (and_congr Iff.rfl (slice_moved hDet hpi hg hComp hMove).symm)⟩

theorem rawPattern_moveRows (hM : FirstOrder.Theory.Models M nativeZF)
    {w N X I alpha B A E det pi g product R U pr P Q : M.Carrier .set}
    (hDet : MapsTo X I det) (hpi : Permutation I pi) (hg : MapsTo I I g)
    (hComp : CompositionGraph I pi g product) (hMove : Moved pi R U)
    (hP : RawPattern w N alpha B A E det g R pr P) (hQ : RawPattern w N alpha B A E det product U pr Q) : P = Q := by
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM N E P).mp hP.1).1.1
    ((ForcingSupportSize.native_mapsTo hM N E Q).mp hQ.1).1.1
  intro delta e
  apply (hP.2 delta e).trans
  apply Iff.trans _ (hQ.2 delta e).symm
  apply and_congr Iff.rfl
  exact exists_congr (fun s => and_congr (sequence_moved hDet hpi hg hComp hMove) Iff.rfl)

theorem complete_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root H N det alpha pi p r : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : ConstructionGermCosets.Carrier D I mul q root H)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : Moved pi p r)
    (hComplete : Complete w H N det alpha p) : Complete w H N det alpha r := by
  have hp := (hH pi).mp hpi
  obtain ⟨inv,hinv,hInv⟩ := ForcingConditionGraphs.exists_inverse hM hp.1
  have hInvH := ConstructionGermSeparation.stabilizes_inverse hM hq hp hinv hInv
  intro g hg delta hd
  have hgStab := (hH g).mp hg
  obtain ⟨diff,hdiff,hComp⟩ := ForcingConditionGraphs.exists_composition hM hinv hgStab.1
  have hDiffH := (hH diff).mpr (ConstructionGermSeparation.stabilizes_composition hM hm hJ hq hInvH hgStab hdiff hComp)
  obtain ⟨bound,hbound,hAssigned⟩ := hComplete diff hDiffH delta hd
  refine ⟨bound,hbound,?_⟩
  intro n hn hbn b hb
  obtain ⟨d,x,y,v,hdn,hdx,hxy,hyb⟩ := hAssigned n hn hbn b hb
  obtain ⟨_,z,hxz,hzy⟩ := (hComp x y).mp hxy
  exact ⟨d,x,z,v,hdn,hdx,hxz,(hMove z b v).mpr ⟨y,(hInv y z).mpr hzy,hyb⟩⟩

def rowsSentence {m : Nat} (I K C B lo hi pi p q R U : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ConstructionCohenCompatibility.moved pi p q) (.imp (ConstructionCohenRows.rows C B lo hi p R) (.imp (ConstructionCohenRows.rows C B lo hi q U) (ConstructionCohenCompatibility.moved pi R U))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionCohenRows.rows_freeClosed]

theorem rows_models {m : Nat} (I K C B lo hi pi p q R U : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rowsSentence I K C B lo hi pi p q R U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (rowsSentence I K C B lo hi pi p q R U)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionCohenCompatibility.moved_semantics hM,ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),ConstructionCohenRows.rows_semantics hM]
  exact rows_permute hM

theorem rows_kernel_certificate {m : Nat} (I K C B lo hi pi p q R U : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rowsSentence I K C B lo hi pi p q R U)) :=
  ModelTransfer.derives (fun _ hM => rows_models I K C B lo hi pi p q R U hM)

def rawSentence {m : Nat} (w N X I alpha B A E det pi g product R U pr P Q : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo g I I)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph I pi g product)) (.imp (ConstructionCohenCompatibility.moved pi R U) (.imp (ConstructionGermRawPattern.rawPattern w N alpha B A E det g R pr P) (.imp (ConstructionGermRawPattern.rawPattern w N alpha B A E det product U pr Q) (Project.Formula.extensionalEq (.bound P) (.bound Q)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCohenCompatibility.moved_freeClosed,Project.Formula.extensionalEq,ConstructionGermRawPattern.rawPattern_freeClosed]

theorem raw_models {m : Nat} (w N X I alpha B A E det pi g product R U pr P Q : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rawSentence w N X I alpha B A E det pi g product R U pr P Q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (rawSentence w N X I alpha B A E det pi g product R U pr P Q)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionCohenCompatibility.moved_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),ConstructionGermRawPattern.rawPattern_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  exact rawPattern_moveRows hM

theorem raw_kernel_certificate {m : Nat} (w N X I alpha B A E det pi g product R U pr P Q : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rawSentence w N X I alpha B A E det pi g product R U pr P Q)) :=
  ModelTransfer.derives (fun _ hM => raw_models w N X I alpha B A E det pi g product R U pr P Q hM)

def completeSentence {m : Nat} (w D I mul unit q root H N det alpha pi p r : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi p r) (.imp (ConstructionGermComplete.complete w H N det alpha p) (ConstructionGermComplete.complete w H N det alpha r))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermComplete.complete_freeClosed]

theorem complete_models {m : Nat} (w D I mul unit q root H N det alpha pi p r : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (completeSentence w D I mul unit q root H N det alpha pi p r)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (completeSentence w D I mul unit q root H N det alpha pi p r)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionCohenCompatibility.moved_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionGermComplete.complete_semantics hM]
  exact complete_permute hM

theorem complete_kernel_certificate {m : Nat} (w D I mul unit q root H N det alpha pi p r : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (completeSentence w D I mul unit q root H N det alpha pi p r)) :=
  ModelTransfer.derives (fun _ hM => complete_models w D I mul unit q root H N det alpha pi p r hM)

end PPAC.Migration.ConstructionGermRowCovariance
