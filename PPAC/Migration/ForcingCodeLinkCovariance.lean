/- Pinned QuotientActions.links_permute:469 and tail_eq_permute:487.
Direct consumers: GermSelectors.preliminary_permute:143. Reuse actual tail
fixation, EqF transport, moved arrows and supporting-root reflection. -/
import PPAC.Migration.ForcingCodeLinkClosure
import PPAC.Migration.ForcingTailGroup
import PPAC.Migration.ForcingLabelSystem

namespace PPAC.Migration.ForcingCodeLinkCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow)
open ForcingPrincipalFilter (EqF)
open ForcingCodeLinks (Links)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem join (hM : FirstOrder.Theory.Models M nativeZF) {w N L : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hN : (Project.FirstOrderSemantics.reduct M).mem N w)
    (hL : (Project.FirstOrderSemantics.reduct M).mem L w) :
    ∃ J, (Project.FirstOrderSemantics.reduct M).mem J w ∧ NatLe N J ∧ NatLe L J := by
  rcases ConstructionFractionOrder.nat_compare hM hw hN hL with he | hnl | hln
  · exact ⟨L,hL,Or.inl he,Or.inl rfl⟩
  · exact ⟨L,hL,Or.inr hnl,Or.inl rfl⟩
  · exact ⟨N,hN,Or.inl rfl,Or.inr hln⟩

theorem links_permute (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (ha : ForcingTailCodes.ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env a))
    (hTail : ForcingTailCovariance.TailFixes (env w) (env (rho 0)) (env pi) (env chain))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env vertex) (env movedVertex))
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) (env tau) (env movedTau))
    (hLinks : Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) (env tau) (env a)) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env movedD) (env movedVertex) (env movedTau) (env a) := by
  obtain ⟨L,hL,hFixed⟩ := ForcingTailCovariance.tail_fixed hData hChain hTail (bound := env bound)
  have hMoveCopy := hMove
  obtain ⟨r,idx,U,r',hv,hv',hr,hr',hComp⟩ := hMoveCopy
  obtain ⟨s,idxS,US,hvS,N,hN,hLinks⟩ := hLinks
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hvS
  obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
  refine ⟨r',idx,U,hv',J,hJ,?_⟩
  intro i hi hJi
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
  obtain ⟨vi,sigma,n,hvi,hsi,hArrow,heq⟩ := hLinks i hi (ZF.eqOrMem_trans ord hNJ hJi)
  obtain ⟨vi',hvi',hEntry⟩ := ha.2 i sigma hsi
  have hev := ForcingConditionGraphs.function_unique hChain.1.1 hvi hvi'
  subst vi'
  obtain ⟨hFixedVertex,hSigma⟩ := hFixed i vi sigma hi (ZF.eqOrMem_trans ord hLJ hJi) hvi hEntry
  obtain ⟨hp,_,hpi,_,_,_,_,hAct,_,_⟩ := hData
  exact ⟨vi,sigma,n,hvi,hsi,ForcingComponentMove.move_arrow hMove hFixedVertex hArrow,
    (ForcingPersistentCovariance.eqF_transport_iff hM env rho mul act hm hp hpi hAct hc hdd hr.1 hr'.1 hComp hSigma hTau).mpr heq⟩

theorem tail_eq_permute (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group))
    (hMember : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env group))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hCode : Code (env root) (env r) (env idx) (env U))
    (hTau : ForcingSupportedNames.Supported (fun j => env (rho j)) (env group) (env tau))
    (hSigma : ForcingSupportedNames.Supported (fun j => env (rho j)) (env group) (env sigma))
    (he : EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env r) (env tau) (env sigma)) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env movedD) (env r) (env tau) (env sigma) := by
  have hTail := ((hGroup (env pi)).mp hMember).2
  obtain ⟨hp,hG,hpi,_,_,_,_,hAct,_,hF⟩ := hData
  obtain ⟨_,movedRoot,hMove,_⟩ := ForcingTailGroup.fixes_mem_stabilizer hM hm hJoins hq hAq hpi hChain hTail
  have hMoveCopy := hMove
  obtain ⟨r0,idx0,U0,rT,hCode0,hCodeT,hr0,hrT,hComp⟩ := hMoveCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
  have hMap := (ForcingProductFamily.mapRel_action (fun j => env (rho j)) (env pi) (env act)).mpr hAct
  have heT := (ForcingPersistentCovariance.eqF_transport_iff hM env rho mul act hm hp hpi hAct hc hdd hr0.1 hrT.1 hComp
    (hTau (env pi) hMember (env act) hMap) (hSigma (env pi) hMember (env act) hMap)).mpr he
  have hTailCopy := hTail
  obtain ⟨N,vN,rN,idxN,UN,AN,hN,hNv,hCodeN,hAN,hFixN⟩ := hTailCopy
  obtain ⟨J,hJ,hNJ,hZJ⟩ := join hM hw hN (ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1)
  obtain ⟨vJ,hJv,_⟩ := hChain.1.1.2 J hJ
  obtain ⟨n,hArrow⟩ := hChain.2.2.1 (env zero) J (env root) vJ hZJ hChain.2.1 hJv
  have hArrowCopy := hArrow
  obtain ⟨r0,idx0,U0,rJ,idxJ,UJ,hCode0,hCodeJ,_,hrJ,hArr⟩ := hArrowCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
  obtain ⟨AJ,hAJ⟩ := ForcingLabelSystem.exists_range hM hrJ.1
  obtain ⟨HJ,hHJ⟩ := ForcingLabelPermutations.exists_fixing hM (env G) AJ
  have hFixJ := ForcingTailGroup.fixes_later hChain hNJ hNv hJv hCodeN hCodeJ hAN hAJ hFixN
  have hSelf : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) vJ vJ :=
    ⟨rJ,idxJ,UJ,rJ,hCodeJ,hCodeJ,hrJ,hrJ,ForcingComponentMove.root_fixed hpi hrJ.1 hAJ hFixJ⟩
  have hMovedArrow := ForcingComponentMove.move_arrow hMove hSelf hArrow
  obtain ⟨rT',idxT',UT',rJ',idxJ',UJ',hCodeT',hCodeJ',_,_,hMovedArr⟩ := hMovedArrow
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCodeT hCodeT'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCodeJ hCodeJ'
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset HJ (env group) := by
    intro g hg
    obtain ⟨hgG,hgFix⟩ := (hHJ g).mp hg
    exact (hGroup g).mpr ⟨hgG,J,vJ,rJ,idxJ,UJ,AJ,hJ,hJv,hCodeJ,hAJ,hgFix⟩
  have hTauJ : ForcingSupportedNames.Supported (fun j => env (rho j)) HJ (env tau) :=
    fun g hg A hA => hTau g (hSub g hg) A hA
  have hSigmaJ : ForcingSupportedNames.Supported (fun j => env (rho j)) HJ (env sigma) :=
    fun g hg A hA => hSigma g (hSub g hg) A hA
  have hd' := (ForcingLocalTransport.part_permutation hc).1.2 (env d) (env movedD) hdd
  obtain ⟨zT,hzT,heT⟩ := heT
  obtain ⟨zJ,hzJ⟩ := ForcingSupportingRoot.exists_code hM (env movedD) rJ
  have heJ := ForcingOrdinalRoot.eq_at_root hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hp hG hF
    hrJ.1 hAJ hHJ hrT.1 ⟨n,hrT.2.2.1 n hMovedArr.1,hMovedArr.2.1⟩ ((hp.2.2.1 (env movedD)).mp hd') hzT hzJ hTauJ hSigmaJ heT
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM (env movedD) (env r)
  exact ⟨z,hz,ForcingAtomicBasic.eq_mono hM
    (ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2)
    (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 (env movedD)).mp hd') hr0.1 hz)
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul z zJ).mpr ((ForcingSupportingRoot.code_le hz hzJ).mpr
      ⟨fun _ h => h,n,hr0.2.2.1 n hArr.1,hArr.2.1⟩)) heJ⟩


def linksSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingTailCovariance.tailFixes w (rho 0) pi chain)
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi vertex movedVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act tau movedTau))
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a)
    (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain movedD movedVertex movedTau a))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,
      ForcingTailCovariance.tailFixes_freeClosed,
      ForcingComponentMove.move_freeClosed,
      ForcingCodeLinks.links_freeClosed]

theorem links_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (linksSentence rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductCovariance.systemData_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.chainCode_semantics hM,
    ForcingTailCovariance.tailFixes_semantics hM,
    ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,
    ForcingStabilizer.action_semantics (M := M),
    ForcingCodeLinks.links_semantics hM]
  exact links_permute hM env rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau

theorem links_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (linksSentence rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau)) :=
  ModelTransfer.derives (fun _ hM => links_models rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a ac d movedD vertex movedVertex tau movedTau hM)


def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailGroup.tailGroup w (rho 0) G chain group)
    (.imp (.mem (.bound pi) (.bound group))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho group tau))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho group sigma))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d r tau sigma)
    (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) movedD r tau sigma)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingPrincipalFilter.eqF_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailGroup.tailGroup_semantics hM,
    Project.Formula.satisfies_mem_iff,
    ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,
    ForcingSupportedNames.supported_semantics (M := M),
    ForcingPrincipalFilter.eqF_semantics hM]
  exact tail_eq_permute hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (equalitySentence rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma)).mp
      (equality_models rho w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q Aq zero root vertices chain group ac d movedD r idx U tau sigma hL hChoice)

end PPAC.Migration.ForcingCodeLinkCovariance
