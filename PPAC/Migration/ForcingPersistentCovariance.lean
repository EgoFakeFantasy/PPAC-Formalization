/- Pinned PersistentCodes.ChainCode.same_covariance:270-286.
Use the actual condition permutation and literal tail fixation. All bounds
and indices belong to internal omega. No invariance of the code wellorder. -/
import PPAC.Migration.ForcingPersistentWorks

namespace PPAC.Migration.ForcingPersistentCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingProductSymmetry (orderFormula)
open ForcingPrincipalFilter (EqF)
open ForcingPersistentCodes (Same)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem eqF_transport_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul act : Fin k)
    {I K B w one pi ac d d' r r' sigma tau sigma' tau' : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hpi : Permutation I pi)
    (hAct : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi (env act))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d d' ac)
    (hr : Injection (env (rho 0)) I r) (hr' : Injection (env (rho 0)) I r')
    (hComp : CompositionGraph (env (rho 0)) pi r r')
    (hs : ForcingStabilizer.Action (env (rho 6)) (env act) sigma sigma')
    (ht : ForcingStabilizer.Action (env (rho 6)) (env act) tau tau') :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d' r' sigma' tau' ↔
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau := by
  have hac := ForcingLocalTransport.part_permutation hc
  have hd := ForcingConditionGraphs.function_input hac.1.1 hdd
  have hd' := hac.1.2 d d' hdd
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,_,_,ht,_,_,hGraph⟩ := hc
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  obtain ⟨g,hg⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) d
  obtain ⟨g',hg'⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) d'
  have hImage := ForcingPrincipalFilter.principal_move hac ho hdd hg hg'
  have hRel : ∀ x y, ForcingMapConditions.MapRel (ForcingConditionAction.actFormula (0 : Fin 2) 1)
      (Source.SetLanguage.args2 (env (rho 6)) (env act)) x y ↔
      ForcingMapConditions.MapRel (ForcingConditionAction.actFormula (rho 6) act) env x y := by
    intro x y
    exact (ForcingConditionAction.relation_semantics _ _ _ x y).trans
      (ForcingConditionAction.relation_semantics env (rho 6) act x y).symm
  have hs' := (ForcingMapLaws.mapping_congr hRel sigma sigma').mp hs
  have ht' := (ForcingMapLaws.mapping_congr hRel tau tau').mp ht
  exact (ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd' hr' hg').symm.trans
    ((ForcingLocalTransport.local_eq_transport_iff hM env rho mul act hp hpi hAct hc
      (ForcingPrincipalFilter.principal_filter hd hg) hImage hr hr' hComp hs' ht').trans
      (ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd hr hg))

theorem same_covariance (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul act : Fin k)
    {I K B w G F mu pi inv c ai one q zero root vertices chain bound names a b ac d d' : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env act) ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (ha : ForcingTailCodes.ChainCode (fun j => env (rho j)) G F bound w names chain a)
    (hb : ForcingTailCodes.ChainCode (fun j => env (rho j)) G F bound w names chain b)
    (hTail : ForcingTailCovariance.TailFixes w (env (rho 0)) pi chain)
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d d' ac) :
    Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d' a b ↔
      Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b := by
  obtain ⟨N,hN,hFixed⟩ := ForcingTailCovariance.tail_fixed hData hChain hTail (bound := bound)
  have hPoint : ∀ i vertex sigma tau r index U,
      (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
      PureKuratowski.PairMember M i vertex chain → PureKuratowski.PairMember M i sigma a →
      PureKuratowski.PairMember M i tau b → ConstructionComponentCarrier.Code vertex r index U →
      (EqF (orderFormula (rho 0) mul) env (env (rho 6)) d' r sigma tau ↔
       EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau) := by
    intro i vertex sigma tau r index U hi hNi hiv his hit hCode
    obtain ⟨va,hiva,hEa⟩ := ha.2 i sigma his
    obtain ⟨vb,hivb,hEb⟩ := hb.2 i tau hit
    have hva := ForcingConditionGraphs.function_unique hChain.1.1 hiv hiva
    have hvb := ForcingConditionGraphs.function_unique hChain.1.1 hiv hivb
    subst va; subst vb
    obtain ⟨hMove,hSigma⟩ := hFixed i vertex sigma hi hNi hiv hEa
    have hTau := (hFixed i vertex tau hi hNi hiv hEb).2
    obtain ⟨r0,index0,U0,r1,hCode0,hCode1,hr0,hr1,hComp⟩ := hMove
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
    obtain ⟨rfl,_,_⟩ := ConstructionComponentCarrier.code_injective hCode hCode1
    obtain ⟨hp,_,hpi,_,_,_,_,hAct,_,_⟩ := hData
    exact eqF_transport_iff hM env rho mul act hm hp hpi hAct hc hdd hr0.1 hr1.1 hComp hSigma hTau
  have hJoin : ∀ L, (Project.FirstOrderSemantics.reduct M).mem L w →
      ∃ J, (Project.FirstOrderSemantics.reduct M).mem J w ∧ NatLe N J ∧ NatLe L J := by
    intro L hL
    rcases ConstructionFractionOrder.nat_compare hM hw hN hL with he | hnl | hln
    · exact ⟨L,hL,Or.inl he,Or.inl rfl⟩
    · exact ⟨L,hL,Or.inr hnl,Or.inl rfl⟩
    · exact ⟨N,hN,Or.inl rfl,Or.inr hln⟩
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM)
  constructor
  · rintro ⟨L,hL,h⟩
    obtain ⟨J,hJ,hNJ,hLJ⟩ := hJoin L hL
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    obtain ⟨vertex,sigma,tau,r,index,U,hiv,his,hit,hCode,heq⟩ := h i hi (ZF.eqOrMem_trans (ord i hi) hLJ hJi)
    exact ⟨vertex,sigma,tau,r,index,U,hiv,his,hit,hCode,
      (hPoint i vertex sigma tau r index U hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) hiv his hit hCode).mp heq⟩
  · rintro ⟨L,hL,h⟩
    obtain ⟨J,hJ,hNJ,hLJ⟩ := hJoin L hL
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    obtain ⟨vertex,sigma,tau,r,index,U,hiv,his,hit,hCode,heq⟩ := h i hi (ZF.eqOrMem_trans (ord i hi) hLJ hJi)
    exact ⟨vertex,sigma,tau,r,index,U,hiv,his,hit,hCode,
      (hPoint i vertex sigma tau r index U hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) hiv his hit hCode).mpr heq⟩


def covarianceSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain b)
    (.imp (ForcingTailCovariance.tailFixes w (rho 0) pi chain)
    (.existsE (.conj (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1).succ (rho 2).succ (rho 3).succ pi.succ 0)) (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0)) (.iff (ForcingPersistentCodes.same (orderFormula (rho 0) mul) (fun j => j.succ.succ.succ) (rho 6).succ.succ.succ w.succ.succ.succ chain.succ.succ.succ 0 a.succ.succ.succ b.succ.succ.succ) (ForcingPersistentCodes.same (orderFormula (rho 0) mul) (fun j => j.succ.succ.succ) (rho 6).succ.succ.succ w.succ.succ.succ chain.succ.succ.succ 1 a.succ.succ.succ b.succ.succ.succ))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.chainCode_freeClosed,
      ForcingTailCovariance.tailFixes_freeClosed,ForcingPersistentCodes.same_freeClosed]
    exact Project.Formula.isOmega_freeClosed _ rfl

theorem covariance_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.chainCode_semantics hM,
    ForcingTailCovariance.tailFixes_semantics hM,ForcingLocalTransport.cohenPart_semantics (M := M),
    ForcingPersistentCodes.same_semantics hM]
  intro hm hData hw hChain ha hb hTail
  have hDataCopy := hData
  obtain ⟨_,_,_,_,_,_,_,hAct,_,_⟩ := hDataCopy
  obtain ⟨ac,hc⟩ := ForcingLocalTransport.part_of_action hAct
  exact ⟨ac,hc,fun d d' hdd => same_covariance hM env rho mul act hm hData hw hChain ha hb hTail hc hdd⟩

theorem covariance_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b)) :=
  ModelTransfer.derives (fun _ hM => covariance_models rho I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names a b hM)

-- Source works_covariance first transfers representation in each actual
-- principal quotient. Both complete presentations remain explicit here.
theorem represented_transport_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT
      oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (v 0) mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (v 0) mul)
    (hData : ForcingProductCovariance.SystemData v I K B w G F mu pi inv c act ai)
    (hBound : ForcingSupportedNames.Supported v G bound)
    (hq : Injection (v 0) I q) (hFix : CompositionGraph (v 0) pi q q)
    (hg : ForcingPrincipalFilter.Principal (v 3) d g)
    (hgT : ForcingPrincipalFilter.Principal (v 3) dT gT)
    (hB : ForcingPersistentWorks.Bundle R Hdom env v I G F mul g q bound labels E root oi objects S mi maps P Q pr)
    (hBT : ForcingPersistentWorks.Bundle R Hdom env v I G F mul gT q bound labels E root oiT targets ST miT targetMaps PT Z prT)
    (hAppMap : ForcingSupportSize.MapsTo (v 4) appImage apps)
    (hFamily : ForcingEligibleReindex.Family R Hdom env v G F mul g gT q bound labels E pi act apps)
    (hPres : ForcingReindexSystem.PreservesAvailability (v 0) mul pi objects maps targets targetMaps apps)
    (hAll : ForcingComponentGluing.AllFiberMaps (v 0) I mul q objects maps root Q pr)
    (hAllT : ForcingComponentGluing.AllFiberMaps (v 0) I mul q targets targetMaps root Z prT)
    (hNat : ForcingGluedTransport.Naturality (v 0) I mul q pi objects maps targets targetMaps apps root Q Z pr prT phi)
    (hPhi : Injection Q Z phi)
    (hOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Z →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Q ∧ PureKuratowski.PairMember M x y phi)
    (hRoot : ForcingComponentMove.Move (v 0) I mul q pi root rootT)
    (hStab : ConstructionComponentCofinal.EncodedCommon (v 0) I mul q root rootT)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w (v 0) I mul q zero root vertices chain)
    (hCode : ForcingTailCodes.ChainCode v G F bound w names chain code)
    (hTail : ForcingTailCovariance.TailFixes w (v 0) pi chain) :
    ForcingPersistentWorks.Represented R Hdom env v I G F mul q bound labels E root w chain dT code ↔
      ForcingPersistentWorks.Represented R Hdom env v I G F mul q bound labels E root w chain d code := by
  rw [ForcingPersistentWorks.represented_iff hM hgT hBT,ForcingPersistentWorks.represented_iff hM hg hB]
  have transfer : ∀ b bT, PureKuratowski.PairMember M b bT phi →
      (ForcingTailCodes.Represents R Hdom env v I G F mul gT q bound labels E targets targetMaps root prT w chain code bT ↔
       ForcingTailCodes.Represents R Hdom env v I G F mul g q bound labels E objects maps root pr w chain code b) := by
    intro b bT hbbT
    exact ForcingTailCovariance.represents_same_code hM hm hJ hData hBound hq hFix
      hB.1 hBT.1 hB.2.1 hBT.2.1 hAppMap hFamily hPres hAll hAllT hNat hPhi hRoot hStab hbbT hw hChain hCode hTail
  constructor
  · rintro ⟨bT,hbT,hRep⟩
    obtain ⟨b,hb,hbbT⟩ := hOnto bT hbT
    exact ⟨b,hb,(transfer b bT hbbT).mp hRep⟩
  · rintro ⟨b,hb,hRep⟩
    obtain ⟨bT,hbbT,_⟩ := hPhi.1.1.2 b hb
    exact ⟨bT,hPhi.1.2 b bT hbbT,(transfer b bT hbbT).mpr hRep⟩


def representedSentence {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ForcingPrincipalFilter.principal (rho 3) d g)
    (.imp (ForcingPrincipalFilter.principal (rho 3) dT gT)
    (.imp (ForcingPersistentWorks.bundle R Hdom base rho I G F mul g q bound labels E root oi objects S mi maps P Q pr)
    (.imp (ForcingPersistentWorks.bundle R Hdom base rho I G F mul gT q bound labels E root oiT targets ST miT targetMaps PT Z prT)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps (rho 4) appImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleReindex.family R Hdom base rho G F mul g gT q bound labels E pi act apps))
    (.imp (ForcingReindexSystem.preservesAvailability (rho 0) mul pi objects maps targets targetMaps apps)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q objects maps root Q pr)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q targets targetMaps root Z prT)
    (.imp (ForcingGluedTransport.naturality (rho 0) I mul q pi objects maps targets targetMaps apps root Q Z pr prT phi)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection phi Q Z))
    (.imp (.forallE (.imp (.mem (.bound 0) (.bound Z.succ)) (.existsE (.conj (.mem (.bound 0) (.bound Q.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge phi.succ.succ 0 1))))))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi root rootT)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root rootT)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain code)
    (.imp (ForcingTailCovariance.tailFixes w (rho 0) pi chain)
    (.iff (ForcingPersistentWorks.represented R Hdom base rho I G F mul q bound labels E root w chain dT code) (ForcingPersistentWorks.represented R Hdom base rho I G F mul q bound labels E root w chain d code))))))))))))))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingPrincipalFilter.principal_freeClosed,
      ForcingPersistentWorks.bundle_freeClosed,ForcingReindexSystem.preservesAvailability_freeClosed,
      ForcingComponentGluing.allFiberMaps_freeClosed,ForcingGluedTransport.naturality_freeClosed,
      ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.chainCode_freeClosed,
      ForcingTailCovariance.tailFixes_freeClosed,ForcingPersistentWorks.represented_freeClosed]
    exact Project.Formula.isOmega_freeClosed _ rfl

theorem represented_models {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (representedSentence R Hdom base rho I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro boundEnv
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingPrincipalFilter.principal_semantics,ForcingPersistentWorks.bundle_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleReindex.family_semantics (M := M),
    ForcingReindexSystem.preservesAvailability_semantics hM,ForcingComponentGluing.allFiberMaps_semantics hM,
    ForcingGluedTransport.naturality_semantics hM,ForcingComponentMove.move_semantics hM,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.chainCode_semantics hM,ForcingTailCovariance.tailFixes_semantics hM,
    ForcingPersistentWorks.represented_semantics hM]
  exact represented_transport_iff hM (R := R) (Hdom := Hdom)
    (env := fun j => boundEnv (base j)) (v := fun j => boundEnv (rho j))

theorem represented_kernel_certificate {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (representedSentence R Hdom base rho I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT)) :=
  ModelTransfer.derives (fun _ hM => represented_models R Hdom base rho I K B w G F mu pi inv c act ai mul one g gT q bound labels E root rootT oi objects S mi maps P Q pr oiT targets ST miT targetMaps PT Z prT appImage apps phi zero vertices chain names code d dT hM)

end PPAC.Migration.ForcingPersistentCovariance
