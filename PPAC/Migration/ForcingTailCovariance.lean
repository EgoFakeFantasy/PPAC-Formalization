/- Pinned TailGraphs.tail_fixed/represents_same_code:152-187.
Reuse the actual internal Chain, its range contraction and literal local-name
support. Eventual comparison uses internal omega ordinals, not host Nat. -/
import PPAC.Migration.ForcingTailTransport

namespace PPAC.Migration.ForcingTailCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (EncodedCommon)
open ForcingComponentMove (Move)
open ForcingEligibleFamily (Data)
open ForcingTailCodes (At Entry ChainCode Represents)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def TailFixes (w D pi chain : M.Carrier .set) : Prop :=
  ∃ N vertex r index U A, (Project.FirstOrderSemantics.reduct M).mem N w ∧
    PureKuratowski.PairMember M N vertex chain ∧ Code vertex r index U ∧
    ForcingSupportedNames.Range D r A ∧ ForcingLabelPermutations.Fixes A pi

theorem tail_fixed {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c act ai mul q zero root vertices chain bound : M.Carrier .set}
    (hData : ForcingProductCovariance.SystemData v I K B w G F mu pi inv c act ai)
    (hChain : ConstructionComponentCofinal.Chain w (v 0) I mul q zero root vertices chain)
    (hTail : TailFixes w (v 0) pi chain) :
    ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ i vertex sigma,
      (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
      PureKuratowski.PairMember M i vertex chain → Entry v G F bound vertex sigma →
      Move (v 0) I mul q pi vertex vertex ∧ ForcingStabilizer.Action (v 6) act sigma sigma := by
  obtain ⟨N,vertexN,rN,indexN,UN,AN,hN,hNv,hCodeN,hAN,hFixN⟩ := hTail
  refine ⟨N,hN,?_⟩
  intro i vertex sigma _ hNi hiv hEntry
  obtain ⟨n,rN',indexN',UN',r,index,U,hCodeN',hCode,hrN,hr,hArrow⟩ := hChain.2.2.1 N i vertexN vertex hNi hNv hiv
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCodeN hCodeN'
  obtain ⟨r',index',U',A,H,hCode',hA,hH,hName⟩ := hEntry
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
  have hFix : ForcingLabelPermutations.Fixes A pi := fun x hx =>
    hFixN x ((hAN x).mpr (ConstructionDescentPlacement.range_antitone
      ⟨n,hrN.2.2.1 n hArrow.1,hArrow.2.1⟩ ((hA x).mp hx)))
  have hMove : Move (v 0) I mul q pi vertex vertex :=
    ⟨r,index,U,r,hCode,hCode,hr,hr,ForcingComponentMove.root_fixed hData.2.2.1 hr.1 hA hFix⟩
  have hpiH := (hH pi).mpr ⟨(hData.2.1 pi).mpr hData.2.2.1,hFix⟩
  obtain ⟨_,_,_,_,_,_,_,hAct,_,_⟩ := hData
  exact ⟨hMove,hName.2 pi hpiH act ((ForcingProductFamily.mapRel_action v pi act).mpr hAct)⟩

theorem represents_same_code (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps
      objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (v 0) mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (v 0) mul)
    (hData : ForcingProductCovariance.SystemData v I K B w G F mu pi inv c act ai)
    (hBound : ForcingSupportedNames.Supported v G bound)
    (hq : Injection (v 0) I q) (hFix : CompositionGraph (v 0) pi q q)
    (hObjMap : MapsTo (v 4) objImage objects) (hTargetMap : MapsTo (v 4) targetImage targets)
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTarget : ForcingEligibleFamily.Family R Hdom env v G F mul gT q bound labels E (v 4) targets)
    (hAppMap : MapsTo (v 4) appImage apps)
    (hFamily : ForcingEligibleReindex.Family R Hdom env v G F mul g gT q bound labels E pi act apps)
    (hPres : ForcingReindexSystem.PreservesAvailability (v 0) mul pi objects maps targets targetMaps apps)
    (hAll : ForcingComponentGluing.AllFiberMaps (v 0) I mul q objects maps root Q gluePr)
    (hAllT : ForcingComponentGluing.AllFiberMaps (v 0) I mul q targets targetMaps root Z gluePrT)
    (hNat : ForcingGluedTransport.Naturality (v 0) I mul q pi objects maps targets targetMaps apps root Q Z gluePr gluePrT phi)
    (hPhi : Injection Q Z phi) (hRoot : Move (v 0) I mul q pi root rootT)
    (hStab : EncodedCommon (v 0) I mul q root rootT)
    (hbbT : PureKuratowski.PairMember M b bT phi)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w (v 0) I mul q zero root vertices chain)
    (hCode : ChainCode v G F bound w names chain code)
    (hTail : TailFixes w (v 0) pi chain) :
    Represents R Hdom env v I G F mul gT q bound labels E targets targetMaps root gluePrT w chain code bT ↔
      Represents R Hdom env v I G F mul g q bound labels E objects maps root gluePr w chain code b := by
  obtain ⟨N,hN,hFixed⟩ := tail_fixed hData hChain hTail (bound := bound)
  have hAt : ∀ i vertex sigma, (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
      PureKuratowski.PairMember M i vertex chain → PureKuratowski.PairMember M i sigma code →
      (At R Hdom env v I G F mul gT q bound labels E targets targetMaps root gluePrT vertex sigma bT ↔
        At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b) := by
    intro i vertex sigma hi hNi hiv his
    obtain ⟨vertex',hiv',hEntry⟩ := hCode.2 i sigma his
    have he := ForcingConditionGraphs.function_unique hChain.1.1 hiv hiv'
    subst vertex'
    obtain ⟨hMove,hAct⟩ := hFixed i vertex sigma hi hNi hiv hEntry
    have hName : ForcingNames.IsName (v 6) sigma := by
      obtain ⟨_,_,_,_,_,_,_,_,h⟩ := hEntry
      exact ForcingHS.isName h.1.1
    exact ForcingTailTransport.at_transport_iff hM hm hJ hData hBound hq hFix hObjMap hTargetMap
      hObj hTarget hAppMap hFamily hPres hAll hAllT hNat hPhi hRoot hStab hMove hName hAct hbbT
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM)
  have hMax : ∀ L, (Project.FirstOrderSemantics.reduct M).mem L w →
      ∃ J, (Project.FirstOrderSemantics.reduct M).mem J w ∧ NatLe N J ∧ NatLe L J := by
    intro L hL
    rcases ConstructionFractionOrder.nat_compare hM hw hN hL with he | hn | hl
    · exact ⟨L,hL,Or.inl he,Or.inl rfl⟩
    · exact ⟨L,hL,Or.inr hn,Or.inl rfl⟩
    · exact ⟨N,hN,Or.inl rfl,Or.inr hl⟩
  constructor
  · rintro ⟨L,hL,hWorks⟩
    obtain ⟨J,hJ,hNJ,hLJ⟩ := hMax L hL
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    obtain ⟨vertex,sigma,hiv,his,hAtT⟩ := hWorks i hi (ZF.eqOrMem_trans (ord i hi) hLJ hJi)
    exact ⟨vertex,sigma,hiv,his,(hAt i vertex sigma hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) hiv his).mp hAtT⟩
  · rintro ⟨L,hL,hWorks⟩
    obtain ⟨J,hJ,hNJ,hLJ⟩ := hMax L hL
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    obtain ⟨vertex,sigma,hiv,his,hAtS⟩ := hWorks i hi (ZF.eqOrMem_trans (ord i hi) hLJ hJi)
    exact ⟨vertex,sigma,hiv,his,(hAt i vertex sigma hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) hiv his).mpr hAtS⟩

def tailFixes {m : Nat} (w D pi chain : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 5) (.bound w.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ.succ.succ.succ 5 4)) (.conj (ConstructionComponentCarrier.code 4 3 2 1) (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id (ForcingLabelPermutations.fixes 0 pi.succ.succ.succ.succ.succ.succ))))))))))))

theorem tailFixes_freeClosed {m : Nat} (w D pi chain : Fin m) : (tailFixes w D pi chain).FreeClosed := by
  simp -implicitDefEqProofs [tailFixes,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem tailFixes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D pi chain : Fin m) :
    Project.Formula.satisfies env (tailFixes w D pi chain) ↔
      TailFixes (env.bound w) (env.bound D) (env.bound pi) (env.bound chain) := by
  simp only [tailFixes,TailFixes,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixes_semantics (M := M)]
  rfl

def covarianceSentence {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) objImage))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets (rho 4) targetImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family R Hdom base rho G F mul g q bound labels E (rho 4) objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family R Hdom base rho G F mul gT q bound labels E (rho 4) targets))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps (rho 4) appImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleReindex.family R Hdom base rho G F mul g gT q bound labels E pi act apps))
    (.imp (ForcingReindexSystem.preservesAvailability (rho 0) mul pi objects maps targets targetMaps apps)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q objects maps root Q gluePr)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q targets targetMaps root Z gluePrT)
    (.imp (ForcingGluedTransport.naturality (rho 0) I mul q pi objects maps targets targetMaps apps root Q Z gluePr gluePrT phi)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection phi Q Z))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi root rootT)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root rootT)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge phi b bT))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain code)
    (.imp (tailFixes w (rho 0) pi chain)
    (.iff (ForcingTailCodes.represents R Hdom base rho I G F mul gT q bound labels E targets targetMaps root gluePrT w chain code bT)
      (ForcingTailCodes.represents R Hdom base rho I G F mul g q bound labels E objects maps root gluePr w chain code b))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingReindexSystem.preservesAvailability_freeClosed,
      ForcingComponentGluing.allFiberMaps_freeClosed,ForcingGluedTransport.naturality_freeClosed,
      ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.chainCode_freeClosed,tailFixes_freeClosed,
      ForcingTailCodes.represents_freeClosed]

theorem covariance_models {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (covarianceSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro boundEnv
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleReindex.family_semantics (M := M),ForcingReindexSystem.preservesAvailability_semantics hM,
    ForcingComponentGluing.allFiberMaps_semantics hM,ForcingGluedTransport.naturality_semantics hM,
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    KuratowskiZF.source_edge,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.chainCode_semantics hM,
    tailFixes_semantics hM,ForcingTailCodes.represents_semantics hM]
  exact represents_same_code hM (R := R) (Hdom := Hdom)
    (env := fun j => boundEnv (base j)) (v := fun j => boundEnv (rho j))

theorem covariance_kernel_certificate {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code)) :=
  ModelTransfer.derives (fun _ hM => covariance_models R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT gluePr gluePrT Q Z phi b bT zero vertices chain names code hM)

end PPAC.Migration.ForcingTailCovariance
