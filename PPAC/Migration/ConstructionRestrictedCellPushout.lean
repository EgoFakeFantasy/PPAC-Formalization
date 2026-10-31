/- Pinned CellCuts.restrict_selected.work: identify the SAME conservative
simulation with the retained successor, then map_apex/change_left the full
pushout. Actual Probe/Merger simulation producers are imported, not assumed
as new foundational axioms. Their selected-record assembly is the consumer. -/
import PPAC.Migration.ConstructionRestrictedCellSimulation

namespace PPAC.Migration.ConstructionRestrictedCellPushout
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom IsPushout)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionCellGeneration (Submonoid Generated ClosureMember)
open ConstructionConservativeHull (ProductGraph)
open ConstructionAttachmentCoefficients (OldFixed)
open ForcingSupportSize (MapsTo Injection)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (IdentityGraph InverseGraph function_input function_unique)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Only ordinary submonoid closure is needed at an isomorphism range.
Reuse the existing restricted unit and associativity; cancellation is inherited. -/
theorem monoid_restrict {V GV e S GS : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hS : Submonoid V GV e S)
    (hGS : ProductGraph S GV GS) : LeftCancelMonoid S GS e := by
  refine ⟨ConstructionCellGeneration.unit_restrict hv.1 hS hGS,?_,
    ConstructionCellGeneration.associative_restrict hv.2.2 hS hGS⟩
  intro x hx
  refine ⟨?_,?_,?_⟩
  · intro y hy
    obtain ⟨z,_,hp⟩ := (hv.2.1 x (hS.1 x hx)).1 y (hS.1 y hy)
    exact ⟨z,hS.2.2 x y z hx hy hp,(hGS x y z).mpr ⟨hx,hy,hp⟩⟩
  · intro y z t hy hp hq
    exact (hv.2.1 x (hS.1 x hx)).2.1 y z t (hS.1 y hy)
      ((hGS x y z).mp hp).2.2 ((hGS x y t).mp hq).2.2
  · intro y z t hy hz hp hq
    exact (hv.2.1 x (hS.1 x hx)).2.2 y z t (hS.1 y hy) (hS.1 z hz)
      ((hGS x y t).mp hp).2.2 ((hGS x z t).mp hq).2.2

def Result (D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc
    embedding pairsT GT invF pairsNext GNext invEmbedding inclusion : M.Carrier .set) : Prop :=
  ConstructionProbeLetters.Representatives T T pairsT ∧ MapsTo pairsT T GT ∧ ProductGraph T GV GT ∧
    LeftCancelMonoid T GT e ∧ Hom W T G GT unit e F ∧ Hom T W GT G e unit invF ∧ InverseGraph F invF ∧
    ConstructionProbeLetters.Representatives next next pairsNext ∧ MapsTo pairsNext next GNext ∧ ProductGraph next GV GNext ∧
    LeftCancelMonoid next GNext e ∧ Hom W0 next G0 GNext unit0 e embedding ∧
    Hom next W0 GNext G0 e unit0 invEmbedding ∧ InverseGraph embedding invEmbedding ∧
    Hom W0 V G0 GV unit0 e embedding ∧ Injection W0 V embedding ∧
    NodeMap H F embedding ∧ OldFixed O0 embedding ∧ Range W0 embedding next ∧
    Hom next T GNext GT e e inclusion ∧ IdentityGraph next inclusion ∧
    IsPushout D next T mul GNext GT e e e inc inc inclusion old

/-- Source work with all original old/generator graphs fixed. Construct both
range multiplication graphs and both internal inverses, then transfer the
universal property. No extra closure/factor/join premise is imposed on the
range: ordinary generated submonoid closure suffices. -/
theorem work (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hm0 : LeftCancelMonoid W0 G0 unit0) (hv : LeftCancelMonoid V GV e)
    (hO : MapsTo D W O) (hO0 : MapsTo cut W0 O0) (hP0 : MapsTo I W0 P0)
    (hF : Hom W V G GV unit e F) (hFInj : Injection W V F) (hRange : Range W F T)
    (hH : Hom W0 W G0 G unit0 unit H) (hHInj : Injection W0 W H)
    (hPush : IsPushout D W0 W mul G0 G e unit0 unit O0 inc H O)
    (hFixed : OldFixed O F) (hOld : IdentityGraph D old) (hInc : IdentityGraph cut inc)
    (hGenerated : Generated cut I W0 G0 unit0 O0 P0)
    (hGen : NodeMap P F generators) (hGen0 : NodeMap P0 H P) (hGenerators : MapsTo I retained generators)
    (hRet : Submonoid V GV e retained)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D)
    (hNext : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T)
    (hWords : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y retained →
      (Project.FirstOrderSemantics.reduct M).mem y T → ¬ (Project.FirstOrderSemantics.reduct M).mem y D →
      ClosureMember I V GV e old generators cut y) :
    ∃ embedding pairsT GT invF pairsNext GNext invEmbedding inclusion,
      Result D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc
        embedding pairsT GT invF pairsNext GNext invEmbedding inclusion := by
  obtain ⟨embedding,hEmbedding,hComp⟩ := ConstructionPushoutPasting.exists_hom_comp hM hH hF
  have hEmbInj : Injection W0 V embedding := by
    refine ⟨hEmbedding.1,?_⟩
    intro x y z hxz hyz
    obtain ⟨a,hxa,haz⟩ := (hComp x z).mp hxz
    obtain ⟨b,hyb,hbz⟩ := (hComp y z).mp hyz
    exact hHInj.2 x y a hxa ((hFInj.2 a b z haz hbz).symm ▸ hyb)
  have hFixed0 : OldFixed O0 embedding := by
    intro a u hau
    have haCut := function_input hO0.1 hau
    obtain ⟨q,haq,_⟩ := hO.1.2 a ((hCut a).mp haCut).2
    exact (hComp u a).mpr ⟨q,(hPush.1 a u a q hau ((hInc a a).mpr ⟨haCut,rfl⟩)).mpr haq,hFixed a q haq⟩
  have hEmbT : MapsTo W0 T embedding := by
    refine ⟨hEmbedding.1.1,?_⟩
    intro x y hxy
    obtain ⟨u,_,huy⟩ := (hComp x y).mp hxy
    exact (hRange y).mpr ⟨u,function_input hF.1.1 huy,huy⟩
  have hGenEmb : NodeMap P0 embedding generators :=
    (ConstructionPushoutPasting.nodeMap_assoc hGen0 hComp).mp hGen
  have hExact := ConstructionSelectedCellRestriction.exact_range hM hm0 hv hO0 hP0
    hEmbedding hEmbT hGenerated hFixed0 hGenEmb hGenerators hRet hOld hCut hNext hWords
  have hTMonoid := ConstructionCellSimulationEquiv.range_submonoid hm hv hF hRange
  have hNextMonoid := ConstructionCellSimulationEquiv.range_submonoid hm0 hv hEmbedding hExact
  obtain ⟨pairsT,GT,hPairsT,hGT,hProductT⟩ := ConstructionCellGeneration.exists_product hM
    (fun x y hx hy => (hv.2.1 x hx).1 y hy)
    (fun x y z t hx hy hp hq => (hv.2.1 x hx).2.1 y z t hy hp hq) hTMonoid
  obtain ⟨pairsNext,GNext,hPairsNext,hGNext,hProductNext⟩ := ConstructionCellGeneration.exists_product hM
    (fun x y hx hy => (hv.2.1 x hx).1 y hy)
    (fun x y z t hx hy hp hq => (hv.2.1 x hx).2.1 y z t hy hp hq) hNextMonoid
  have hmT := monoid_restrict hv hTMonoid hProductT
  have hmNext := monoid_restrict hv hNextMonoid hProductNext
  have hFT := ConstructionCellGeneration.hom_restrict hF (ConstructionRangeObject.corestrict_maps hF.1 hRange) hProductT
  obtain ⟨invF,hInvF,hInverseF⟩ := ConstructionCellSimulationEquiv.inverse_hom hM hm hmT hFT ⟨hFT.1,hFInj.2⟩ hRange
  have hEmbNext := ConstructionCellGeneration.hom_restrict hEmbedding
    (ConstructionRangeObject.corestrict_maps hEmbedding.1 hExact) hProductNext
  have hEmbHomT := ConstructionCellGeneration.hom_restrict hEmbedding hEmbT hProductT
  obtain ⟨invEmbedding,hInvEmb,hInverseEmb⟩ := ConstructionCellSimulationEquiv.inverse_hom hM hm0 hmNext
    hEmbNext ⟨hEmbNext.1,hEmbInj.2⟩ hExact
  have hOldComp : NodeMap O F old := by
    intro a y
    constructor
    · intro hay
      obtain ⟨haD,rfl⟩ := (hOld a y).mp hay
      obtain ⟨u,hau,_⟩ := hO.1.2 a haD
      exact ⟨u,hau,hFixed a u hau⟩
    · rintro ⟨u,hau,huy⟩
      have he := function_unique hF.1.1 huy (hFixed a u hau)
      subst y
      exact (hOld a a).mpr ⟨function_input hO.1 hau,rfl⟩
  have hApex := ConstructionPushoutIdentification.map_apex hM hFT hInvF hInverseF hComp hOldComp hPush
  have hOld0Comp : NodeMap O0 embedding inc := by
    intro a y
    constructor
    · intro hay
      obtain ⟨haCut,rfl⟩ := (hInc a y).mp hay
      obtain ⟨u,hau,_⟩ := hO0.1.2 a haCut
      exact ⟨u,hau,hFixed0 a u hau⟩
    · rintro ⟨u,hau,huy⟩
      have he := function_unique hEmbedding.1.1 huy (hFixed0 a u hau)
      subst y
      exact (hInc a a).mpr ⟨function_input hO0.1 hau,rfl⟩
  obtain ⟨inclusion,hInclusion,hInclComp⟩ := ConstructionPushoutPasting.exists_hom_comp hM hInvEmb hEmbHomT
  have hIdentity : IdentityGraph next inclusion := by
    intro x y
    constructor
    · intro hxy
      obtain ⟨u,hxu,huy⟩ := (hInclComp x y).mp hxy
      exact ⟨function_input hInvEmb.1.1 hxu,(function_unique hEmbedding.1.1 ((hInverseEmb u x).mpr hxu) huy)⟩
    · rintro ⟨hx,rfl⟩
      obtain ⟨u,hxu,_⟩ := hInvEmb.1.1.2 x hx
      exact (hInclComp x x).mpr ⟨u,hxu,(hInverseEmb u x).mpr hxu⟩
  have hFinal := ConstructionPushoutIdentification.change_left hM hO0 hEmbHomT hEmbNext hInvEmb
    hInverseEmb hOld0Comp hInclComp hApex
  exact ⟨embedding,pairsT,GT,invF,pairsNext,GNext,invEmbedding,inclusion,
    hPairsT,hGT,hProductT,hmT,hFT,hInvF,hInverseF,hPairsNext,hGNext,hProductNext,hmNext,
    hEmbNext,hInvEmb,hInverseEmb,hEmbedding,hEmbInj,hComp,hFixed0,hExact,hInclusion,hIdentity,hFinal⟩

def result {m : Nat} (D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc embedding pairsT GT invF pairsNext GNext invEmbedding inclusion : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbeLetters.representatives T T pairsT) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo GT pairsT T)) (.conj (ConstructionConservativeHull.productGraph T GV GT) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid T GT e)) (.conj (ConstructionProbePushoutSyntax.hom W T G GT unit e F) (.conj (ConstructionProbePushoutSyntax.hom T W GT G e unit invF) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph F invF)) (.conj (ConstructionProbeLetters.representatives next next pairsNext) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo GNext pairsNext next)) (.conj (ConstructionConservativeHull.productGraph next GV GNext) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid next GNext e)) (.conj (ConstructionProbePushoutSyntax.hom W0 next G0 GNext unit0 e embedding) (.conj (ConstructionProbePushoutSyntax.hom next W0 GNext G0 e unit0 invEmbedding) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph embedding invEmbedding)) (.conj (ConstructionProbePushoutSyntax.hom W0 V G0 GV unit0 e embedding) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection embedding W0 V)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap H F embedding) (.conj (ConstructionAttachmentCoefficients.oldFixed O0 embedding) (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range W0 embedding next)) (.conj (ConstructionProbePushoutSyntax.hom next T GNext GT e e inclusion) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph next inclusion)) (ConstructionProbePushoutSyntax.isPushout D next T mul GNext GT e e e inc inc inclusion old))))))))))))))))))))))

theorem result_freeClosed {m : Nat} (D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc embedding pairsT GT invF pairsNext GNext invEmbedding inclusion : Fin m) : (result D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc embedding pairsT GT invF pairsNext GNext invEmbedding inclusion).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ConstructionProbeLetters.representatives_freeClosed,ProjectSyntax.freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc embedding pairsT GT invF pairsNext GNext invEmbedding inclusion : Fin m) :
    Project.Formula.satisfies env (result D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc embedding pairsT GT invF pairsNext GNext invEmbedding inclusion) ↔ Result (env.bound D) (env.bound mul) (env.bound e) (env.bound T) (env.bound next) (env.bound W) (env.bound G) (env.bound unit) (env.bound F) (env.bound W0) (env.bound G0) (env.bound unit0) (env.bound O0) (env.bound H) (env.bound V) (env.bound GV) (env.bound old) (env.bound inc) (env.bound embedding) (env.bound pairsT) (env.bound GT) (env.bound invF) (env.bound pairsNext) (env.bound GNext) (env.bound invEmbedding) (env.bound inclusion) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionConservativeHull.productGraph_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbePushoutSyntax.hom_semantics hM,ForcingConditionGraphs.inverseGraph_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,ForcingSupportedNames.range_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionProbePushoutSyntax.isPushout_semantics hM]
  rfl

def workSentence {m : Nat} (D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W G unit)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W0 G0 unit0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O D W)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O0 cut W0)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P0 I W0)) (.imp (ConstructionProbePushoutSyntax.hom W V G GV unit e F) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection F W V)) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W F T)) (.imp (ConstructionProbePushoutSyntax.hom W0 W G0 G unit0 unit H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection H W0 W)) (.imp (ConstructionProbePushoutSyntax.isPushout D W0 W mul G0 G e unit0 unit O0 inc H O) (.imp (ConstructionAttachmentCoefficients.oldFixed O F) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph cut inc)) (.imp (ConstructionCellGeneration.generated cut I W0 G0 unit0 O0 P0) (.imp (ConstructionProbeMappedPathSyntax.nodeMap P F generators) (.imp (ConstructionProbeMappedPathSyntax.nodeMap P0 H P) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I retained)) (.imp (ConstructionCellGeneration.submonoid V GV e retained) (.imp (ConstructionAttachmentCoefficients.intersection cut retained D) (.imp (ConstructionAttachmentCoefficients.intersection next retained T) (.imp (.forallE (.imp (.mem (.bound 0) (.bound retained.succ)) (.imp (.mem (.bound 0) (.bound T.succ)) (.imp (.neg (.mem (.bound 0) (.bound D.succ))) (ConstructionCellGeneration.closureMember I.succ V.succ GV.succ e.succ old.succ generators.succ cut.succ 0))))) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (result D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ T.succ.succ.succ.succ.succ.succ.succ.succ next.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ.succ W0.succ.succ.succ.succ.succ.succ.succ.succ G0.succ.succ.succ.succ.succ.succ.succ.succ unit0.succ.succ.succ.succ.succ.succ.succ.succ O0.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ old.succ.succ.succ.succ.succ.succ.succ.succ inc.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 4 3 2 1 0))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ConstructionCellGeneration.generated_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionCellGeneration.submonoid_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,ConstructionCellGeneration.closureMember_freeClosed,result_freeClosed]

theorem work_models {m : Nat} (D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (workSentence D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (workSentence D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbePushoutSyntax.hom_semantics hM,ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ConstructionProbePushoutSyntax.isPushout_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionCellGeneration.generated_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionCellGeneration.submonoid_semantics hM,ConstructionAttachmentCoefficients.intersection_semantics (M := M),ConstructionCellGeneration.closureMember_semantics hM,result_semantics hM]
  exact work hM

theorem work_kernel_certificate {m : Nat} (D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (workSentence D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators)) :=
  ModelTransfer.derives (fun _ hM => work_models D mul e T next retained cut I W G unit O P F W0 G0 unit0 O0 P0 H V GV old inc generators hM)

end PPAC.Migration.ConstructionRestrictedCellPushout
