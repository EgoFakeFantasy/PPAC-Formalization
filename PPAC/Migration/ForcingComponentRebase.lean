/- Pinned QuotientTransport.rebaseGlued/componentEquiv:353-421.
The existing set quotient is literally unchanged by a root change within the
same Common component. Consume the existing whole-component transport and
rebase its target to the original root, as required by TailGraphs.transport. -/
import PPAC.Migration.ForcingGluedTransport

namespace PPAC.Migration.ForcingComponentRebase
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation)
open ConstructionComponentCarrier (EncodedVertex)
open ConstructionComponentCofinal (EncodedCommon)
open ForcingComponentFibers (VertexFiber)
open ForcingComponentGluing (ToGlued Component)
open ForcingComponentMove (Move)
open ForcingGluedTransport (Gluing FiberMove RootMap Naturality gluing gluing_freeClosed
  gluing_semantics fiberMove fiberMove_freeClosed fiberMove_semantics
  rootMap rootMap_freeClosed rootMap_semantics naturality naturality_freeClosed naturality_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem common_symm {D I mul q a b : M.Carrier .set}
    (h : EncodedCommon D I mul q a b) : EncodedCommon D I mul q b a := by
  obtain ⟨r,i,U,s,j,V,ha,hb,hr,hs,h⟩ := h
  exact ⟨s,j,V,r,i,U,hb,ha,hs,hr,ConstructionComponentVertices.common_symm h⟩

theorem common_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q a b w : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (h : EncodedCommon D I mul q a b) :
    EncodedCommon D I mul q a w ↔ EncodedCommon D I mul q b w :=
  ⟨ForcingComponentGluing.common_between hM hm hJ h,
    ForcingComponentGluing.common_between hM hm hJ (common_symm h)⟩

theorem rebase_component (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q objects maps a b P : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (h : EncodedCommon D I mul q a b)
    (hP : Component D I mul q objects maps a P) :
    Component D I mul q objects maps b P := by
  intro p
  rw [hP p]
  exact and_congr_right fun _ => exists_congr fun w => exists_congr fun x =>
    and_congr_right fun _ => common_iff hM hm hJ h

/-- The same points, classes, projection and every toGlued graph remain valid.
No representative is selected and no quotient is reconstructed. -/
theorem rebase_gluing (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q objects maps a b P Q pr : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (h : EncodedCommon D I mul q a b) (hG : Gluing D I mul q objects maps a P Q pr) :
    Gluing D I mul q objects maps b P Q pr := by
  refine ⟨rebase_component hM hm hJ h hG.1,hG.2.1,hG.2.2.1,hG.2.2.2.1,?_,hG.2.2.2.2.2⟩
  intro w X hw hX
  exact hG.2.2.2.2.1 w X ((common_iff hM hm hJ h).mpr hw) hX

def Transport (D I mul q pi objects maps targets targetMaps apps v : M.Carrier .set) : Prop :=
  ∃ V X XT P Q pr PT Z prT f b c phi,
    Move D I mul q pi v V ∧ VertexFiber D mul objects maps v X ∧ VertexFiber D mul targets targetMaps V XT ∧
    Gluing D I mul q objects maps v P Q pr ∧ Gluing D I mul q targets targetMaps v PT Z prT ∧
    FiberMove D mul pi objects maps targets targetMaps apps v V X XT f ∧
    ToGlued v X Q pr b ∧ ToGlued V XT Z prT c ∧ RootMap b f c phi ∧ Injection Q Z phi ∧
    (∀ E, (Project.FirstOrderSemantics.reduct M).mem E Z →
      ∃ C, (Project.FirstOrderSemantics.reduct M).mem C Q ∧ PureKuratowski.PairMember M C E phi) ∧
    Naturality D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi

theorem of_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q pi objects maps targets targetMaps apps v V : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hMove : Move D I mul q pi v V) (hCommon : EncodedCommon D I mul q v V)
    (h : ForcingGluedTransport.Transport D I mul q pi objects maps targets targetMaps apps v) :
    Transport D I mul q pi objects maps targets targetMaps apps v := by
  obtain ⟨W,X,XT,P,Q,pr,PT,Z,prT,f,b,c,phi,hw,hX,hXT,hG,hGT,hf,hb,hc,hRoot,hInj,hOnto,hNat⟩ := h
  have he := ForcingComponentMove.move_unique hM hMove hw
  subst W
  exact ⟨V,X,XT,P,Q,pr,PT,Z,prT,f,b,c,phi,hw,hX,hXT,hG,
    rebase_gluing hM hm hJ (common_symm hCommon) hGT,hf,hb,hc,hRoot,hInj,hOnto,hNat⟩

theorem exists_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q pi diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps v V : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hTargets : MapsTo diagrams targetImage targets)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hTargetMaps : MapsTo S targetMapImage targetMaps)
    (hSys : ForcingEligibleSystem.System D objects maps) (hTSys : ForcingEligibleSystem.System D targets targetMaps)
    (hAppMap : MapsTo diagrams appImage apps) (hApps : ForcingReindexSystem.Apps D pi objects targets apps)
    (hNatural : ForcingReindexSystem.Natural D pi maps targetMaps apps) (hv : EncodedVertex D I mul q v)
    (hMove : Move D I mul q pi v V) (hCommon : EncodedCommon D I mul q v V) :
    Transport D I mul q pi objects maps targets targetMaps apps v := by
  exact of_transport hM hm hJ hMove hCommon
    (ForcingGluedTransport.exists_transport hM hm hJ hp hFix hDiagrams hObj hTargets hS hMaps hTargetMaps hSys hTSys hAppMap hApps hNatural hv)

def transport {m : Nat} (D I mul q pi objects maps targets targetMaps apps v : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingComponentMove.move D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 10) (.conj (gluing D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7) (.conj (gluing D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 4) (.conj (fiberMove D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 11 10 3) (.conj (ForcingComponentGluing.toGlued v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 8 7 2) (.conj (ForcingComponentGluing.toGlued 12 10 5 4 1) (.conj (rootMap 2 3 1 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 8 5)) (.conj (.forallE (.imp (.mem (.bound 0) (.bound 6)) (.existsE (.conj (.mem (.bound 0) (.bound 10)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1)))))) (naturality D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 5 7 4 0)))))))))))))))))))))))))

theorem transport_freeClosed {m : Nat} (D I mul q pi objects maps targets targetMaps apps v : Fin m) : (transport D I mul q pi objects maps targets targetMaps apps v).FreeClosed := by
  simp -implicitDefEqProofs [transport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentMove.move_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,gluing_freeClosed,fiberMove_freeClosed,ForcingComponentGluing.toGlued_freeClosed,rootMap_freeClosed,naturality_freeClosed]

theorem transport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi objects maps targets targetMaps apps v : Fin m) :
    Project.Formula.satisfies env (transport D I mul q pi objects maps targets targetMaps apps v) ↔ Transport (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) (env.bound v) := by
  simp only [transport,Transport,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,gluing_semantics hM,fiberMove_semantics hM,ForcingComponentGluing.toGlued_semantics hM,rootMap_semantics hM,ForcingSupportSize.injection_semantics (M := M),naturality_semantics hM]
  rfl

def constructionSentence {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D pi q q)) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets diagrams targetImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targetMaps S targetMapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (.imp (ForcingEligibleSystem.system D targets targetMaps) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps diagrams appImage)) (.imp (ForcingReindexSystem.appsF D pi objects targets apps) (.imp (ForcingReindexSystem.natural D pi maps targetMaps apps) (.imp (ConstructionComponentCarrier.encodedVertex D I mul q v) (.imp (ForcingComponentMove.move D I mul q pi v V) (.imp (ConstructionComponentCofinal.encodedCommon D I mul q v V) (transport D I mul q pi objects maps targets targetMaps apps v)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingEligibleSystem.system_freeClosed,
      ForcingReindexSystem.appsF_freeClosed,ForcingReindexSystem.natural_freeClosed,ConstructionComponentCarrier.encodedVertex_freeClosed,transport_freeClosed,ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem construction_models {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    ForcingReindexSystem.appsF_semantics hM,ForcingReindexSystem.natural_semantics hM,
    ConstructionComponentCarrier.encodedVertex_semantics hM,transport_semantics hM,ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  exact exists_transport hM

theorem construction_kernel_certificate {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v V hM)

end PPAC.Migration.ForcingComponentRebase
