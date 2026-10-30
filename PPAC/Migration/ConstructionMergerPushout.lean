/- Pinned MergerPushouts.roots_satisfy/map_roots_satisfy/satisfies_map_iff/
mergerSimulation_root/mergerSimulation_pushout. Consumer: ConservativeCells and
CellReorder. Build the actual induced homomorphism from the existing literal
Merger presentations; no universal property or target conservation is assumed. -/
import PPAC.Migration.ConstructionMergerPresentedLift
import PPAC.Migration.ConstructionMergerPrescriptionMapSyntax
import PPAC.Migration.ConstructionPushoutIdentification

namespace PPAC.Migration.ConstructionMergerPushout
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionProbeHomEvaluation (product_unique)
open ConstructionProbePushout (Hom SquareComm IsPushout composition_value)
open ConstructionProbeMappedPath (NodeMap exists_node_map)
open ConstructionPushoutPasting (exists_hom_comp nodeMap_assoc square_redirect)
open ConstructionMergerPresentedLift (Value Satisfies PresentedBoundary)
open ConstructionMergerRelations (Prescription Valid)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (Unit Associative LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Only concrete contracts, all already constructed in the Merger producer.
No universal-property field and no new proof/quotient kernel. -/
structure Presentation (w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set) : Prop where
  monoid : LeftCancelMonoid D mul e
  prescription : Prescription n D P
  representatives : Representatives n D C
  copies : ConstructionMergerCopies.Copies n D mul P C L
  projection_map : MapsTo C L projection
  projection_law : ConstructionMergerCopies.Projection n D mul P C projection
  equality : ConstructionMergerCopies.EqualityLaw n D mul P projection
  copy_action : ConstructionMergerAction.ActionTable D mul projection A
  copy_law : ConstructionMergerAction.CopyLaw D mul projection A
  word : Carrier w D L W
  word_action : ConstructionMergerWordAction.ActionTable w D L zero mul A T
  product : ConstructionMergerWordProduct.Laws w D L zero T G
  old_unit : Old zero D e unit
  unit_law : Unit W G unit
  associative : Associative W G
  product_representatives : Representatives W W B
  product_map : MapsTo B W G
  old_graph : ConstructionProbeOldEmbedding.OldGraph zero D O
  old_hom : Hom D W mul G e unit O
  roots_map : MapsTo n W roots
  roots : ConstructionMergerRoots.RootGraph w D L e projection unit roots

/-- Assemble the existing complete Merger producer without adding conicality
of either the base or the target: only unit/associativity are needed here. -/
theorem exists_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P) (hValid : Valid n D mul P) :
    ∃ C L projection A W T B G unit O roots, Presentation w n zero D mul e P C L projection A W T B G unit O roots := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,G,hC,hp,hL,hProjection,hEq,_,_,hAction,_,hCopy,hW,_,hT,hWordAction,hWordFree,hB,hG,hProduct⟩ :=
    ConstructionMergerWordProduct.exists_system hM hw hz hzw hm hP hValid
  obtain ⟨unit,hUnit⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hm.1.1
  have hUW := ConstructionMergerWordMonoid.unit_laws hM hw hz hzw hm hW hT hWordFree hWordAction hProduct hUnit
  have hAssoc := ConstructionMergerWordMonoid.associative hM hw hz hzw hW hB hG hT hWordFree hWordAction hProduct
  obtain ⟨O,hO,hOG⟩ := ConstructionMergerOldEmbedding.exists_old_graph hM hz hzw hW
  have hOH : Hom D W mul G e unit O := ⟨hO.1,(hOG e unit).mpr hUnit,
    ConstructionMergerOldEmbedding.preserves_products hOG hWordAction hProduct⟩
  obtain ⟨roots,hRootsMap,hRoots⟩ := ConstructionMergerRoots.exists_root_graph hM hw hz hzw hm hW hC hp hUnit
  exact ⟨C,L,projection,A,W,T,B,G,unit,O,roots,hm,hP,hC,hL,hp,hProjection,hEq,hAction,hCopy,hW,
    hWordAction,hProduct,hUnit,hUW,hAssoc,hB,hG,hOG,hOH,hRootsMap,hRoots⟩

section Actual
variable (hM : FirstOrder.Theory.Models M nativeZF)
variable {w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set}
variable (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
include hA

theorem boundary_iff_lifts {Q f p F : M.Carrier .set} (hf : MapsTo D Q f) (hp : MapsTo n Q p) :
    PresentedBoundary zero D roots f p F ↔ NodeMap O F f ∧ NodeMap roots F p := by
  constructor
  · intro h
    constructor
    · intro x y
      constructor
      · intro hxy
        obtain ⟨q,hq,_⟩ := hA.old_hom.1.1.2 x (function_input hf.1 hxy)
        exact ⟨q,hq,(h.1 x q y ((hA.old_graph x q).mp hq)).mpr hxy⟩
      · rintro ⟨q,hq,hqy⟩
        exact (h.1 x q y ((hA.old_graph x q).mp hq)).mp hqy
    · intro i y
      constructor
      · intro hiy
        obtain ⟨r,hr,_⟩ := hA.roots_map.1.2 i (function_input hp.1 hiy)
        exact ⟨r,hr,(h.2 i r y hr).mpr hiy⟩
      · rintro ⟨r,hr,hry⟩
        exact (h.2 i r y hr).mp hry
  · rintro ⟨ho,hr⟩
    exact ⟨fun x q y hx => (composition_value hA.old_hom.1 ho ((hA.old_graph x q).mpr hx)).symm,
      fun _ _ _ hi => (composition_value hA.roots_map hr hi).symm⟩

include hM

theorem presentation_lift
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {Q J mulQ eQ f p : M.Carrier .set}
    (hJ : Representatives Q Q J) (hMul : MapsTo J Q mulQ) (hUnit : Unit Q mulQ eQ) (hAssoc : Associative Q mulQ)
    (hf : Hom D Q mul mulQ e eQ f) (hp : MapsTo n Q p) (hSat : Satisfies P f p mulQ) :
    ∃ F, Hom W Q G mulQ unit eQ F ∧ NodeMap O F f ∧ NodeMap roots F p ∧
      ∀ K, Hom W Q G mulQ unit eQ K → NodeMap O K f → NodeMap roots K p → K = F := by
  obtain ⟨F,hF,hB,hUnique⟩ := ConstructionMergerPresentedLift.existsUnique_presentedHom hM hw hz hzw hA.word hA.monoid
    hA.representatives hA.copies hA.projection_law hA.projection_map hA.equality hA.prescription
    hA.copy_law hA.copy_action hA.word_action hA.product hA.old_unit hA.unit_law hA.roots_map hA.roots
    hJ hMul hUnit hAssoc hf hp hSat
  obtain ⟨ho,hr⟩ := (boundary_iff_lifts hA hf.1 hp).mp hB
  exact ⟨F,hF,ho,hr,fun K hK ho hr => hUnique K hK ((boundary_iff_lifts hA hf.1 hp).mpr ⟨ho,hr⟩)⟩

theorem roots_satisfy
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) : Satisfies P O roots G := by
  intro i j a b u v hne hStart hu hv
  obtain ⟨ri,oa,hri,hoa,hu⟩ := hu
  obtain ⟨rj,ob,hrj,hob,hv⟩ := hv
  have hLaw := ConstructionMergerRoots.root_laws hM hw hz hA.monoid hA.copy_law hA.equality
    hA.word_action hA.product hA.old_graph hA.roots
  exact (hLaw.2.1 i j a b ri rj oa ob u v hri hrj hoa hob hu hv).mpr
    (ConstructionMergerPrescriptionMap.rel_start hA.monoid hA.prescription hne hStart)

theorem map_roots_satisfy
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    {Q J mulQ eQ F f p : M.Carrier .set} (hMul : MapsTo J Q mulQ)
    (hF : Hom W Q G mulQ unit eQ F) (hf : NodeMap O F f) (hp : NodeMap roots F p) :
    Satisfies P f p mulQ := by
  intro i j a b u v hne hStart hu hv
  obtain ⟨pi,fa,hpi,hfa,hu⟩ := hu
  obtain ⟨pj,fb,hpj,hfb,hv⟩ := hv
  obtain ⟨ri,hri,hriF⟩ := (hp i pi).mp hpi
  obtain ⟨rj,hrj,hrjF⟩ := (hp j pj).mp hpj
  obtain ⟨oa,hoa,hoaF⟩ := (hf a fa).mp hfa
  obtain ⟨ob,hob,hobF⟩ := (hf b fb).mp hfb
  obtain ⟨ua,huaD,hua⟩ := projected hM hA.product_representatives hA.product_map
    (hA.roots_map.2 i ri hri) (hA.old_hom.1.2 a oa hoa)
  obtain ⟨ub,_,hub⟩ := projected hM hA.product_representatives hA.product_map
    (hA.roots_map.2 j rj hrj) (hA.old_hom.1.2 b ob hob)
  have he := roots_satisfy hM hA hw hz i j a b ua ub hne hStart ⟨ri,oa,hri,hoa,hua⟩ ⟨rj,ob,hrj,hob,hub⟩
  subst ub
  obtain ⟨z,hzF,_⟩ := hF.1.1.2 ua huaD
  exact (product_unique hM hMul hu (hF.2.2 ri oa ua pi fa z hua hriF hoaF hzF)).trans
    (product_unique hM hMul hv (hF.2.2 rj ob ua pj fb z hub hrjF hobF hzF)).symm

theorem presentation_ext
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {Q J mulQ eQ F K f p : M.Carrier .set}
    (hJ : Representatives Q Q J) (hMul : MapsTo J Q mulQ) (hUnit : Unit Q mulQ eQ) (hAssoc : Associative Q mulQ)
    (hF : Hom W Q G mulQ unit eQ F) (hK : Hom W Q G mulQ unit eQ K)
    (hf : Hom D Q mul mulQ e eQ f) (hp : MapsTo n Q p)
    (hFO : NodeMap O F f) (hFR : NodeMap roots F p) (hKO : NodeMap O K f) (hKR : NodeMap roots K p) : F = K := by
  obtain ⟨out,_,_,_,hu⟩ := presentation_lift hM hA hw hz hzw hJ hMul hUnit hAssoc hf hp
    (map_roots_satisfy hM hA hw hz hMul hF hFO hFR)
  exact (hu F hF hFO hFR).trans (hu K hK hKO hKR).symm

end Actual

/-- Composition of old coefficient values, using the already constructed graph. -/
theorem value_comp {D N f t tf p mulQ i a fa v : M.Carrier .set}
    (hf : MapsTo D N f) (hComp : NodeMap f t tf) (hfa : PureKuratowski.PairMember M a fa f) :
    Value tf p mulQ i a v ↔ Value t p mulQ i fa v := by
  exact exists_congr fun pi => exists_congr fun x => and_congr_right fun _ =>
    and_congr_left fun _ => composition_value hf hComp hfa

theorem satisfies_map_iff {n D N P PN f t tf p mulQ : M.Carrier .set}
    (hP : Prescription n D P) (hf : MapsTo D N f) (hMap : ConstructionMergerPrescriptionMap.Mapped P f PN)
    (hComp : NodeMap f t tf) : Satisfies PN t p mulQ ↔ Satisfies P tf p mulQ := by
  constructor
  · intro h i j a b u v hne hStart hu hv
    have hTyped := hP.1 i j a b hStart
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a hTyped.2.2.1
    obtain ⟨fb,hfb,_⟩ := hf.1.2 b hTyped.2.2.2
    exact h i j fa fb u v hne ((hMap i j fa fb).mpr ⟨a,b,hStart,hfa,hfb⟩)
      ((value_comp hf hComp hfa).mp hu) ((value_comp hf hComp hfb).mp hv)
  · intro h i j fa fb u v hne hStart hu hv
    obtain ⟨a,b,hStart,hfa,hfb⟩ := (hMap i j fa fb).mp hStart
    exact h i j a b u v hne hStart ((value_comp hf hComp hfa).mpr hu) ((value_comp hf hComp hfb).mpr hv)

/-- Literal snoc equation of ConservativeExtensions.mergerSimulation_snoc,
using the original displayed copy representatives and the mapped coefficients. -/
def TransportSnoc (w D L projection N LN projectionN f H : M.Carrier .set) : Prop :=
  ∀ i a fa c cN t tN q qN, Product projection i a c → PureKuratowski.PairMember M a fa f →
    Product projectionN i fa cN → Cons w D L c t q → PureKuratowski.PairMember M t tN H →
    Cons w N LN cN tN qN → PureKuratowski.PairMember M q qN H

section Pushout
variable (hM : FirstOrder.Theory.Models M nativeZF)
variable {w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set}
variable {N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H : M.Carrier .set}
variable (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
variable (hB : Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
include hM hA hB

/-- Construct the actual induced homomorphism and both generator equations. -/
theorem exists_simulation
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Hom D N mul mulN e eN f) (hMap : ConstructionMergerPrescriptionMap.Mapped P f PN) :
    ∃ H, Hom W WN G GN unit unitN H ∧ SquareComm O f H ON ∧ NodeMap roots H rootsN := by
  obtain ⟨fOld,hfOld,hfOldGraph⟩ := exists_hom_comp hM hf hB.old_hom
  have hSat := (satisfies_map_iff hA.prescription hf.1 hMap hfOldGraph).mp (roots_satisfy hM hB hw hz)
  obtain ⟨H,hH,hOld,hRoot,_⟩ := presentation_lift hM hA hw hz hzw hB.product_representatives
    hB.product_map hB.unit_law hB.associative hfOld hB.roots_map hSat
  refine ⟨H,hH,?_,hRoot⟩
  intro x q fx y hq hfx
  exact (composition_value hA.old_hom.1 hOld hq).symm.trans (composition_value hf.1 hfOldGraph hfx)

/-- Pinned mergerSimulation_pushout, with its full arbitrary-target universal
property, on the same two literal Merger carriers and induced map. -/
theorem simulation_pushout
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hMap : ConstructionMergerPrescriptionMap.Mapped P f PN)
    (hH : Hom W WN G GN unit unitN H) (hComm : SquareComm O f H ON) (hRoots : NodeMap roots H rootsN) :
    IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  refine ⟨hComm,?_⟩
  intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨oldS,hOldS,hOldSGraph⟩ := exists_hom_comp hM hA.old_hom hs
  obtain ⟨p,hp,hpGraph⟩ := exists_node_map hM hA.roots_map hs.1
  have hFT := square_redirect hA.old_hom.1 hf hc hOldSGraph
  have hSat := (satisfies_map_iff hA.prescription hf hMap hFT).mpr
    (map_roots_satisfy hM hA hw hz hMul hs hOldSGraph hpGraph)
  obtain ⟨out,hOut,hOld,hRoot,hu⟩ := presentation_lift hM hB hw hz hzw hJ hMul hUnit hAssoc ht hp hSat
  obtain ⟨K,hK,hKGraph⟩ := exists_hom_comp hM hH hOut
  have hSquare := ConstructionPushoutPasting.square_post hComm hKGraph hOld
  have hKO : NodeMap O K oldS := square_redirect hf hA.old_hom.1
    (fun x fx q y hfx hq => (hSquare x q fx y hq hfx).symm) hFT
  have hKR : NodeMap roots K p := (nodeMap_assoc hRoots hKGraph).mp hRoot
  have he : K = s := presentation_ext hM hA hw hz hzw hJ hMul hUnit hAssoc hK hs hOldS hp hKO hKR hOldSGraph hpGraph
  have hNew : NodeMap H out s := he ▸ hKGraph
  refine ⟨out,hOut,hNew,hOld,?_⟩
  intro R hR hRN hRO
  exact hu R hR hRO ((nodeMap_assoc hRoots hRN).mpr hpGraph)

/-- Identify the constructed homomorphism with the literal source transport,
in addition to its old/root generator equations. All words are internal. -/
theorem simulation_snoc
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hH : Hom W WN G GN unit unitN H)
    (hComm : SquareComm O f H ON) (hRoots : NodeMap roots H rootsN) :
    TransportSnoc w D L projection N LN projectionN f H := by
  have map_product {x y z fx fy fz : M.Carrier .set}
      (hx : PureKuratowski.PairMember M x fx H) (hy : PureKuratowski.PairMember M y fy H)
      (hProd : Product G x y z) (hProdN : Product GN fx fy fz) : PureKuratowski.PairMember M z fz H := by
    obtain ⟨v,hv,_⟩ := hH.1.1.2 z (projected_range hA.product_map hProd)
    have he := product_unique hM hB.product_map (hH.2.2 x y z fx fy v hProd hx hy hv) hProdN
    exact he ▸ hv
  intro i a fa c cN t tN q qN hca hfa hcaN hCons ht hConsN
  obtain ⟨hi,ha⟩ := ConstructionProbeAction.projected_indices hA.representatives hA.projection_map hca
  obtain ⟨r,hr,_⟩ := hA.roots_map.1.2 i hi
  obtain ⟨rN,hrN,_⟩ := hB.roots_map.1.2 i hi
  have hrrN := (composition_value hA.roots_map hRoots hr).mp hrN
  obtain ⟨oa,hoa,_⟩ := hA.old_hom.1.1.2 a ha
  obtain ⟨oaN,hoaN,_⟩ := hB.old_hom.1.1.2 fa (hf.2 a fa hfa)
  have hooN := (hComm a oa fa oaN hoa hfa).mpr hoaN
  obtain ⟨letter,hLetter⟩ := ConstructionProbeRaw.exists_cons hM hw (projected_range hA.projection_map hca)
    (ConstructionProbeRaw.old_raw hM hz hzw hA.old_unit)
  obtain ⟨letterN,hLetterN⟩ := ConstructionProbeRaw.exists_cons hM hw (projected_range hB.projection_map hcaN)
    (ConstructionProbeRaw.old_raw hM hz hzw hB.old_unit)
  have hProd := (ConstructionMergerRoots.root_mul_old hM hw hz hA.monoid hA.copy_law hA.word_action hA.product
    ((hA.roots i r).mp hr) ((hA.old_graph a oa).mp hoa)).mpr ⟨c,hca,hLetter⟩
  have hProdN := (ConstructionMergerRoots.root_mul_old hM hw hz hB.monoid hB.copy_law hB.word_action hB.product
    ((hB.roots i rN).mp hrN) ((hB.old_graph fa oaN).mp hoaN)).mpr ⟨cN,hcaN,hLetterN⟩
  have hLetters := map_product hrrN hooN hProd hProdN
  have hTUnit : Product G t unit t := ((hA.unit_law.2 t (function_input hH.1.1 ht) t).2).mpr rfl
  have hTUnitN : Product GN tN unitN tN := ((hB.unit_law.2 tN (hH.1.2 t tN ht) tN).2).mpr rfl
  exact map_product ht hLetters ((hA.product.2 c unit letter t q hLetter).mpr ⟨t,hTUnit,hCons⟩)
    ((hB.product.2 cN unitN letterN tN qN hLetterN).mpr ⟨tN,hTUnitN,hConsN⟩)

theorem exists_pushout
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Hom D N mul mulN e eN f) (hMap : ConstructionMergerPrescriptionMap.Mapped P f PN) :
    ∃ H, Hom W WN G GN unit unitN H ∧ NodeMap roots H rootsN ∧
      TransportSnoc w D L projection N LN projectionN f H ∧ IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  obtain ⟨H,hH,hComm,hRoots⟩ := exists_simulation hM hA hB hw hz hzw hf hMap
  exact ⟨H,hH,hRoots,simulation_snoc hM hA hB hw hz hzw hf.1 hH hComm hRoots,simulation_pushout hM hA hB hw hz hzw hf.1 hMap hH hComm hRoots⟩

end Pushout

/-- Construct BOTH complete actual presentations and the mapped prescription
before proving the pushout. These are existential outputs, not caller fields. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P N mulN eN f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hValid : Valid n D mul P)
    (hf : ConstructionProbeConservative.Conservative D N mul mulN f)
    (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul) :
    ∃ PN C L projection A W T B G unit O roots CN LN projectionN AN WN TN BN GN unitN ON rootsN H,
      ConstructionMergerPrescriptionMap.Graph P f PN ∧
      Presentation w n zero D mul e P C L projection A W T B G unit O roots ∧
      Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN ∧
      Hom W WN G GN unit unitN H ∧ NodeMap roots H rootsN ∧
      TransportSnoc w D L projection N LN projectionN f H ∧ IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  obtain ⟨PN,hGraph,hMap,hPN,hValidPN,_,_⟩ := ConstructionMergerPrescriptionMap.exists_system hM hm hmN hP hf hPres hJoins
  obtain ⟨C,L,projection,A,W,T,B,G,unit,O,roots,hA⟩ := exists_presentation hM hw hz hzw hm hP hValid
  obtain ⟨CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,hB⟩ := exists_presentation hM hw hz hzw hmN hPN (hValidPN.mpr hValid)
  obtain ⟨H,hH,hRoots,hSnoc,hPush⟩ := exists_pushout hM hA hB hw hz hzw ⟨hf.1.1,hOne,hPres⟩ hMap
  exact ⟨PN,C,L,projection,A,W,T,B,G,unit,O,roots,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,
    hGraph,hA,hB,hH,hRoots,hSnoc,hPush⟩

def presentation {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.conj
  (ConstructionMergerRelations.prescription n D P) (.conj (ConstructionProbeLetters.representatives n D C)
  (.conj (ConstructionMergerCopies.copies n D mul P C L) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo projection C L)) (.conj (ConstructionMergerCopies.projectionGraph n D mul P C
  projection) (.conj (ConstructionMergerCopies.equalityLaw n D mul P projection) (.conj
  (ConstructionMergerAction.actionTable D mul projection A) (.conj (ConstructionMergerAction.copyLaw D mul
  projection A) (.conj (ConstructionProbeRaw.carrier w D L W) (.conj (ConstructionMergerWordAction.actionTable
  w D L zero mul A T) (.conj (ConstructionMergerWordProduct.laws w D L zero T G) (.conj
  (ConstructionProbeRaw.old zero D e unit) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.unit W G
  unit)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.associative W G)) (.conj
  (ConstructionProbeLetters.representatives W W B) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
  G B W)) (.conj (ConstructionProbeOldEmbeddingSyntax.oldGraph zero D O) (.conj
  (ConstructionProbePushoutSyntax.hom D W mul G e unit O) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo roots n W)) (ConstructionMergerRoots.rootGraph w D L e projection unit
  roots)))))))))))))))))))))

theorem presentation_freeClosed {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) : (presentation w n zero D mul e P C L projection A W T B G unit O roots).FreeClosed := by
  simp -implicitDefEqProofs [presentation,
    Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,
    ConstructionMergerRelations.prescription_freeClosed,
    ConstructionProbeLetters.representatives_freeClosed,
    ConstructionMergerCopies.copies_freeClosed,
    ConstructionMergerCopies.projectionGraph_freeClosed,
    ConstructionMergerCopies.equalityLaw_freeClosed,
    ConstructionMergerAction.actionTable_freeClosed,
    ConstructionMergerAction.copyLaw_freeClosed,
    ConstructionProbeRaw.carrier_freeClosed,
    ConstructionMergerWordAction.actionTable_freeClosed,
    ConstructionMergerWordProduct.laws_freeClosed,
    ConstructionProbeRaw.old_freeClosed,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,
    ConstructionMergerRoots.rootGraph_freeClosed]

theorem presentation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) :
    Project.Formula.satisfies env (presentation w n zero D mul e P C L projection A W T B G unit O roots) ↔ Presentation (env.bound w) (env.bound n) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound P) (env.bound C) (env.bound L) (env.bound projection) (env.bound A) (env.bound W) (env.bound T) (env.bound B) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) := by
  simp only [presentation,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.unit_semantics (M := M),
    ForcingDiagramPoset.associative_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionProbeRaw.carrier_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,
    ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionMergerRoots.rootGraph_semantics hM]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩
  · intro h
    exact ⟨h.monoid,h.prescription,h.representatives,h.copies,h.projection_map,h.projection_law,h.equality,h.copy_action,h.copy_law,h.word,h.word_action,h.product,h.old_unit,h.unit_law,h.associative,h.product_representatives,h.product_map,h.old_graph,h.old_hom,h.roots_map,h.roots⟩

def transportSnoc {m : Nat} (w D L projection N LN projectionN f H : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product
  projection.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7 5)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6)) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projectionN.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6 4)) (.imp
  (ConstructionProbeRaw.cons w.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 3 1) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 2)) (.imp
  (ConstructionProbeRaw.cons w.succ.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ LN.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 2 0)
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ.succ.succ.succ 1
  0)))))))))))))))))

theorem transportSnoc_freeClosed {m : Nat} (w D L projection N LN projectionN f H : Fin m) : (transportSnoc w D L projection N LN projectionN f H).FreeClosed := by
  simp -implicitDefEqProofs [transportSnoc,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem transportSnoc_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D L projection N LN projectionN f H : Fin m) :
    Project.Formula.satisfies env (transportSnoc w D L projection N LN projectionN f H) ↔ TransportSnoc (env.bound w) (env.bound D) (env.bound L) (env.bound projection) (env.bound N) (env.bound LN) (env.bound projectionN) (env.bound f) (env.bound H) := by
  simp only [transportSnoc,TransportSnoc,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeRaw.cons_semantics hM]
  rfl

/-- Every constructed set and graph is existentially quantified inside the
pure-membership sentence, including both Merger carriers and the simulation. -/
def sourceSentence {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound
    zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp
    (ConstructionMergerRelations.prescription n D P) (.imp (ConstructionMergerRelations.valid n D mul P) (.imp
    (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.imp
    (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN f) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f e eN)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionMergerPrescriptionMapSyntax.graph
    P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    23) (.conj (presentation
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    22 21 20 19 18 17 16 15 14 13 12) (.conj (presentation
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    23 11 10 9 8 7 6 5 4 3 2 1) (.conj (ConstructionProbePushoutSyntax.hom 18 7 15 4 14 3 0) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap 12 0 1) (.conj (transportSnoc
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    21 20
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    10 9
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    0) (ConstructionProbePushoutSyntax.isPushout
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    18 7
    mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    15 4
    eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    14 3 13
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    0 2))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      ConstructionMergerRelations.prescription_freeClosed,
      ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,
      presentation_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      transportSnoc_freeClosed,
      ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem source_models {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w n zero D mul e P N mulN eN f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (sourceSentence w n zero D mul e P N mulN eN f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,
    presentation_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    transportSnoc_semantics hM,
    ConstructionProbePushoutSyntax.isPushout_semantics hM]
  exact exists_system hM

theorem source_kernel_certificate {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w n zero D mul e P N mulN eN f)) :=
  ModelTransfer.derives (fun _ hM => source_models w n zero D mul e P N mulN eN f hM)

end PPAC.Migration.ConstructionMergerPushout
