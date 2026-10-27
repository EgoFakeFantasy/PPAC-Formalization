/- Pinned MonoidRounds.ProbeData.map:17 / MergerData.map:31 /
Request.map:43. Both original constructors, arbitrary internal paths and
finite indices; reuse accepted node composition and exact prescription map. -/
import PPAC.Migration.ConstructionMergerPrescriptionMapSyntax
import PPAC.Migration.ConstructionProbeMappedPathSyntax

namespace PPAC.Migration.ConstructionRequestMaps
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePath (Path)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionMergerRelations (Prescription Valid)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem node_map_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w N node f A B : M.Carrier .set} (hA : MapsTo w N A) (hB : MapsTo w N B)
    (hMA : NodeMap node f A) (hMB : NodeMap node f B) : A = B :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM w N A).mp hA).1.1
    ((ForcingSupportSize.native_mapsTo hM w N B).mp hB).1.1
    (fun i x => (hMA i x).trans (hMB i x).symm)

theorem probe_map (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero N mulN eN f a b node : M.Carrier .set}
    (hCons : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hPath : Path w D mul e zero a node) :
    ∃ fa fb mapped, PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
      (Project.FirstOrderSemantics.reduct M).mem fb N ∧ fb ≠ eN ∧ MapsTo w N mapped ∧
      NodeMap node f mapped ∧ Path w N mulN eN zero fa mapped ∧
      ∀ fa' fb' other, PureKuratowski.PairMember M a fa' f → PureKuratowski.PairMember M b fb' f →
        MapsTo w N other → NodeMap node f other → fa' = fa ∧ fb' = fb ∧ other = mapped := by
  have hf := hCons.1.1
  obtain ⟨fa,hfa,_⟩ := hf.1.2 a hPath.2.1
  obtain ⟨fb,hfb,_⟩ := hf.1.2 b hb
  obtain ⟨mapped,hmapped,hMap⟩ := ConstructionProbeMappedPath.exists_node_map hM hPath.1 hf
  have hneN : fb ≠ eN := fun heq => hne (hCons.1.2 b e eN (heq ▸ hfb) hOne)
  refine ⟨fa,fb,mapped,hfa,hfb,hf.2 b fb hfb,hneN,hmapped,hMap,
    ConstructionProbeMappedPath.mapped_path hPath hf hmapped hMap hPres hOne hfa,?_⟩
  intro fa' fb' other hfa' hfb' hOther hOtherMap
  exact ⟨function_unique hf.1 hfa' hfa,function_unique hf.1 hfb' hfb,node_map_unique hM hOther hmapped hOtherMap hMap⟩

/-- Both source Request.map branches. No profiles are assumed or transported
as request data: only the original parameters/path/prescription are mapped. -/
def MapsRequests (w D mul e zero N mulN eN f : M.Carrier .set) : Prop :=
  (∀ a b node, (Project.FirstOrderSemantics.reduct M).mem b D → b ≠ e → Path w D mul e zero a node →
    ∃ fa fb mapped, PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
      (Project.FirstOrderSemantics.reduct M).mem fb N ∧ fb ≠ eN ∧ MapsTo w N mapped ∧
      NodeMap node f mapped ∧ Path w N mulN eN zero fa mapped ∧
      ∀ fa' fb' other, PureKuratowski.PairMember M a fa' f → PureKuratowski.PairMember M b fb' f →
        MapsTo w N other → NodeMap node f other → fa' = fa ∧ fb' = fb ∧ other = mapped) ∧
  ∀ n P, (Project.FirstOrderSemantics.reduct M).mem n w →
    (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) → Prescription n D P → Valid n D mul P →
    ∃ PN, ConstructionMergerPrescriptionMap.Graph P f PN ∧ ConstructionMergerPrescriptionMap.Mapped P f PN ∧
      (Project.FirstOrderSemantics.reduct M).mem n w ∧ (∃ i, (Project.FirstOrderSemantics.reduct M).mem i n) ∧
      Prescription n N PN ∧ Valid n N mulN PN ∧
      ∀ other, ConstructionMergerPrescriptionMap.Graph P f other → other = PN

theorem maps_requests (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero N mulN eN f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hCons : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul) :
    MapsRequests w D mul e zero N mulN eN f := by
  refine ⟨fun _ _ _ hb hne hp => probe_map hM hCons hPres hOne hb hne hp,?_⟩
  intro n P hn hnp hP hValid
  obtain ⟨PN,hGraph,hMap,hPN,hValidIff,_,hUnique⟩ :=
    ConstructionMergerPrescriptionMap.exists_system hM hm hmN hP hCons hPres hJoins
  exact ⟨PN,hGraph,hMap,hn,hnp,hPN,hValidIff.mpr hValid,hUnique⟩

end PPAC.Migration.ConstructionRequestMaps
