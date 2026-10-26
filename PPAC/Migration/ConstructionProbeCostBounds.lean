/- Pinned ProbeMargins.Path.letter_inside_cost / target_outside_cost.
Use the additive form of the source bounds and construct the actual bounded
sum cuts. The source old point-margin consequence remains an explicit input;
the inside/outside conclusions and the letter floor are not assumed. -/
import PPAC.Migration.ConstructionCutAddition
import PPAC.Migration.ConstructionProbeLetterFloorSyntax
import PPAC.Migration.ConstructionProbeSharedIntersections

namespace PPAC.Migration.ConstructionProbeCostBounds
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionCutAddition
open ConstructionProbeLetterFloor
open ConstructionProbeAlphabet (InCone)
open ConstructionProbeCones (ConeLaws JoinProperty)
open ConstructionProbeAction (ActionLaws)
open ConstructionProbeTarget (TargetLaws)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Non-strict additive consequence of the source old HeightCost.point_margin. -/
def PointBound (hM : FirstOrder.Theory.Models M nativeZF) (w D mul H C : M.Carrier .set) : Prop :=
  ∀ x y d hx hy cd, PureKuratowski.PairMember M x hx H → PureKuratowski.PairMember M y hy H →
    PureKuratowski.PairMember M d cd C → Divides D mul x y → Divides D mul d y →
    ¬ Divides D mul d x → AddBound hM w hx cd hy

def BoundedAdd (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b upper : M.Carrier .set) : Prop :=
  AddBound hM w a b upper ∧ ∃ c, Cut hM w Q c ∧ SumCut hM w Q a b c ∧ Subset c upper

def CostBounds (hM : FirstOrder.Theory.Models M nativeZF) (w Q D mul S A K H C F : M.Carrier .set) : Prop :=
  ∀ s v, PureKuratowski.PairMember M s v F →
    (∀ x d hx cd, (Project.FirstOrderSemantics.reduct M).mem x D →
      (Project.FirstOrderSemantics.reduct M).mem d D → InCone S A x s → InCone S A d s →
      ¬ Divides D mul d x → PureKuratowski.PairMember M x hx H → PureKuratowski.PairMember M d cd C →
      BoundedAdd hM w Q hx cd v) ∧
    (∀ t d ht cd, PureKuratowski.PairMember M s t K → (Project.FirstOrderSemantics.reduct M).mem d D →
      Divides D mul d t → ¬ InCone S A d s → PureKuratowski.PairMember M t ht H →
      PureKuratowski.PairMember M d cd C → BoundedAdd hM w Q v cd ht)

/-- Minimality against every internal set identifies the floor with its exact
height-image union; no external enumeration or chosen representative occurs. -/
theorem floor_member (hM : FirstOrder.Theory.Models M nativeZF) {D S A H s v p : M.Carrier .set}
    (hv : Floor D S A H s v) : (Project.FirstOrderSemantics.reduct M).mem p v ↔
      ∃ x c, (Project.FirstOrderSemantics.reduct M).mem x D ∧ InCone S A x s ∧
        PureKuratowski.PairMember M x c H ∧ (Project.FirstOrderSemantics.reduct M).mem p c := by
  obtain ⟨family,hf,hu,hl⟩ := hv
  obtain ⟨union,he⟩ := KP.exists_union (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) family
  have hvu : Subset v union := hl union (fun c hc q hq => (he q).mpr ⟨c,hc,hq⟩)
  constructor
  · intro hp
    obtain ⟨c,hc,hpc⟩ := (he p).mp (hvu p hp)
    obtain ⟨x,hx,hcone,hxc⟩ := (hf c).mp hc
    exact ⟨x,c,hx,hcone,hxc,hpc⟩
  · rintro ⟨x,c,hx,hcone,hxc,hpc⟩
    exact hu c ((hf c).mpr ⟨x,hx,hcone,hxc⟩) p hpc

section Actual
variable {hM : FirstOrder.Theory.Models M nativeZF}
variable {w Q R D mul e S I A K projection T H C zero node factor : M.Carrier .set}
variable (hm : LeftCancelMonoid D mul e) (hI : Representatives D S I) (hA : MapsTo I S A)
variable (hK : MapsTo S D K) (hTarget : TargetLaws mul projection T A K)
variable (hH : HeightOrder D mul R H) (hPoint : PointBound hM w D mul H C)
variable (hCones : ConeLaws w D mul e zero node factor S projection A)
include hm hI hA hK hTarget hH hPoint hCones

theorem letter_inside_cost (hJ : ConditionalJoins D mul) {s v x d hx cd : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (hv : Floor D S A H s v)
    (hxD : (Project.FirstOrderSemantics.reduct M).mem x D) (hdD : (Project.FirstOrderSemantics.reduct M).mem d D)
    (hxs : InCone S A x s) (hds : InCone S A d s) (hdx : ¬ Divides D mul d x)
    (hxh : PureKuratowski.PairMember M x hx H) (hdc : PureKuratowski.PairMember M d cd C) :
    AddBound hM w hx cd v := by
  obtain ⟨t,ht,_⟩ := hK.1.2 s hs
  have htD := hK.2 s t ht
  obtain ⟨j,hj,hJoin⟩ := hJ x d t hxD hdD htD
    (ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hTarget hxs ht)
    (ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hTarget hds ht)
  have hjj : Divides D mul j j := ⟨e,hm.1.1,((hm.1.2 j hj j).2).mpr rfl⟩
  obtain ⟨hxj,hdj⟩ := (hJoin j hj).mpr hjj
  have hjs := (hCones.2.2.2.1 x d j s hxD hdD hj hJoin).mp ⟨hxs,hds⟩
  obtain ⟨c,hjc,_⟩ := hH.1.1.2 j hj
  have hcv : Subset c v := by
    obtain ⟨family,hf,hu,_⟩ := hv
    exact hu c ((hf c).mpr ⟨j,hj,hjs,hjc⟩)
  exact bound_mono (hPoint x j d hx c cd hxh hjc hdc hxj hdj hdx) hcv

theorem target_outside_cost (hAction : ActionLaws mul e S A) {s v t d ht cd : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (hv : Floor D S A H s v)
    (hst : PureKuratowski.PairMember M s t K) (hdD : (Project.FirstOrderSemantics.reduct M).mem d D)
    (hdt : Divides D mul d t) (hdn : ¬ InCone S A d s)
    (hth : PureKuratowski.PairMember M t ht H) (hdc : PureKuratowski.PairMember M d cd C) :
    AddBound hM w v cd ht := by
  have hxbound : ∀ x c, (Project.FirstOrderSemantics.reduct M).mem x D → InCone S A x s →
      PureKuratowski.PairMember M x c H → AddBound hM w c cd ht := by
    intro x c _ hxs hxc
    exact hPoint x t d c ht cd hxc hth hdc
      (ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hTarget hxs hst) hdt
      (fun hdx => hdn (hCones.2.2.1 d x s hdD hdx hxs))
  obtain ⟨he,hhe,_⟩ := hH.1.1.2 e hm.1.1
  have hUnit := hxbound e he hm.1.1 (ConstructionProbeCones.one_inCone hAction hs) hhe
  have hFloor := (floor_bounds hm hI hA hK hTarget hH hAction hs hv).2.2 t ht hst hth
  intro p hp
  rcases hp with hp | hp | ⟨q,r,z,hq,hr,hz,hpz⟩
  · exact hFloor p hp
  · exact hUnit p (Or.inr (Or.inl hp))
  · obtain ⟨x,c,hx,hxs,hxc,hqc⟩ := (floor_member hM hv).mp hq
    exact hxbound x c hx hxs hxc p (Or.inr (Or.inr ⟨q,r,z,hqc,hr,hz,hpz⟩))

theorem exists_cost_bounds
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hC : MapsTo D R C) (hJ : ConditionalJoins D mul)
    (hAction : ActionLaws mul e S A) : ∃ F, MapsTo S R F ∧ Graph D S A H F ∧
      FloorLaws D S A K H F ∧ CostBounds hM w Q D mul S A K H C F := by
  obtain ⟨F,hF,hGraph,hFloor⟩ := exists_floor_graph hm hI hA hK hTarget hH hR hAction
  refine ⟨F,hF,hGraph,hFloor,?_⟩
  intro s v hfv
  obtain ⟨hs,hv⟩ := (hGraph s v).mp hfv
  have hvCut := (hR v).mp (hF.2 s v hfv)
  constructor
  · intro x d hx cd hxD hdD hxs hds hdx hxh hdc
    have hb := letter_inside_cost hm hI hA hK hTarget hH hPoint hCones hJ hs hv hxD hdD hxs hds hdx hxh hdc
    exact ⟨hb,exists_bounded_sum hM hw hQ ((hR hx).mp (hH.1.2 x hx hxh)) ((hR cd).mp (hC.2 d cd hdc)) hvCut hb⟩
  · intro t d ht cd hst hdD hdt hdn hth hdc
    have hb := target_outside_cost hm hI hA hK hTarget hH hPoint hCones hAction hs hv hst hdD hdt hdn hth hdc
    exact ⟨hb,exists_bounded_sum hM hw hQ hvCut ((hR cd).mp (hC.2 d cd hdc)) ((hR ht).mp (hH.1.2 t ht hth)) hb⟩

end Actual
end PPAC.Migration.ConstructionProbeCostBounds
