/- Pinned AssignedGraphs.Condition.antichain_cardinal_le:403-457.
Consume the SAME internal code/decode/choice/flip operation and the completed
CountableHull. Discharge hin and pack; ordinary nativeZF certificate relative
to the SAME existing internal L discharges source object Choice. -/
import PPAC.Migration.ForcingCohenOperation
import PPAC.Migration.ForcingProductParameters

namespace PPAC.Migration.ForcingCohenAntichain
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingWithTopCarrier (Empty)
open ForcingCohenRestriction (Covered)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Antichain (A : M.Carrier .set) : Prop := ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A →
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q A → ConstructionCohenCompatibility.Compatible p q → p = q

def antichain {m} (A : Fin m) : Project.Formula 1 m := .forallE (.forallE (.imp
  (.mem (.bound 1) (.bound A.succ.succ)) (.imp (.mem .newest (.bound A.succ.succ))
    (.imp (ConstructionCompatiblePlacement.compatible (1 : Fin (m+2)) 0)
      (Project.Formula.extensionalEq (.bound 1) .newest)))))

theorem antichain_freeClosed {m} (A : Fin m) : (antichain A).FreeClosed := by
  simp -implicitDefEqProofs [antichain,Definitional.Formula.FreeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem antichain_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (A : Fin m) :
    Project.Formula.satisfies ρ (antichain A) ↔ Antichain (ρ.bound A) := by
  simp only [antichain,Antichain,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,ConstructionCompatiblePlacement.compatible_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact ⟨fun h p hp q hq hc => h p q hp hq hc, fun h p q hp hq hc => h p hp q hq hc⟩

/-- Source hflip, using an ACTUAL constant internal function and label (false,zero). -/
theorem hull_flip_closed (hM : FirstOrder.Theory.Models M nativeZF)
    {z w W P Space C D Q F B L O mu Y : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hL : ForcingCohenCoordinates.Cartesian B w L)
    (hO : ForcingCohenOperation.Graph z L Space C D Q F O)
    (hY : ForcingCountableHull.Hull (KuratowskiZF.interpretation hM) w L W O z mu Y)
    (hzB : (Project.FirstOrderSemantics.reduct M).mem z B)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem z w) : ForcingCohenFlip.Closed F Y := by
  intro x y hx hxy
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨f,hf,he⟩ := ZF.exists_constantFunction hZF I (source := w) hx
  have hfY := (ForcingSupportSize.native_mapsTo hM w Y f).mpr hf
  have hfW : MapsTo w W f := ⟨hfY.1,fun n v hnv => hY.1 v (hfY.2 n v hnv)⟩
  obtain ⟨a,ha⟩ := I.total z z
  have haL := (hL a).mpr ⟨z,hzB,z,hzw,ha⟩
  apply hY.2.2.2 a f haL hf y
  exact (hO a f y).mpr ⟨haL,(h.1 f).mpr hfW,z,z,ha,Or.inl ⟨rfl,x,(he z x).mpr ⟨hzw,rfl⟩,hxy⟩⟩

/-- Source hbS: evaluate the true branch on the SAME code of d and recover decode(code d). -/
theorem hull_selected_code (hM : FirstOrder.Theory.Models M nativeZF)
    {z o w W P Space C D Q F B L O mu Y d f q g : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hL : ForcingCohenCoordinates.Cartesian B w L)
    (hO : ForcingCohenOperation.Graph z L Space C D Q F O)
    (hY : ForcingCountableHull.Hull (KuratowskiZF.interpretation hM) w L W O z mu Y)
    (hoB : (Project.FirstOrderSemantics.reduct M).mem o B) (hoz : o ≠ z)
    (hdf : PureKuratowski.PairMember M d f C) (hdq : PureKuratowski.PairMember M d q Q)
    (hqg : PureKuratowski.PairMember M q g C) (hfY : MapsTo w Y f) : MapsTo w Y g := by
  have hfSpace := (h.1 f).mpr (h.2.1.2 d f hdf).1
  obtain ⟨r,hfr,_⟩ := h.2.2.1.1.2 f hfSpace
  have er := ForcingCohenCodes.data_decode_code hM h hdf hfr
  subst r
  have hcode := h.2.1.2 q g hqg
  refine ⟨hcode.1.1,fun n y hny => ?_⟩
  have hn := ForcingConditionGraphs.function_input hcode.1.1 hny
  obtain ⟨a,ha⟩ := KuratowskiZF.exists_code hM o n
  have haL := (hL a).mpr ⟨o,hoB,n,hn,ha⟩
  apply hY.2.2.2 a f haL ((ForcingSupportSize.native_mapsTo hM w Y f).mp hfY) y
  exact (hO a f y).mpr ⟨haL,hfSpace,o,n,ha,Or.inr ⟨hoz,d,q,g,hfr,hdq,hqg,hny⟩⟩

/-- Source hin, with restrictedGraph, compatibleChoice_spec, hbits and hbp consumed. -/
theorem covered_antichain (hM : FirstOrder.Theory.Models M nativeZF)
    {z o w B Coord S W P A Space C D Q F L O mu Y : M.Carrier .set}
    (hz : Empty z) (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem z w)
    (hS : ForcingCohenCoordinates.Cartesian Coord B S) (hP : ForcingCohenConditions.Carrier S w P)
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A P) (hanti : Antichain A)
    (h : ForcingCohenCodes.Data w W P Space C D) (hQ : ForcingCohenCompatibleChoice.Selection A P Q)
    (hF : ForcingCohenFlip.Graph z o W F) (hL : ForcingCohenCoordinates.Cartesian B w L)
    (hO : ForcingCohenOperation.Graph z L Space C D Q F O)
    (hY : ForcingCountableHull.Hull (KuratowskiZF.interpretation hM) w L W O z mu Y) :
    ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A → Covered p Y := by
  have hzB := (hB z).mpr (Or.inl ho.predecessor_mem)
  have hbits := ForcingCohenFlip.flip_bits hM hz ho hB hF hY.1
    (hull_flip_closed hM h hL hO hY hzB hzw)
  have hoz : o ≠ z := by intro e; exact hz z (e ▸ ho.predecessor_mem)
  intro p hpA
  have hp := (hP p).mp (hA p hpA)
  obtain ⟨d,hd⟩ := ForcingCohenRestriction.exists_restriction hM Y p
  have hdP := (hP d).mpr (ForcingCohenRestriction.restricted_condition hM hp hd)
  obtain ⟨f,hdf,_⟩ := h.2.1.1.2 d hdP
  have hfY := ForcingCohenRestriction.code_into hM (h.2.1.2 d f hdf)
    (ForcingCohenRestriction.restricted_covered hd) hz hY.2.2.1
  obtain ⟨q,hdq,_⟩ := hQ.1.1.2 d hdP
  obtain ⟨hqA,hdcompat⟩ := ForcingCohenCompatibleChoice.selection_spec hQ hdq
    ⟨p,hpA,ForcingCohenRestriction.restricted_compatible hp hd⟩
  obtain ⟨g,hqg,_⟩ := h.2.1.1.2 q (hA q hqA)
  have hgY := hull_selected_code hM h hL hO hY hB.predecessor_mem hoz hdf hdq hqg hfY
  have hqcover := ForcingCohenRestriction.covered_of_code (h.2.1.2 q g hqg) hgY hM
  have hpq := ForcingCohenFlip.compatible_of_bits hM hS hp ((hP q).mp (hA q hqA)) hd hqcover hbits hdcompat
  exact (hanti p hpA q hqA hpq).symm ▸ hqcover

/-- Source pack is the restriction of the SAME code family, retargeted to the full function space. -/
theorem pack_injection (hM : FirstOrder.Theory.Models M nativeZF)
    {z w W P A Space C D Y SY : M.Carrier .set} (hz : Empty z)
    (hzY : (Project.FirstOrderSemantics.reduct M).mem z Y)
    (h : ForcingCohenCodes.Data w W P Space C D)
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A P)
    (hcover : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A → Covered p Y)
    (hSY : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) SY w Y) :
    ∃ K, (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) K A SY := by
  obtain ⟨K,hK⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) C A
  have hMap : MapsTo A SY K := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro t ht
      obtain ⟨p,f,hpf⟩ := hK.1 t ht
      exact ⟨p,f,((hK.2 p f).mp ⟨t,hpf,ht⟩).1,hpf⟩
    · intro p hp
      obtain ⟨f,hpf,_⟩ := h.2.1.1.2 p (hA p hp)
      exact ⟨f,(hK.2 p f).mpr ⟨hp,hpf⟩,fun g hg =>
        ForcingConditionGraphs.function_unique h.2.1.1 ((hK.2 p g).mp hg).2 hpf⟩
    · intro p f hpf
      obtain ⟨hp,hpf⟩ := (hK.2 p f).mp hpf
      exact (hSY f).mpr ((ForcingSupportSize.native_mapsTo hM w Y f).mp
        (ForcingCohenRestriction.code_into hM (h.2.1.2 p f hpf) (hcover p hp) hz hzY))
  exact ⟨K,(ForcingSupportSize.native_injection hM A SY K).mp ⟨hMap,fun p q f hp hq =>
    ForcingCohenCodes.family_injective hM h.2.1 ((hK.2 p f).mp hp).2 ((hK.2 q f).mp hq).2⟩⟩

/-- Entire source antichain theorem. All operations/hull/selection/pack witnesses are constructed. -/
theorem cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC)
    {w mu Coord B S P A Power : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hPower : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) Power w mu)
    (hPow : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Power mu)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : ForcingCohenCoordinates.Cartesian Coord B S) (hP : ForcingCohenConditions.Carrier S w P)
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A P) (hanti : Antichain A) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) A mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨o,⟨z,hz,ho⟩,hB⟩ := hTwo
  obtain ⟨z',hz',hzw'⟩ := hw.1.1
  have hzw := ForcingWithTopCarrier.empty_unique hM hz' hz ▸ hzw'
  obtain ⟨o',ho',how'⟩ := hw.1.2 z hzw
  have how := Structure.SuccessorOf.eq hZF.1 ho' ho ▸ how'
  have hBw : (Project.FirstOrderSemantics.reduct M).MemberSubset B w := by
    intro b hb
    exact (ForcingCohenFlip.two_cases hM hz ho hB hb).elim (fun e => e ▸ hzw) (fun e => e ▸ how)
  obtain ⟨Bw,hBw⟩ := ZF.exists_inclusionInjection hZF I hBw
  obtain ⟨wmu,hwmu⟩ := hmu.2
  have hBmu := ZF.exists_compositionInjection hZF I hBw hwmu
  obtain ⟨L,hL⟩ := ForcingCohenCoordinates.exists_cartesian hM B w
  have hLmu := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hBmu hmu.2 hL
  obtain ⟨W,hW⟩ := ForcingWithTopCarrier.exists_carrier hM S
  obtain ⟨Space,C,D,h⟩ := ForcingCohenCodes.data_exists hM hZFC hw hW hP
  obtain ⟨Q,hQ⟩ := ForcingCohenCompatibleChoice.exists_selection hM hZFC hP hA
  obtain ⟨F,hF⟩ := ForcingCohenFlip.exists_flip hM hz ho hB hS hW
  obtain ⟨O,hO⟩ := ForcingCohenOperation.exists_graph (z := z) hM h hQ.1 hF.1 hL
  have hop := ForcingCohenOperation.operation hM h hQ.1 hF.1 hL hO
  obtain ⟨Y,hY⟩ := ForcingCountableHull.exists_closed I hZF hw hmu hLmu hPower hPow hop ((hW z).mpr (Or.inl hz))
  have hcover := covered_antichain hM hz ho hB hzw hS hP hA hanti h hQ hF hL hO hY
  obtain ⟨SY,hSY⟩ := ZF.exists_functionSpace hZF I w Y
  obtain ⟨K,hK⟩ := pack_injection hM hz hY.2.2.1 h hA hcover hSY
  obtain ⟨Ymu,hYmu⟩ := hY.2.1
  obtain ⟨idw,hidw⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨J,hJ⟩ := ZF.exists_functionSpaceTransportInjection hZF I hSY hPower hidw hYmu
  obtain ⟨AP,hAP⟩ := ZF.exists_compositionInjection hZF I hK hJ
  obtain ⟨Pmu,hPmu⟩ := hPow
  exact ZF.exists_compositionInjection hZF I hAP hPmu

/-- Literal source infinite fixed-point hypotheses; no code/hull/operation premises remain. -/
def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 1) (.bound 1) (.bound 0))
    (.imp (ForcingProductParameters.two (3 : Fin 7))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 7) 3 4))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (4 : Fin 7) 0 5))
    (.imp (Project.Formula.subset (.bound 6) (.bound 5)) (.imp (antichain (6 : Fin 7))
      (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 6) (.bound 1))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isInfiniteCardinal,
    Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,ProjectSyntax.freeClosed,
    ForcingProductParameters.two_freeClosed,antichain_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence boundSentence := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff I hZF.1,Project.Formula.satisfies_isCardinalExponentiation_iff I hZF.1,
    Project.Formula.satisfies_cardinalLessOrEqual_iff I hZF.1,ForcingProductParameters.two_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.carrier_semantics (M := M),
    Project.Formula.satisfies_subset_iff,antichain_semantics hM]
  intro hw hmu hpow hTwo hS hP hA hanti
  obtain ⟨Power,hPower⟩ := ZF.exists_functionSpace hZF I (bound 0) (bound 1)
  obtain ⟨Pmu,hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hM hpow hPower).2.symm hZF I
  exact cardinal_le hM hZFC hw hmu hPower ⟨Pmu,hPmu.1⟩ hTwo hS hP hA hanti

/-- SAME completed internal L discharges object Choice; ordinary nativeZF remains the background. -/
theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative boundSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact bound_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

end PPAC.Migration.ForcingCohenAntichain
