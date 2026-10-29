/- Pinned LocalRecords.Condition.graph_code/cardinal_le:61-104.
Reuse the already constructed code family and pack_injection. Only the
actual Option-carrier size and source coordinate products are assembled. -/
import PPAC.Migration.ForcingCohenAntichain

namespace PPAC.Migration.ForcingCohenCounting
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source |Option S| <= mu, including S empty, with an actual internal injection. -/
theorem option_bound (hM : FirstOrder.Theory.Models M nativeZF) {w mu S W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hS : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) S mu)
    (hW : ForcingWithTopCarrier.Carrier S W) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) W mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨z,hz,hzw⟩ := hw.1.1
  obtain ⟨o,ho,how⟩ := hw.1.2 z hzw
  have hzo : z ≠ o := by intro e; exact hz z (e.symm ▸ ho.predecessor_mem)
  obtain ⟨J,hJ⟩ := hS
  obtain ⟨wmu,hwmu⟩ := hmu.2
  obtain ⟨dummy,hdummy,_⟩ := hwmu.1.2.2 z hzw
  obtain ⟨T,hT⟩ := ZF.exists_cartesianProduct hZF I w mu
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 4 :=
    (((⟨fun _ => J,fun _ => J⟩ : Env _ 1).push z).push o).push dummy
  let φ : Project.BinarySchema 4 := {body := (.disj
    (.conj (Project.Formula.isEmpty (.bound 1))
      (PureKuratowskiProject.convention.code .newest (.bound 4) (.bound 2)))
    (.existsE (.existsE (.conj (Project.Formula.isSingleton (.bound 3) (.bound 1))
      (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound 7))
        (PureKuratowskiProject.convention.code (.bound 2) (.bound 5) .newest))))))}
  have hφ x t : φ.denote ρ x t ↔ (Empty x ∧ PureKuratowski.Code M t z dummy) ∨
      ∃ s i, Single x s ∧ PureKuratowski.PairMember M s i J ∧ PureKuratowski.Code M t o i := by
    simp only [φ,Project.BinarySchema.denote,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_isSingleton_iff hZF.1,Project.Formula.satisfies_orderedPairMem_iff I,I.satisfies_code_iff]
    rfl
  obtain ⟨K,hK⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ (source := W) (target := T)
    (by
      intro x hx
      rcases (hW x).mp hx with he | ⟨s,hs,hxs⟩
      · obtain ⟨t,ht⟩ := I.total z dummy
        exact ⟨t,(hφ x t).mpr (Or.inl ⟨he,ht⟩)⟩
      · obtain ⟨i,_,hi⟩ := hJ.1.2.2 s hs
        obtain ⟨t,ht⟩ := I.total o i
        exact ⟨t,(hφ x t).mpr (Or.inr ⟨s,i,hxs,hi,ht⟩)⟩)
    (by
      intro x _ t v ht hv
      rcases (hφ x t).mp ht with ⟨he,ht⟩ | ⟨s,i,hxs,hi,ht⟩ <;>
        rcases (hφ x v).mp hv with ⟨hf,hv⟩ | ⟨r,j,hxr,hj,hv⟩
      · exact I.unique ht hv
      · exact (ForcingWithTopCarrier.single_nonempty hxr he).elim
      · exact (ForcingWithTopCarrier.single_nonempty hxs hf).elim
      · have es := ForcingWithTopCarrier.single_injective hxs hxr
        subst r
        have ei := hJ.1.1.2 s i j hi hj
        exact I.unique ht (ei.symm ▸ hv))
    (by
      intro x t _ ht
      rcases (hφ x t).mp ht with ⟨_,ht⟩ | ⟨s,i,_,hi,ht⟩
      · exact (hT t).mpr ⟨z,hzw,dummy,hdummy,ht⟩
      · exact (hT t).mpr ⟨o,how,i,hJ.1.output_mem_of_pairMember hi,ht⟩)
    (by
      intro x y t _ _ hx hy
      rcases (hφ x t).mp hx with ⟨he,ht⟩ | ⟨s,i,hxs,hi,ht⟩ <;>
        rcases (hφ y t).mp hy with ⟨hf,hv⟩ | ⟨r,j,hyr,hj,hv⟩
      · exact ForcingWithTopCarrier.empty_unique hM he hf
      · exact (hzo (I.injective ht hv).1).elim
      · exact (hzo (I.injective hv ht).1).elim
      · obtain ⟨_,eij⟩ := I.injective ht hv
        subst j
        have es := hJ.2 s r i hi hj
        exact ForcingWithTopCarrier.single_unique hM hxs (es.symm ▸ hyr))
  obtain ⟨idmu,hidmu⟩ := ZF.exists_identityBijection hZF I mu
  obtain ⟨Tmu,hTmu⟩ := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hmu.2 ⟨idmu,hidmu.1⟩ hT
  exact ZF.exists_compositionInjection hZF I hK hTmu

/-- No new enumeration: apply the SAME accepted pack to A=P and Y=Option S. -/
theorem carrier_bound (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w mu S P Power : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hPower : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) Power w mu)
    (hPow : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Power mu)
    (hS : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) S mu)
    (hP : ForcingCohenConditions.Carrier S w P) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) P mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨W,hW⟩ := ForcingWithTopCarrier.exists_carrier hM S
  obtain ⟨Wmu,hWmu⟩ := option_bound hM hw hmu hS hW
  obtain ⟨Space,C,D,h⟩ := ForcingCohenCodes.data_exists hM hZFC hw hW hP
  have hSpace : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace I Space w W :=
    fun f => (h.1 f).trans (ForcingSupportSize.native_mapsTo hM w W f)
  obtain ⟨z,hz⟩ := ForcingWithTopCarrier.exists_empty hM
  have hcover : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → ForcingCohenRestriction.Covered p W := by
    intro p hp s hs
    obtain ⟨y,hy⟩ := ForcingWithTopCarrier.exists_single hM s
    exact ⟨y,hy,(hW y).mpr (Or.inr ⟨s,((hP p).mp hp).1 s hs,hy⟩)⟩
  obtain ⟨K,hK⟩ := ForcingCohenAntichain.pack_injection hM hz ((hW z).mpr (Or.inl hz)) h (fun _ hp => hp) hcover hSpace
  obtain ⟨idw,hidw⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨J,hJ⟩ := ZF.exists_functionSpaceTransportInjection hZF I hSpace hPower hidw hWmu
  obtain ⟨KP,hKP⟩ := ZF.exists_compositionInjection hZF I hK hJ
  obtain ⟨Pmu,hPmu⟩ := hPow
  exact ZF.exists_compositionInjection hZF I hKP hPmu

/-- Literal source coordinate product (I x kappa) x Bool is mu-small. -/
theorem coordinates_bound (hM : FirstOrder.Theory.Models M nativeZF) {w mu X K B Coord S : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hX : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) X mu)
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) K mu)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hCoord : ForcingCohenCoordinates.Cartesian X K Coord) (hS : ForcingCohenCoordinates.Cartesian Coord B S) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) S mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨o,⟨z,hz,ho⟩,hB⟩ := hTwo
  obtain ⟨z',hz',hzw'⟩ := hw.1.1
  have hzw := ForcingWithTopCarrier.empty_unique hM hz' hz ▸ hzw'
  obtain ⟨o',ho',how'⟩ := hw.1.2 z hzw
  have how := Structure.SuccessorOf.eq hZF.1 ho' ho ▸ how'
  obtain ⟨Bw,hBw⟩ := ZF.exists_inclusionInjection hZF I (source := B) (target := w) (by
    intro b hb
    exact (ForcingCohenFlip.two_cases hM hz ho hB hb).elim (fun e => e ▸ hzw) (fun e => e ▸ how))
  obtain ⟨wmu,hwmu⟩ := hmu.2
  have hBmu := ZF.exists_compositionInjection hZF I hBw hwmu
  have hCmu := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hX hK hCoord
  exact ExistingCardinalBounds.infinite_product_l I hZF hw hmu hCmu hBmu hS

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 1) (.bound 1) (.bound 0))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 2) (.bound 1))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 3) (.bound 1))
    (.imp (ForcingProductParameters.two (4 : Fin 8))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 8) 3 5))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (5 : Fin 8) 4 6))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (6 : Fin 8) 0 7))
      (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 7) (.bound 1)))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isInfiniteCardinal,
    Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,ProjectSyntax.freeClosed,ForcingProductParameters.two_freeClosed]

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
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.carrier_semantics (M := M)]
  intro hw hmu hpow hX hK hTwo hC hS hP
  obtain ⟨Power,hPower⟩ := ZF.exists_functionSpace hZF I (bound 0) (bound 1)
  obtain ⟨Pmu,hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hM hpow hPower).2.symm hZF I
  exact carrier_bound hM hZFC hw hmu hPower ⟨Pmu,hPmu.1⟩ (coordinates_bound hM hw hmu hX hK hTwo hC hS) hP

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative boundSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact bound_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))


/-- CodeCardinals.ordinalType_cardinal_le, hrec: construct the literal M x (M x Condition M kappa). -/
theorem records_bound (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w mu X K B Coord S P Power : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hPower : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) Power w mu)
    (hPow : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Power mu)
    (hX : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) X mu)
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) K mu)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hCoord : ForcingCohenCoordinates.Cartesian X K Coord) (hS : ForcingCohenCoordinates.Cartesian Coord B S)
    (hP : ForcingCohenConditions.Carrier S w P) :
    ∃ Inner Records, ForcingCohenCoordinates.Cartesian X P Inner ∧
      ForcingCohenCoordinates.Cartesian X Inner Records ∧
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Records mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hPmu := carrier_bound hM hZFC hw hmu hPower hPow (coordinates_bound hM hw hmu hX hK hTwo hCoord hS) hP
  obtain ⟨Inner,hInner⟩ := ZF.exists_cartesianProduct hZF I X P
  obtain ⟨Records,hRecords⟩ := ZF.exists_cartesianProduct hZF I X Inner
  have hInnerMu := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hX hPmu hInner
  exact ⟨Inner,Records,hInner,hRecords,ExistingCardinalBounds.infinite_product_l I hZF hw hmu hX hInnerMu hRecords⟩

def recordsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 1) (.bound 1) (.bound 0))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 2) (.bound 1))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 3) (.bound 1))
    (.imp (ForcingProductParameters.two (4 : Fin 8))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 8) 3 5))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (5 : Fin 8) 4 6))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (6 : Fin 8) 0 7))
      (.existsE (.existsE (.conj
        (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (4 : Fin 10) 9 1))
        (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (4 : Fin 10) 1 0))
          (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention .newest (.bound 3)))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isInfiniteCardinal,
    Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,ProjectSyntax.freeClosed,ForcingProductParameters.two_freeClosed]

theorem records_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence recordsSentence := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff I hZF.1,Project.Formula.satisfies_isCardinalExponentiation_iff I hZF.1,
    Project.Formula.satisfies_cardinalLessOrEqual_iff I hZF.1,ForcingProductParameters.two_semantics,
    GodelDefRecursion.encode_semantics hZF.1,ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingCohenConditions.carrier_semantics (M := M),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff]
  intro hw hmu hpow hX hK hTwo hC hS hP
  obtain ⟨Power,hPower⟩ := ZF.exists_functionSpace hZF I (bound 0) (bound 1)
  obtain ⟨Pmu,hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hM hpow hPower).2.symm hZF I
  exact records_bound hM hZFC hw hmu hPower ⟨Pmu,hPmu.1⟩ hX hK hTwo hC hS hP

theorem records_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative recordsSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact records_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

end PPAC.Migration.ForcingCohenCounting
