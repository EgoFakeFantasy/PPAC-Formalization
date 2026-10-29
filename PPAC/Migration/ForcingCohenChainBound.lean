/- Pinned AssignedGraphs.antichain_continuum:461-464 and the actual hcc
consumers in CodeCardinals:98-102,282-286. Reuse the completed antichain
proof and the already proved internal continuum fixed-power theorem. -/
import PPAC.Migration.ForcingCohenCounting

namespace PPAC.Migration.ForcingCohenChainBound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal compatibility on the ACTUAL condition carrier, bounded on both coordinates. -/
def Graph (P R : M.Carrier .set) : Prop := ∀ p q, PureKuratowski.PairMember M p q R ↔
  (Project.FirstOrderSemantics.reduct M).mem p P ∧ (Project.FirstOrderSemantics.reduct M).mem q P ∧
    ConstructionCohenCompatibility.Compatible p q

def graph {m} (P R : Fin m) : Project.Formula 1 m := .forallE (.forallE (.iff
  (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound R.succ.succ))
  (.conj (.mem (.bound 1) (.bound P.succ.succ)) (.conj (.mem .newest (.bound P.succ.succ))
    (ConstructionCompatiblePlacement.compatible (1 : Fin (m+2)) 0)))))

theorem graph_freeClosed {m} (P R : Fin m) : (graph P R).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (P R : Fin m) :
    Project.Formula.satisfies ρ (graph P R) ↔ Graph (ρ.bound P) (ρ.bound R) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    ConstructionCompatiblePlacement.compatible_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) (P : M.Carrier .set) : ∃ R, Graph P R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨X,hX⟩ := ZF.exists_cartesianProduct hZF I P P
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0,fun _ => P⟩
  let φ : Project.UnarySchema 0 := {
    body := .existsE (.existsE (.conj (PureKuratowskiProject.convention.code (.bound 2) (.bound 1) .newest)
      (ConstructionCompatiblePlacement.compatible (1 : Fin 3) 0)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionCompatiblePlacement.compatible_freeClosed] }
  have hφ t : φ.denote ρ t ↔ ∃ p q, PureKuratowski.Code M t p q ∧ ConstructionCohenCompatibility.Compatible p q := by
    simp only [φ,Project.UnarySchema.denote,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,I.satisfies_code_iff,ConstructionCompatiblePlacement.compatible_semantics hM]
    rfl
  obtain ⟨R,hR⟩ := ZF.separation_exists_d hZF φ ρ X
  refine ⟨R,fun p q => ⟨?_,?_⟩⟩
  · rintro ⟨t,ht,htR⟩
    obtain ⟨htX,htφ⟩ := (hR t).mp htR
    obtain ⟨p',hp,q',hq,ht'⟩ := (hX t).mp htX
    obtain ⟨rfl,rfl⟩ := I.injective ht ht'
    obtain ⟨p'',q'',ht'',hc⟩ := (hφ t).mp htφ
    obtain ⟨rfl,rfl⟩ := I.injective ht ht''
    exact ⟨hp,hq,hc⟩
  · rintro ⟨hp,hq,hc⟩
    obtain ⟨t,ht⟩ := I.total p q
    exact ⟨t,ht,(hR t).mpr ⟨(hX t).mpr ⟨p,hp,q,hq,ht⟩,(hφ t).mpr ⟨p,q,ht,hc⟩⟩⟩

theorem graph_refl {S w P R : M.Carrier .set} (hP : ForcingCohenConditions.Carrier S w P) (hR : Graph P R) :
    ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → PureKuratowski.PairMember M p p R :=
  fun p hp => (hR p p).mpr ⟨hp,hp,((hP p).mp hp).2.1⟩

/-- Discharge the existing ChainBound premise with the proved ACTUAL Cohen antichain theorem. -/
theorem chain_bound (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w mu Coord B S P R Power : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hPower : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) Power w mu)
    (hPow : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Power mu)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : ForcingCohenCoordinates.Cartesian Coord B S) (hP : ForcingCohenConditions.Carrier S w P) (hR : Graph P R) :
    ForcingChainBound.ChainBound (KuratowskiZF.interpretation hM) P R mu := by
  intro A hA hanti
  apply ForcingCohenAntichain.cardinal_le hM hZFC hw hmu hPower hPow hTwo hS hP hA
  intro p hp q hq hc
  exact hanti p hp q hq ((hR p q).mpr ⟨hA p hp,hA q hq,hc⟩)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 1) (.bound 1) (.bound 0))
    (.imp (ForcingProductParameters.two (3 : Fin 6))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 6) 3 4))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (4 : Fin 6) 0 5))
    (.existsE (.conj (graph (6 : Fin 7) 0) (.conj
      (ForcingChainBound.chainBound (𝒞 := PureKuratowskiProject.convention) (.bound 6) .newest (.bound 2))
      (ForcingChainBound.compatibleRefl (𝒞 := PureKuratowskiProject.convention) (.bound 6) .newest))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isInfiniteCardinal,
    Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,ProjectSyntax.freeClosed,
    ForcingProductParameters.two_freeClosed,graph_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence constructionSentence := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff I hZF.1,Project.Formula.satisfies_isCardinalExponentiation_iff I hZF.1,
    ForcingProductParameters.two_semantics,GodelDefRecursion.encode_semantics hZF.1,
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.carrier_semantics (M := M),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,graph_semantics hM,
    ForcingChainBound.chainBound_semantics I hZF.1,ForcingChainBound.compatibleRefl,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff I]
  intro hw hmu hpow hTwo hS hP
  obtain ⟨Power,hPower⟩ := ZF.exists_functionSpace hZF I (bound 0) (bound 1)
  obtain ⟨Pmu,hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hM hpow hPower).2.symm hZF I
  obtain ⟨R,hR⟩ := exists_graph hM (bound 5)
  exact ⟨R,hR,chain_bound hM hZFC hw hmu hPower ⟨Pmu,hPmu.1⟩ hTwo hS hP hR,graph_refl hP hR⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact construction_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

/-- Actual continuum instance; the power set and its cardinal are constructed, not assumed. -/
theorem continuum (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w Coord B S P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : ForcingCohenCoordinates.Cartesian Coord B S) (hP : ForcingCohenConditions.Carrier S w P) :
    ∃ Pow c R, (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Pow w ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) c Pow ∧
      (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w c ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) c c w ∧
      Graph P R ∧ ForcingChainBound.ChainBound (KuratowskiZF.interpretation hM) P R c ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → PureKuratowski.PairMember M p p R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0,fun _ => w⟩
  have hSat : Project.Formula.satisfies ρ (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies ρ (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact (Structure.satisfiesSentence_iff _ _).mp (hZFC.2 Axioms.choice .choice) ρ.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hM ρ).mp hSat
  obtain ⟨Pow,c,hPow,hc,hInfinite,hpower⟩ := ConstructionConcreteCardinals.continuum_fixed_countable_power hM hChoice hw
  obtain ⟨Space,hSpace⟩ := ZF.exists_functionSpace hZF I w c
  obtain ⟨Sc,hSc⟩ := (ConstructionConcreteCardinals.normalize_power hM hpower hSpace).2.symm hZF I
  obtain ⟨R,hR⟩ := exists_graph hM P
  exact ⟨Pow,c,R,hPow,hc,hInfinite,hpower,hR,
    chain_bound hM hZFC hw hInfinite hSpace ⟨Sc,hSc.1⟩ hTwo hS hP hR,graph_refl hP hR⟩

def continuumSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (ForcingProductParameters.two (2 : Fin 5))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (1 : Fin 5) 2 3))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (3 : Fin 5) 0 4))
    (.existsE (.existsE (.existsE (.conj (Project.Formula.isPowerSet (.bound 2) (.bound 3))
      (.conj (Project.Formula.isCardinalOf PureKuratowskiProject.convention (.bound 1) (.bound 2))
      (.conj (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 3) (.bound 1))
      (.conj (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 1) (.bound 1) (.bound 3))
      (.conj (graph (7 : Fin 8) 0) (.conj
        (ForcingChainBound.chainBound (𝒞 := PureKuratowskiProject.convention) (.bound 7) .newest (.bound 1))
        (ForcingChainBound.compatibleRefl (𝒞 := PureKuratowskiProject.convention) (.bound 7) .newest))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isPowerSet,
    Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
    ProjectSyntax.freeClosed,ForcingProductParameters.two_freeClosed,graph_freeClosed]

theorem continuum_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence continuumSentence := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    ForcingProductParameters.two_semantics,GodelDefRecursion.encode_semantics hZF.1,
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.carrier_semantics (M := M),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isPowerSet_iff,
    Project.Formula.satisfies_isCardinalOf_iff I hZF.1,Project.Formula.satisfies_isInfiniteCardinal_iff I hZF.1,
    Project.Formula.satisfies_isCardinalExponentiation_iff I hZF.1,graph_semantics hM,
    ForcingChainBound.chainBound_semantics I hZF.1,ForcingChainBound.compatibleRefl,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff I]
  exact fun hw hTwo hS hP => continuum hM hZFC hw hTwo hS hP

theorem continuum_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative continuumSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact continuum_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

end PPAC.Migration.ForcingCohenChainBound
