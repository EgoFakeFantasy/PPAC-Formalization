/- Representation adapters for pinned Models.ConcreteSystem.CardinalParameters.
Reuse existing ordinal enumeration/order type, native cardinal representatives,
function-space transport, exponent laws and original internal regularity.
All functions/cardinals remain sets in the same native model. -/
import PPAC.Migration.ConstructionIdealProbes
import YesMetaZFC.SetTheory.Card.OrdinalCardinality
import YesMetaZFC.SetTheory.Card.Arithmetic.Exponentiation
import YesMetaZFC.SetTheory.Card.Arithmetic.PowerSet

namespace PPAC.Migration.ConstructionConcreteCardinals
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem cardinal_of_set (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) (S : M.Carrier .set) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) c S := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨α,F,hα,hF,hSurj⟩ := ExistingOrdinalEnumeration.ordinal_enum_l
    (ConstructionDirectedCardinality.models_zfc hM hChoice) I S
  obtain ⟨G,hG⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I hα hF hSurj
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction hZF I hG.1.1 hG.1.2.1
  have hGA : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I G S A :=
    ⟨hG.1.1,hG.1.2.1,fun x hx => by
      obtain ⟨y,_,hxy⟩ := hG.1.2.2 x hx
      exact ⟨y,(hA y).mpr ⟨x,hxy⟩,hxy⟩⟩
  have hSA : (Project.FirstOrderSemantics.reduct M).Equinumerous I S A := by
    refine ⟨G,⟨hGA,hG.2⟩,?_⟩
    intro y hy
    obtain ⟨x,hxy⟩ := (hA y).mp hy
    exact ⟨x,hG.1.input_mem_of_pairMember hxy,hxy⟩
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset A α := by
    intro y hy
    obtain ⟨x,hxy⟩ := (hA y).mp hy
    exact hG.1.output_mem_of_pairMember hxy
  obtain ⟨R,β,_,hWell,hType⟩ := ZF.exists_membershipWellOrderType_of_subsetOrdinal hZF I hα hSub
  obtain ⟨c,hc,_⟩ := ZF.ordinalCardinal_existsUnique hZF I (hType.isOrdinal hZF I hWell)
  exact ⟨c,hc.1,hc.2.trans hZF I (((hType.equinumerous hZF I hWell).symm hZF I).trans hZF I (hSA.symm hZF I))⟩

theorem normalize_power (hM : FirstOrder.Theory.Models M nativeZF)
    {w c power space : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation
      (KuratowskiZF.interpretation hM) power c w)
    (hSpace : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace
      (KuratowskiZF.interpretation hM) space w c) :
    (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) power space := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨B,E,F,hB,hE,hF,hPower⟩ := hp
  have hBase := (Structure.Equinumerous.refl hZF I c).trans hZF I hB.2
  have hExponent := (Structure.Equinumerous.refl hZF I w).trans hZF I hE.2
  have hEquiv := ZF.equinumerous_functionSpace hZF I hSpace hF hExponent hBase
  exact ⟨hPower.1,hPower.2.trans hZF I (hEquiv.symm hZF I)⟩


/-- Pinned CardinalParameters.countable_bound, reusing the completed
ConstructionSaturationBoundedness cofinal-order-type argument. It applies
to every regular mu with omega in mu, not only successor cardinals. -/
theorem countable_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu f range : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hReg : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) mu)
    (hwMu : (Project.FirstOrderSemantics.reduct M).mem w mu)
    (hFunction : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo
      (KuratowskiZF.interpretation hM) f w mu)
    (hRange : (Project.FirstOrderSemantics.reduct M).IsRangeOf
      (KuratowskiZF.interpretation hM) range f) :
    (Project.FirstOrderSemantics.reduct M).IsBoundedSubsetOfOrdinal range mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset range mu := by
    intro x hx
    obtain ⟨i,hix⟩ := (hRange x).mp hx
    exact hFunction.output_mem_of_pairMember hix
  rcases Structure.bounded_or_cofinalSubset hZF hReg.isLimitOrdinal hSub with hBounded | hCofinal
  · exact hBounded
  · apply False.elim
    obtain ⟨relation,orderType,hRelation,hOrder,hType⟩ :=
      ZF.exists_membershipWellOrderType_of_subsetOrdinal hZF I hReg.isCardinal.1 hSub
    have hOrdinal := hType.isOrdinal hZF I hOrder
    obtain ⟨toRange,hToRange⟩ := (hType.equinumerous hZF I hOrder).symm hZF I
    have hToRangeFun : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I f w range :=
      ⟨hFunction.1,hFunction.2.1,fun i hi => by
        obtain ⟨x,_,hix⟩ := hFunction.2.2 i hi
        exact ⟨x,(hRange x).mpr ⟨i,hix⟩,hix⟩⟩
    obtain ⟨idW,hIdW⟩ := ZF.exists_identityBijection hZF I w
    have hRangeSmall := ExistingOrdinalImage.ordinal_image_bound_l I hZF
      (ExistingCardinalBounds.omega_cardinal_l I hZF hw).1 ⟨idW,hIdW.1⟩ hToRangeFun
      (fun x hx => by
        obtain ⟨i,hix⟩ := (hRange x).mp hx
        exact ⟨i,hFunction.input_mem_of_pairMember hix,hix⟩)
    obtain ⟨rangeToW,hRangeToW⟩ := hRangeSmall
    obtain ⟨typeToW,hTypeToW⟩ := ZF.exists_compositionInjection hZF I hToRange.1 hRangeToW
    have hMuW : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual I mu w := by
      rcases hCofinal.cofinality_le_orderType hZF I hRelation hOrder hType hReg with he | hlt
      · subst orderType
        exact ⟨typeToW,hTypeToW⟩
      · obtain ⟨inclusion,hInclusion⟩ := ZF.exists_inclusionInjection hZF I (hOrdinal.transitive mu hlt)
        exact ZF.exists_compositionInjection hZF I hInclusion hTypeToW
    exact hReg.isCardinal.2 w hwMu (ZF.equinumerous_of_cardinalLessOrEqual hZF I
      (ZF.exists_inclusionInjection hZF I (hReg.isCardinal.1.transitive.memberSubset hwMu)) hMuW)

/-- Pinned CardinalParameters.succ_power_aleph0: partition all internal
omega-functions by an ordinal bound; existing small-family union supplies
the source sigma/fiber estimate. No countable choice is assumed separately. -/
theorem successor_countable_power (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w c mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hc : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w c)
    (hPow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) c c w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) mu c) :
    (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) mu ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hZFC := ConstructionDirectedCardinality.models_zfc hM hChoice
  let I := KuratowskiZF.interpretation hM
  have hReg := ExistingSuccessorRegularity.hartogs_regular_l I hZFC hw hc hMu
  have hMuCard := hReg.isCardinal
  have hwCard := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  have hwMu := (hMu.2 w hwCard.1).mpr hc.2
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_identityBijection hZF I mu
  obtain ⟨idW,hIdW⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨idC,hIdC⟩ := ZF.exists_identityBijection hZF I c
  have hcMu := (hMu.2 c hc.1.1).mpr ⟨idC,hIdC.1⟩
  obtain ⟨cToMu,hCToMu⟩ := ZF.exists_inclusionInjection hZF I (hMuCard.1.transitive.memberSubset hcMu)
  obtain ⟨wToMu,hWToMu⟩ := ZF.exists_inclusionInjection hZF I (hMuCard.1.transitive.memberSubset hwMu)
  have hMuInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal I w mu := ⟨hMuCard,wToMu,hWToMu⟩
  obtain ⟨F,hF⟩ := ZF.exists_functionSpace hZF I w mu
  obtain ⟨C,hC⟩ := ZF.exists_functionSpace hZF I w c
  have hCardC := normalize_power hM hPow hC
  obtain ⟨CtoC,hCtoC⟩ := hCardC.2.symm hZF I
  obtain ⟨P,hP⟩ := ZF.exists_powerSet hZF F
  have extend {a T} (ha : (Project.FirstOrderSemantics.reduct M).mem a mu)
      (hT : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace I T w a) :
      (Project.FirstOrderSemantics.reduct M).MemberSubset T F := by
    intro f hf
    have hfun := (hT f).mp hf
    refine (hF f).mpr ⟨hfun.1,hfun.2.1,?_⟩
    intro i hi
    obtain ⟨y,hy,hiy⟩ := hfun.2.2 i hi
    exact ⟨y,hMuCard.1.transitive a ha y hy,hiy⟩
  let schema : Project.BinarySchema 1 := {
    body := Project.Formula.isFunctionSpace PureKuratowskiProject.convention (.bound 0) (.bound 2) (.bound 1)
    freeClosed := by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isFunctionSpace]
      }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun _ => w, free := fun _ => w }
  have hSchema a T : schema.denote env a T ↔
      (Project.FirstOrderSemantics.reduct M).IsFunctionSpace I T w a := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_isFunctionSpace_iff I hZF.1,
      Project.Term.eval_bound]
    rfl
  obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I schema env (source := mu) (target := P)
    (fun a _ => by obtain ⟨T,hT⟩ := ZF.exists_functionSpace hZF I w a; exact ⟨T,(hSchema a T).mpr hT⟩)
    (fun a _ T V hT hV => hZF.1.eq_of_same_members T V (fun f =>
      ((hSchema a T).mp hT f).trans ((hSchema a V).mp hV f).symm))
    (fun a T ha hT => (hP T).mpr (extend ha ((hSchema a T).mp hT)))
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction hZF I hG.1 hG.2.1
  have hGA : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I G mu A :=
    ⟨hG.1,hG.2.1,fun a ha => by
      obtain ⟨T,_,haT⟩ := hG.2.2 a ha
      exact ⟨T,(hA T).mpr ⟨a,haT⟩,haT⟩⟩
  have hASmall := ExistingOrdinalImage.ordinal_image_bound_l I hZF hMuCard.1 ⟨idMu,hIdMu.1⟩ hGA
    (fun T hT => by
      obtain ⟨a,haT⟩ := (hA T).mp hT
      exact ⟨a,hG.input_mem_of_pairMember haT,haT⟩)
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP hZF) A
  obtain ⟨square,hSquare⟩ := ZF.exists_cartesianProduct hZF I mu mu
  have hUSmall := ExistingSmallUnion.union_bound_l I hZFC hASmall hU (by
    intro T hT
    obtain ⟨a,haT⟩ := (hA T).mp hT
    have ha := hG.input_mem_of_pairMember haT
    have hTspace := (hSchema a T).mp ((hGraph a T).mp haT).2
    obtain ⟨aToC,hAToC⟩ := (hMu.2 a (hMuCard.1.mem ha)).mp ha
    obtain ⟨toC,hToC⟩ := ZF.exists_functionSpaceTransportInjection hZF I hTspace hC hIdW hAToC
    obtain ⟨toCard,hToCard⟩ := ZF.exists_compositionInjection hZF I hToC hCtoC.1
    exact ZF.exists_compositionInjection hZF I hToCard hCToMu) hSquare
  have hFSub : (Project.FirstOrderSemantics.reduct M).MemberSubset F U := by
    intro f hf
    have hfun := (hF f).mp hf
    obtain ⟨range,hRange⟩ := ZF.exists_range_of_setFunction hZF I hfun.1 hfun.2.1
    have hBound := countable_bound hM hw hReg hwMu hfun hRange
    obtain ⟨a,ha,hBelow⟩ := hBound.exists_bound
    obtain ⟨b,hb,hab⟩ := hReg.isLimitOrdinal.2.2 a ha
    have hIntoB : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I f w b := by
      refine ⟨hfun.1,hfun.2.1,?_⟩
      intro i hi
      obtain ⟨y,_,hiy⟩ := hfun.2.2 i hi
      have hyb := (hBelow y ((hRange y).mpr ⟨i,hiy⟩)).elim
        (fun he => he.symm ▸ hab) (fun hya => (hMuCard.1.mem hb).transitive a hab y hya)
      exact ⟨y,hyb,hiy⟩
    obtain ⟨T,_,hbT⟩ := hG.2.2 b hb
    have hTspace := (hSchema b T).mp ((hGraph b T).mp hbT).2
    exact (hU f).mpr ⟨T,(hA T).mpr ⟨b,hbT⟩,(hTspace f).mpr hIntoB⟩
  obtain ⟨toU,hToU⟩ := ZF.exists_inclusionInjection hZF I hFSub
  obtain ⟨unionMap,hUnionMap⟩ := hUSmall
  obtain ⟨toSquare,hToSquare⟩ := ZF.exists_compositionInjection hZF I hToU hUnionMap
  have hSquareSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hMuInfinite
    ⟨idMu,hIdMu.1⟩ ⟨idMu,hIdMu.1⟩ hSquare
  obtain ⟨squareMap,hSquareMap⟩ := hSquareSmall
  have hUpper := ZF.exists_compositionInjection hZF I hToSquare hSquareMap
  obtain ⟨zero,_,hZeroW⟩ := hw.1.1
  have hLower := ZF.exists_constantFunctionInjection hZF I hF ⟨zero,hZeroW⟩
  have hEquiv := ZF.equinumerous_of_cardinalLessOrEqual hZF I hUpper hLower
  exact ⟨hReg,mu,w,F,⟨hMuCard,idMu,hIdMu⟩,⟨hwCard,idW,hIdW⟩,hF,
    hMuCard,(hEquiv.symm hZF I)⟩


/-- The source continuum itself is an actual cardinal representative of
the FULL internal power set of omega, and is fixed by omega-exponentiation. -/
theorem continuum_fixed_countable_power (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ P c, (Project.FirstOrderSemantics.reduct M).IsPowerSetOf P w ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) c P ∧
      (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w c ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) c c w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hwCard := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  obtain ⟨idW,hIdW⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨P,hP⟩ := ZF.exists_powerSet hZF w
  obtain ⟨c,hc⟩ := cardinal_of_set hM hChoice P
  obtain ⟨idC,hIdC⟩ := ZF.exists_identityBijection hZF I c
  obtain ⟨fromP,hFromP⟩ := hc.2.symm hZF I
  obtain ⟨wP,hwP⟩ := (ZF.cardinalLess_powerSet hZF I hP).1
  have hInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal I w c :=
    ⟨hc.1,ZF.exists_compositionInjection hZF I hwP hFromP.1⟩
  obtain ⟨one,hone,_⟩ := hw.exists_ordinalOne_mem
  obtain ⟨zero,hzero,hSucc⟩ := hone
  have hZeroOne := hSucc.predecessor_mem
  have hDistinct : zero ≠ one := by
    intro he
    subst one
    exact hzero zero hZeroOne
  obtain ⟨two,hTwo⟩ := KP.exists_pair (ZF.modelsKP hZF) zero one
  obtain ⟨twoCard,hTwoCard⟩ := cardinal_of_set hM hChoice two
  obtain ⟨F,hF⟩ := ZF.exists_functionSpace hZF I w two
  have hPF := ZF.equinumerous_powerSet_functionSpace hZF I hP hTwo hDistinct hF
  have hInner : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation I c twoCard w :=
    ⟨two,w,F,hTwoCard,⟨hwCard,idW,hIdW⟩,hF,hc.1,hc.2.trans hZF I hPF⟩
  obtain ⟨C,hC⟩ := ZF.exists_functionSpace hZF I w c
  obtain ⟨d,hd⟩ := cardinal_of_set hM hChoice C
  have hLeft : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation I d c w :=
    ⟨c,w,C,⟨hc.1,idC,hIdC⟩,⟨hwCard,idW,hIdW⟩,hC,hd⟩
  have hWW := ZF.infiniteCardinal_selfMultiplication hZF I hw hwCard
    (⟨hwCard,idW,hIdW.1⟩ : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal I w w)
  have he := Structure.IsCardinalExponentiation.iterated_exponent hZF I hInner hLeft hWW hInner
  subst d
  exact ⟨P,c,hP,hc,hInfinite,hLeft⟩

theorem omega_one_le_successor (hM : FirstOrder.Theory.Models M nativeZF)
    {w c mu : M.Carrier .set}
    (hc : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w c)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) mu c) :
    ConstructionSaturationIndex.OmegaOneLe hM w mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  let I := KuratowskiZF.interpretation hM
  obtain ⟨kappa,hKappa⟩ := ExistingOrdinalEnumeration.exists_hartogsNumber_kernel hZF I w
  have hMuCard := hMu.isCardinal hZF I
  refine ⟨kappa,hKappa,?_⟩
  apply (ForcingSupportSize.native_small hM kappa mu).mpr
  rcases Structure.IsOrdinal.trichotomy hZF.1 hKappa.1 hMuCard.1
      (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP kappa mu) with he | hkm | hmk
  · have heq := hZF.1.eq_of_same_members kappa mu he
    subst kappa
    obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I mu
    exact ⟨id,hId.1⟩
  · exact ZF.exists_inclusionInjection hZF I (hMuCard.1.transitive.memberSubset hkm)
  · have hMuW := (hKappa.2 mu hMuCard.1).mp hmk
    exact False.elim (hMu.not_cardinalLessOrEqual hKP
      (by obtain ⟨f,hf⟩ := hMuW; obtain ⟨g,hg⟩ := hc.2; exact ZF.exists_compositionInjection hZF I hf hg))

def Parameters (hM : FirstOrder.Theory.Models M nativeZF)
    (w P c mu : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsPowerSetOf P w ∧
  (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) c P ∧
  (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w c ∧
  (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) c c w ∧
  (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) mu c ∧
  (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) mu ∧
  (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu ∧
  (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w ∧
  ConstructionSaturationIndex.OmegaOneLe hM w mu

theorem parameters_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ P c mu, Parameters hM w P c mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨P,c,hP,hc,hInfinite,hPow⟩ := continuum_fixed_countable_power hM hChoice hw
  obtain ⟨mu,hMu⟩ := ExistingOrdinalEnumeration.exists_hartogsNumber_kernel hZF I c
  obtain ⟨hReg,hMuPow⟩ := successor_countable_power hM hChoice hw hInfinite hPow hMu
  have hWCard := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  have hwMu := (hMu.2 w hWCard.1).mpr hInfinite.2
  obtain ⟨j,hj⟩ := ZF.exists_inclusionInjection hZF I (hReg.isCardinal.1.transitive.memberSubset hwMu)
  exact ⟨P,c,mu,hP,hc,hInfinite,hPow,hMu,hReg,⟨hReg.isCardinal,j,hj⟩,hMuPow,
    omega_one_le_successor hM hInfinite hMu⟩


def parameters {m : Nat} (w P c mu : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isPowerSet (.bound P) (.bound w)) (.conj (Project.Formula.isCardinalOf
  PureKuratowskiProject.convention (.bound c) (.bound P)) (.conj (Project.Formula.isInfiniteCardinal
  PureKuratowskiProject.convention (.bound w) (.bound c)) (.conj (Project.Formula.isCardinalExponentiation
  PureKuratowskiProject.convention (.bound c) (.bound c) (.bound w)) (.conj
  (ConstructionSaturationIndex.hartogs c mu) (.conj (ConstructionSaturationIndex.regular mu) (.conj
  (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu)) (.conj
  (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound mu) (.bound mu) (.bound
  w)) (ConstructionSaturationIndex.omegaOneLe w mu)))))))))

theorem parameters_freeClosed {m : Nat} (w P c mu : Fin m) :
    (parameters w P c mu).FreeClosed := by
  simp -implicitDefEqProofs [parameters,Definitional.Formula.FreeClosed,Project.Formula.isPowerSet,Project.Formula.isCardinalOf_freeClosed,Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,Project.Formula.isFunctionFromTo_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationIndex.regular_freeClosed,ConstructionSaturationIndex.omegaOneLe_freeClosed]

theorem parameters_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w P c mu : Fin m) :
    Project.Formula.satisfies env (parameters w P c mu) ↔ Parameters hM (env.bound w) (env.bound P) (env.bound c) (env.bound mu) := by
  simp only [parameters,Parameters,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_isPowerSet_iff,Project.Formula.satisfies_isCardinalOf_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationIndex.regular_semantics hM,ConstructionSaturationIndex.omegaOneLe_semantics hM]


def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 1)))
      (.existsE (.existsE (.existsE (parameters (3 : Fin 4) (2 : Fin 4) (1 : Fin 4) (0 : Fin 4))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,parameters_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff,parameters_semantics hM,Project.Term.eval_bound]
  exact parameters_exists hM hChoice

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL hChoice)




end PPAC.Migration.ConstructionConcreteCardinals
