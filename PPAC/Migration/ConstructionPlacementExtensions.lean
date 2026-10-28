/- Pinned Placements and DiagramPlacements.extend_permutation_off.
Reuse cardinal_of_set, infinite_union_two_l, native function/range/composition
constructors and Cantor--Bernstein. The infinite budget and large-label
hypotheses are EXACTLY those of the actual finite-overlap placement consumer. -/
import PPAC.Migration.ConstructionPlacementFreshness

namespace PPAC.Migration.ConstructionPlacementExtensions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Difference (I A C : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x C ↔
    (Project.FirstOrderSemantics.reduct M).mem x I ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem x A

def Extends (f p : M.Carrier .set) : Prop :=
  ∀ x y, PureKuratowski.PairMember M x y f → PureKuratowski.PairMember M x y p

theorem complement_equinumerous (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I A C : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset A I)
    (hA : Small A mu) (hC : Difference I A C) :
    (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) I C := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hUnion : (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo I A C := by
    intro x
    constructor
    · intro hx
      by_cases ha : (Project.FirstOrderSemantics.reduct M).mem x A
      · exact Or.inl ha
      · exact Or.inr ((hC x).mpr ⟨hx,ha⟩)
    · intro hx
      exact hx.elim (hSub x) (fun hc => ((hC x).mp hc).1)
  have hCNot : ¬ Small C mu := by
    intro hc
    exact hLarge ((ForcingSupportSize.native_small hM I mu).mpr
      (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
        ((ForcingSupportSize.native_small hM A mu).mp hA)
        ((ForcingSupportSize.native_small hM C mu).mp hc) hUnion))
  obtain ⟨c,hc⟩ := ConstructionConcreteCardinals.cardinal_of_set hM hChoice C
  obtain ⟨cToC,hCToC⟩ := hc.2
  obtain ⟨CtoC,hCtoC⟩ := ZF.exists_inverseBijection hZF pair hCToC
  have hMuToC : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual pair mu c := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 hMu.1.1 hc.1.1
      (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) mu c) with hEq | hLess | hGreater
    · have he := hZF.1.eq_of_same_members mu c hEq
      subst c
      exact ZF.exists_inclusionInjection hZF pair (fun _ hx => hx)
    · exact ZF.exists_inclusionInjection hZF pair (hc.1.1.transitive.memberSubset hLess)
    · apply False.elim
      obtain ⟨incl,hIncl⟩ := ZF.exists_inclusionInjection hZF pair (hMu.1.1.transitive.memberSubset hGreater)
      exact hCNot ((ForcingSupportSize.native_small hM C mu).mpr
        (ZF.exists_compositionInjection hZF pair hCtoC.1 hIncl))
  obtain ⟨muToC,hMuToC⟩ := hMuToC
  obtain ⟨wToMu,hWToMu⟩ := hMu.2
  have hInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal pair w c :=
    ⟨hc.1,ZF.exists_compositionInjection hZF pair hWToMu hMuToC⟩
  obtain ⟨aToMu,hAToMu⟩ := (ForcingSupportSize.native_small hM A mu).mp hA
  have hABound := ZF.exists_compositionInjection hZF pair hAToMu hMuToC
  obtain ⟨iToC,hIToC⟩ := ExistingCardinalBounds.infinite_union_two_l pair hZF hw hInfinite
    hABound ⟨CtoC,hCtoC.1⟩ hUnion
  obtain ⟨forward,hForward⟩ := ZF.exists_compositionInjection hZF pair hIToC hCToC.1
  obtain ⟨reverse,hReverse⟩ := ZF.exists_inclusionInjection hZF pair
    (fun x hx => ((hC x).mp hx).1)
  exact ZF.equinumerous_of_injections hZF pair hForward hReverse

/-- Exact original piecewise union: no prescribed edge is changed. -/
theorem join_injections (hM : FirstOrder.Theory.Models M nativeZF)
    {I S C U f g : M.Carrier .set}
    (hUnion : (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo U S C)
    (hDisjoint : (Project.FirstOrderSemantics.reduct M).IsDisjoint S C)
    (hf : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) f S I)
    (hg : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) g C I)
    (hCross : ∀ x y z, PureKuratowski.PairMember M x z f → PureKuratowski.PairMember M y z g → False) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) p U I ∧
      ∀ x y, PureKuratowski.PairMember M x y p ↔
        PureKuratowski.PairMember M x y f ∨ PureKuratowski.PairMember M x y g := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let schema : Project.BinarySchema 2 := {
    body := .disj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 2))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 3)) }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => I }
  have hSchema x y : schema.denote env x y ↔
      PureKuratowski.PairMember M x y f ∨ PureKuratowski.PairMember M x y g := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_disj_iff,
      Project.Formula.satisfies_orderedPairMem_iff pair]
    rfl
  obtain ⟨p,hp,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF pair schema env
    (source := U) (target := I) (by
      intro x hx
      rcases (hUnion x).mp hx with hx | hx
      · obtain ⟨y,_,hxy⟩ := hf.1.2.2 x hx
        exact ⟨y,(hSchema x y).mpr (Or.inl hxy)⟩
      · obtain ⟨y,_,hxy⟩ := hg.1.2.2 x hx
        exact ⟨y,(hSchema x y).mpr (Or.inr hxy)⟩) (by
      intro x _ y z hy hz
      rcases (hSchema x y).mp hy with hy | hy <;> rcases (hSchema x z).mp hz with hz | hz
      · exact hf.1.1.2 x y z hy hz
      · exact False.elim (hDisjoint x ⟨hf.1.input_mem_of_pairMember hy,hg.1.input_mem_of_pairMember hz⟩)
      · exact False.elim (hDisjoint x ⟨hf.1.input_mem_of_pairMember hz,hg.1.input_mem_of_pairMember hy⟩)
      · exact hg.1.1.2 x y z hy hz) (by
      intro x y _ hy
      exact ((hSchema x y).mp hy).elim hf.1.output_mem_of_pairMember hg.1.output_mem_of_pairMember)
  have hEdges x y : PureKuratowski.PairMember M x y p ↔
      PureKuratowski.PairMember M x y f ∨ PureKuratowski.PairMember M x y g := by
    constructor
    · intro hxy
      exact (hSchema x y).mp ((he x y).mp hxy).2
    · intro hxy
      have hx := hxy.elim (fun hfxy => (hUnion x).mpr (Or.inl (hf.1.input_mem_of_pairMember hfxy)))
        (fun hgxy => (hUnion x).mpr (Or.inr (hg.1.input_mem_of_pairMember hgxy)))
      exact (he x y).mpr ⟨hx,(hSchema x y).mpr hxy⟩
  refine ⟨p,⟨hp,?_⟩,hEdges⟩
  intro x y z hx hy
  rcases (hEdges x z).mp hx with hx | hx <;> rcases (hEdges y z).mp hy with hy | hy
  · exact hf.2 x y z hx hy
  · exact False.elim (hCross x y z hx hy)
  · exact False.elim (hCross y x z hy hx)
  · exact hg.2 x y z hx hy

/-- The full small partial injection extends to an INTERNAL permutation.
The budget hypotheses match DiagramPlacements.extend_permutation_off. -/
theorem extend_permutation (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I S f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset S I)
    (hS : Small S mu)
    (hf : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) f S I) :
    ∃ p, ForcingConditionGraphs.Permutation I p ∧ Extends f p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨T,hT⟩ := ZF.exists_range_of_setFunction hZF pair hf.1.1 hf.1.2.1
  have hBij : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair f S T := by
    refine ⟨⟨⟨hf.1.1,hf.1.2.1,fun x hx => ?_⟩,hf.2⟩,fun y hy => ?_⟩
    · obtain ⟨y,_,hxy⟩ := hf.1.2.2 x hx
      exact ⟨y,(hT y).mpr ⟨x,hxy⟩,hxy⟩
    · obtain ⟨x,hxy⟩ := (hT y).mp hy
      exact ⟨x,hf.1.input_mem_of_pairMember hxy,hxy⟩
  have hTSub : (Project.FirstOrderSemantics.reduct M).MemberSubset T I := by
    intro y hy
    obtain ⟨x,hxy⟩ := (hT y).mp hy
    exact hf.1.output_mem_of_pairMember hxy
  obtain ⟨inverse,hInverse⟩ := ZF.exists_inverseBijection hZF pair hBij
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM S mu).mp hS
  have hTSmall : Small T mu := (ForcingSupportSize.native_small hM T mu).mpr
    (ZF.exists_compositionInjection hZF pair hInverse.1 hToMu)
  obtain ⟨C,hC⟩ := KP.difference_exists_d (ZF.modelsKP hZF) S I
  obtain ⟨D,hD⟩ := KP.difference_exists_d (ZF.modelsKP hZF) T I
  have hIC := complement_equinumerous hM hChoice hw hMu hLarge hSub hS hC
  have hID := complement_equinumerous hM hChoice hw hMu hLarge hTSub hTSmall hD
  obtain ⟨g,hg⟩ := (hIC.symm hZF pair).trans hZF pair hID
  have hUnion : (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo I S C := by
    intro x
    constructor
    · intro hx
      by_cases hs : (Project.FirstOrderSemantics.reduct M).mem x S
      · exact Or.inl hs
      · exact Or.inr ((hC x).mpr ⟨hx,hs⟩)
    · exact fun hx => hx.elim (hSub x) (fun hc => ((hC x).mp hc).1)
  have hDisj : (Project.FirstOrderSemantics.reduct M).IsDisjoint S C :=
    fun x h => ((hC x).mp h.2).2 h.1
  have hgI : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo pair g C I :=
    ⟨⟨hg.1.1.1,hg.1.1.2.1,fun x hx => by
      obtain ⟨y,hy,hxy⟩ := hg.1.1.2.2 x hx
      exact ⟨y,((hD y).mp hy).1,hxy⟩⟩,hg.1.2⟩
  obtain ⟨p,hp,hEdges⟩ := join_injections hM hUnion hDisj hf hgI (fun x y z hx hy =>
    ((hD z).mp (hg.1.1.output_mem_of_pairMember hy)).2 ((hT z).mpr ⟨x,hx⟩))
  have hSurj : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y I →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x I ∧ PureKuratowski.PairMember M x y p := by
    intro y hy
    by_cases ht : (Project.FirstOrderSemantics.reduct M).mem y T
    · obtain ⟨x,hx,hxy⟩ := hBij.2 y ht
      exact ⟨x,hSub x hx,(hEdges x y).mpr (Or.inl hxy)⟩
    · obtain ⟨x,hx,hxy⟩ := hg.2 y ((hD y).mpr ⟨hy,ht⟩)
      exact ⟨x,((hC x).mp hx).1,(hEdges x y).mpr (Or.inr hxy)⟩
  exact ⟨p,(ForcingConditionGraphs.native_permutation hM I p).mpr ⟨hp,hSurj⟩,
    fun x y hxy => (hEdges x y).mpr (Or.inl hxy)⟩

def Avoids (K p v S : M.Carrier .set) : Prop :=
  ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x v →
    ¬ (Project.FirstOrderSemantics.reduct M).mem x S →
    PureKuratowski.PairMember M x y p → ¬ (Project.FirstOrderSemantics.reduct M).mem y K

/-- The exact original extend_permutation_off conclusion, implemented with
the source piecewise partial-injection construction and existing complements. -/
theorem extend_permutation_off (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I S v K f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu)
    (hSSub : (Project.FirstOrderSemantics.reduct M).MemberSubset S I)
    (hVSub : (Project.FirstOrderSemantics.reduct M).MemberSubset v I)
    (hKSub : (Project.FirstOrderSemantics.reduct M).MemberSubset K I)
    (hS : Small S mu) (hv : Small v mu) (hK : Small K mu)
    (hf : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) f S I) :
    ∃ p, ForcingConditionGraphs.Permutation I p ∧ Extends f p ∧ Avoids K p v S := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨T,hT⟩ := ZF.exists_range_of_setFunction hZF pair hf.1.1 hf.1.2.1
  have hBij : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair f S T := by
    refine ⟨⟨⟨hf.1.1,hf.1.2.1,fun x hx => ?_⟩,hf.2⟩,fun y hy => ?_⟩
    · obtain ⟨y,_,hxy⟩ := hf.1.2.2 x hx
      exact ⟨y,(hT y).mpr ⟨x,hxy⟩,hxy⟩
    · obtain ⟨x,hxy⟩ := (hT y).mp hy
      exact ⟨x,hf.1.input_mem_of_pairMember hxy,hxy⟩
  have hTSub : (Project.FirstOrderSemantics.reduct M).MemberSubset T I := by
    intro y hy
    obtain ⟨x,hxy⟩ := (hT y).mp hy
    exact hf.1.output_mem_of_pairMember hxy
  obtain ⟨inverse,hInverse⟩ := ZF.exists_inverseBijection hZF pair hBij
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM S mu).mp hS
  have hTSmall := ZF.exists_compositionInjection hZF pair hInverse.1 hToMu
  obtain ⟨B,hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) K T
  have hBSub : (Project.FirstOrderSemantics.reduct M).MemberSubset B I :=
    fun x hx => ((hB x).mp hx).elim (hKSub x) (hTSub x)
  have hBSmall : Small B mu := (ForcingSupportSize.native_small hM B mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM K mu).mp hK) hTSmall hB)
  obtain ⟨D,hD⟩ := KP.difference_exists_d (ZF.modelsKP hZF) B I
  obtain ⟨iToD,hIToD⟩ := complement_equinumerous hM hChoice hw hMu hLarge hBSub hBSmall hD
  obtain ⟨V,hV⟩ := KP.difference_exists_d (ZF.modelsKP hZF) S v
  obtain ⟨vToI,hVToI⟩ := ZF.exists_inclusionInjection hZF pair
    (fun x hx => hVSub x ((hV x).mp hx).1)
  obtain ⟨g,hg⟩ := ZF.exists_compositionInjection hZF pair hVToI hIToD.1
  have hgI : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo pair g V I :=
    ⟨⟨hg.1.1,hg.1.2.1,fun x hx => by
      obtain ⟨y,hy,hxy⟩ := hg.1.2.2 x hx
      exact ⟨y,((hD y).mp hy).1,hxy⟩⟩,hg.2⟩
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) S v
  have hUUnion : (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo U S V := by
    intro x
    constructor
    · intro hx
      rcases (hU x).mp hx with hs | hvx
      · exact Or.inl hs
      · by_cases hs : (Project.FirstOrderSemantics.reduct M).mem x S
        · exact Or.inl hs
        · exact Or.inr ((hV x).mpr ⟨hvx,hs⟩)
    · intro hx
      exact (hU x).mpr (hx.elim Or.inl (fun h => Or.inr ((hV x).mp h).1))
  have hDisj : (Project.FirstOrderSemantics.reduct M).IsDisjoint S V :=
    fun x h => ((hV x).mp h.2).2 h.1
  obtain ⟨q,hq,hEdges⟩ := join_injections hM hUUnion hDisj hf hgI (fun x y z hx hy =>
    ((hD z).mp (hg.1.output_mem_of_pairMember hy)).2
      ((hB z).mpr (Or.inr ((hT z).mpr ⟨x,hx⟩))))
  have hUSub : (Project.FirstOrderSemantics.reduct M).MemberSubset U I :=
    fun x hx => ((hU x).mp hx).elim (hSSub x) (hVSub x)
  have hUSmall : Small U mu := (ForcingSupportSize.native_small hM U mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM S mu).mp hS)
      ((ForcingSupportSize.native_small hM v mu).mp hv) hU)
  obtain ⟨p,hp,hExt⟩ := extend_permutation hM hChoice hw hMu hLarge hUSub hUSmall hq
  refine ⟨p,hp,fun x y hxy => hExt x y ((hEdges x y).mpr (Or.inl hxy)),?_⟩
  intro x y hx hn hxy hyK
  obtain ⟨z,hz,hxz⟩ := hg.1.2.2 x ((hV x).mpr ⟨hx,hn⟩)
  have hpz := hExt x z ((hEdges x z).mpr (Or.inr hxz))
  have hyz := ForcingConditionGraphs.function_unique hp.1.1 hxy hpz
  exact ((hD z).mp hz).2 ((hB z).mpr (Or.inl (hyz ▸ hyK)))

/-- Pinned ConcreteSystem.I: the actual label set is Hartogs(mu).
Its non-smallness is proved, rather than assumed as another parent input. -/
theorem exists_labels (hM : FirstOrder.Theory.Models M nativeZF) (mu : M.Carrier .set) :
    ∃ I, (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu ∧
      ¬ Small I mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨I,hI⟩ := ExistingOrdinalEnumeration.exists_hartogsNumber_kernel hZF
    (KuratowskiZF.interpretation hM) mu
  exact ⟨I,hI,fun h => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM I mu).mp h)⟩

def extendsF {m : Nat} (f p : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound f.succ.succ))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound p.succ.succ))))

theorem extendsF_freeClosed {m : Nat} (f p : Fin m) : (extendsF f p).FreeClosed := by
  simp -implicitDefEqProofs [extendsF,Definitional.Formula.FreeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem extendsF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f p : Fin m) :
    Project.Formula.satisfies env (extendsF f p) ↔ Extends (env.bound f) (env.bound p) := by
  simp only [extendsF,Extends,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def avoids {m : Nat} (K p v S : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound v.succ.succ))
    (.imp (.neg (.mem (.bound 1) (.bound S.succ.succ)))
      (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
        (.bound 1) (.bound 0) (.bound p.succ.succ))
        (.neg (.mem (.bound 0) (.bound K.succ.succ)))))))

theorem avoids_freeClosed {m : Nat} (K p v S : Fin m) : (avoids K p v S).FreeClosed := by
  simp -implicitDefEqProofs [avoids,Definitional.Formula.FreeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem avoids_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K p v S : Fin m) :
    Project.Formula.satisfies env (avoids K p v S) ↔
      Avoids (env.bound K) (env.bound p) (env.bound v) (env.bound S) := by
  simp only [avoids,Avoids,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def placement {m : Nat} (I S v K f mu : Fin m) : Project.Formula 1 m :=
  .imp (Project.Formula.subset (.bound S) (.bound I))
    (.imp (Project.Formula.subset (.bound v) (.bound I))
      (.imp (Project.Formula.subset (.bound K) (.bound I))
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small S mu))
          (.imp (ProjectSyntax.encode id (ForcingSupportSize.small v mu))
            (.imp (ProjectSyntax.encode id (ForcingSupportSize.small K mu))
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection f S I))
                (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I.succ 0))
                  (.conj (extendsF f.succ 0) (avoids K.succ 0 v.succ S.succ))))))))))

theorem placement_freeClosed {m : Nat} (I S v K f mu : Fin m) : (placement I S v K f mu).FreeClosed := by
  simp -implicitDefEqProofs [placement,Definitional.Formula.FreeClosed,Project.Formula.subset,
    ProjectSyntax.freeClosed,extendsF_freeClosed,avoids_freeClosed]

theorem placement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I S v K f mu : Fin m) :
    Project.Formula.satisfies env (placement I S v K f mu) ↔
      ((Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound S) (env.bound I) →
        (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound v) (env.bound I) →
        (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound K) (env.bound I) →
        Small (env.bound S) (env.bound mu) → Small (env.bound v) (env.bound mu) →
        Small (env.bound K) (env.bound mu) →
        ForcingSupportSize.Injection (env.bound S) (env.bound I) (env.bound f) →
        ∃ p, ForcingConditionGraphs.Permutation (env.bound I) p ∧ Extends (env.bound f) p ∧
          Avoids (env.bound K) p (env.bound v) (env.bound S)) := by
  simp only [placement,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),extendsF_semantics hM,avoids_semantics hM,
    Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
        (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small 2 1)))
          (placement 2 3 4 5 6 1))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed,placement_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),placement_semantics hM,Project.Term.eval_bound]
  intro hw hMu hLarge hSSub hVSub hKSub hS hv hK hf
  exact extend_permutation_off hM hChoice hw hMu hLarge hSSub hVSub hKSub hS hv hK
    ((ForcingSupportSize.native_injection hM (bound 3) (bound 2) (bound 6)).mp hf)

def labelsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.existsE
    (.conj (ConstructionSaturationIndex.hartogs (0 : Fin 1).succ 0)
      (.neg (ProjectSyntax.encode id (ForcingSupportSize.small (0 : Fin 2) (0 : Fin 1).succ)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed]

theorem labels_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence labelsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) labelsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionSaturationIndex.hartogs_semantics hM,Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M)]
  exact exists_labels hM (bound 0)

theorem labels_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence labelsSentence) :=
  ModelTransfer.derives (fun _ hM => labels_models hM)

/-- ONE actually constructed label set works for ALL internal placement
inputs, not a separately supplied label set or one permutation chosen in Lean. -/
def actualLabelsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 2
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
        (.existsE (.conj (ConstructionSaturationIndex.hartogs (1 : Fin 2).succ 0)
          (.conj (.neg (ProjectSyntax.encode id (ForcingSupportSize.small (0 : Fin 3) (1 : Fin 2).succ)))
            (.forallE (.forallE (.forallE (.forallE (placement 4 3 2 1 0 6))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,placement_freeClosed]

theorem actualLabels_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence actualLabelsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) actualLabelsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionSaturationIndex.hartogs_semantics hM,Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),Project.Formula.satisfies_forall_iff,
    placement_semantics hM,Project.Term.eval_bound]
  intro hw hMu
  obtain ⟨I,hHartogs,hLarge⟩ := exists_labels hM (bound 1)
  refine ⟨I,hHartogs,hLarge,?_⟩
  intro S v K f hSSub hVSub hKSub hS hv hK hf
  exact extend_permutation_off hM hChoice hw hMu hLarge hSSub hVSub hKSub hS hv hK
    ((ForcingSupportSize.native_injection hM S I f).mp hf)

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
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

theorem actualLabels_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative actualLabelsSentence)) := by
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
  apply ConstructibleGround.relative_models hM actualLabelsSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) actualLabelsSentence).mp (actualLabels_models hL hChoice)

end PPAC.Migration.ConstructionPlacementExtensions

