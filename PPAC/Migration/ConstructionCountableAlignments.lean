/- Pinned ConcreteQuotients.countable_quotient_of_cells:177-186 (halign).
The SAME countable reordered base works for EVERY component stabilizer element.
Consume existing actual chain indices, alignment laws, hull and finite descent. -/
import PPAC.Migration.ConstructionCountableReordering
import PPAC.Migration.ConstructionReorderedDescent
import PPAC.Migration.ForcingGermAlignments

namespace PPAC.Migration.ConstructionCountableAlignments
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionComponentCofinal (Chain EncodedCommon)
open ForcingGermAlignments (Alignment Indices Index)
open ForcingComponentMove (Move)
open ForcingConditionGraphs (Permutation CompositionGraph function_input function_unique)
open ForcingSupportSize (Small MapsTo Injection)
open ForcingSupportedNames (Range)
open ConstructionRealCuts (Subset)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exactly a source component stabilizer element, not an arbitrary action. -/
def Stabilizes (D I mul q root pi : M.Carrier .set) : Prop :=
  Permutation I pi ∧ CompositionGraph D pi q q ∧
    ∃ rootT, Move D I mul q pi root rootT ∧ EncodedCommon D I mul q root rootT

def Point (D I mul q root chain pi p : M.Carrier .set) : Prop :=
  ∃ i x, PureKuratowski.Code M p i x ∧ Alignment D I mul q root chain pi i x

def point {m : Nat} (D I mul q root chain pi p : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (ForcingGermAlignments.alignment D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ chain.succ.succ pi.succ.succ 1 0)))

theorem point_freeClosed {m : Nat} (D I mul q root chain pi p : Fin m) :
    (point D I mul q root chain pi p).FreeClosed := by
  simp -implicitDefEqProofs [point,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,
    ForcingGermAlignments.alignment_freeClosed]

theorem point_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root chain pi p : Fin m) :
    Project.Formula.satisfies env (point D I mul q root chain pi p) ↔
      Point (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound pi) (env.bound p) := by
  simp only [point,Point,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,ForcingGermAlignments.alignment_semantics hM]
  rfl

theorem alignment_typed {w D I mul q zero root vertices chain pi i x : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    (h : Alignment D I mul q root chain pi i x) :
    (Project.FirstOrderSemantics.reduct M).mem i w ∧ (Project.FirstOrderSemantics.reduct M).mem x D := by
  obtain ⟨v,V,hiv,_,ha⟩ := h
  exact ⟨function_input hC.1.1 hiv,ForcingGermAlignments.arrow_index_mem ha⟩

theorem exists_points (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) :
    ∃ A, ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A ↔ Point D I mul q root chain pi p := by
  let schema : Project.UnarySchema 7 := { body := point 1 2 3 4 5 6 7 0, freeClosed := point_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases root (Fin.cases chain (fun _ => pi)))))),
    free := fun _ => D }
  have he p : schema.denote env p ↔ Point D I mul q root chain pi p :=
    point_semantics hM (env.push p) 1 2 3 4 5 6 7 0
  obtain ⟨P,hP⟩ := ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) w D
  obtain ⟨A,hA⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env P
  refine ⟨A,fun p => ⟨fun hp => (he p).mp ((hA p).mp hp).2,?_⟩⟩
  intro hp
  obtain ⟨i,x,hpx,hAlign⟩ := hp
  have ht := alignment_typed hC hAlign
  exact (hA p).mpr ⟨(hP p).mpr ⟨i,ht.1,x,ht.2,hpx⟩,(he p).mpr ⟨i,x,hpx,hAlign⟩⟩

/-- Discharge every original finite-descent Input from the existing
alignment laws on the actual set of pairs; no replacement oracle remains. -/
theorem inputs (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul e q zero root vertices chain pi rootT graph A base : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hX : ConstructionComponentCarrier.Carrier D I mul q vertices)
    (hC : Chain w D I mul q zero root vertices chain) (hq : Injection D I q)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hMove : Move D I mul q pi root rootT) (hCommon : EncodedCommon D I mul q root rootT)
    (hGraph : Indices w D I mul q root chain graph)
    (hA : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A ↔ Point D I mul q root chain pi p)
    (hBase : ∀ i x, PureKuratowski.PairMember M i x graph → (Project.FirstOrderSemantics.reduct M).mem x base)
    (hFactors : ConstructionConservativeHull.FactorClosed base D mul) :
    ConstructionFiniteDescent.Inputs w D mul graph A base := by
  have read_point p i x (hp : (Project.FirstOrderSemantics.reduct M).mem p A) (hpx : PureKuratowski.Code M p i x) :
      Alignment D I mul q root chain pi i x := by
    obtain ⟨j,y,hpy,ha⟩ := (hA p).mp hp
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hpx hpy
    exact ha
  refine ⟨⟨hGraph.1.1,hBase⟩,hFactors,?_,?_⟩
  · intro p i x hpA hpx
    obtain ⟨N,n,hN,hdiv⟩ := ForcingGermAlignments.alignment_bounded hm hX hC (read_point p i x hpA hpx)
    have hNg := (hGraph.2 N n).mpr hN
    exact ⟨N,n,function_input hGraph.1.1 hNg,hNg,hdiv⟩
  · intro p i x N nN hpA hpx hNw hNg
    have ha := read_point p i x hpA hpx
    obtain ⟨ni,hni,_⟩ := hGraph.1.1.2 i (alignment_typed hC ha).1
    obtain ⟨j,d,y,nj,hd,hay,hij,hxy,hnij,hj,hNy⟩ := ForcingGermAlignments.alignment_replacement_typed hM hm hJ hw hz
      hX hC hq hp hFix hMove hCommon ha ((hGraph.2 i ni).mp hni) ((hGraph.2 N nN).mp hNg)
    obtain ⟨r,hry⟩ := KuratowskiZF.exists_code hM j y
    have hrd := (hA r).mpr ⟨j,y,hry,hay⟩
    exact ⟨r,j,y,hry,⟨hpA,hrd,i,j,x,y,ni,nj,d,hpx,hry,(alignment_typed hC ha).1,
      (alignment_typed hC hay).1,hij,hd,hni,(hGraph.2 j nj).mpr hj,hnij,hxy⟩,hNy⟩

/-- The original halign conclusion on a supplied actual reordered tower. -/
theorem alignment_in_base (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e I R bottom stages base graph labels q root vertices chain pi : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : ConstructionCellRestriction.Stages V GV e stages)
    (hT : ConstructionFirstAppearance.Timeline hM V I R bottom stages)
    (hSteps : ConstructionReordered.Steps hM w zero V GV e I R stages)
    (hBottom : PureKuratowski.PairMember M bottom base stages)
    (hTop : PureKuratowski.PairMember M zero V stages)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : Chain w V labels GV q zero root vertices chain) (hq : Injection V labels q)
    (hGraph : Indices w V labels GV q root chain graph)
    (hBase : ∀ i x, PureKuratowski.PairMember M i x graph → (Project.FirstOrderSemantics.reduct M).mem x base)
    (hpi : Stabilizes V labels GV q root pi) :
    ∃ i x, (Project.FirstOrderSemantics.reduct M).mem i w ∧
      (Project.FirstOrderSemantics.reduct M).mem x base ∧ Alignment V labels GV q root chain pi i x := by
  obtain ⟨hp,hFix,rootT,hMove,hCommon⟩ := hpi
  obtain ⟨A,hA⟩ := exists_points hM hC (pi := pi)
  have hInputs := inputs hM hv hJ hw hz hX hC hq hp hFix hMove hCommon hGraph hA hBase
    (hStages bottom base hBottom).2.2.2.1
  obtain ⟨i,x,ha⟩ := ForcingGermAlignments.alignment_nonempty hM hX hC hq hp hFix hMove hCommon
  obtain ⟨p,hpx⟩ := KuratowskiZF.exists_code hM i x
  have hpA := (hA p).mpr ⟨i,x,hpx,ha⟩
  obtain ⟨r,j,y,hrA,hry,hy,_⟩ := ConstructionReorderedDescent.finite_descent hM hw hz hzw hv hc hJ hStages
    hT hSteps hBottom hInputs (function_input hT.2.1 hTop) V p i x hTop hpA hpx (alignment_typed hC ha).2
  obtain ⟨j',y',hry',ha'⟩ := (hA r).mp hrA
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hry hry'
  exact ⟨j,y,(alignment_typed hC ha').1,hy,ha'⟩

/-- Same actual countable base for all stabilizer elements, not a separate
chosen reordering for each permutation. -/
def Aligned (w V labels GV q root chain base : M.Carrier .set) : Prop :=
  ∀ pi, Stabilizes V labels GV q root pi → ∃ i x,
    (Project.FirstOrderSemantics.reduct M).mem i w ∧ (Project.FirstOrderSemantics.reduct M).mem x base ∧
      Alignment V labels GV q root chain pi i x

/-- Exact source halign with all reordering and countability premises
produced from the original cell tower. The base is chosen before pi. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF
      labels q root vertices chain : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : ConstructionCellRestriction.Stages V GV e S)
    (hT : ConstructionFirstAppearance.Timeline hM V I R bottom S)
    (hIndex : ConstructionFirstAppearance.Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hData : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S)
    (hD : PureKuratowski.PairMember M bottom D S) (hDc : Small D w)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : Chain w V labels GV q zero root vertices chain) (hq : Injection V labels q) :
    ∃ base, ConstructionConservativeHull.Closure V GV e base ∧ Small base w ∧
      Aligned w V labels GV q root chain base := by
  obtain ⟨graph,hIndices⟩ := ForcingGermAlignments.exists_indices hM hv hw hz hC
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  have hNative := (ForcingSupportSize.native_mapsTo hM w V graph).mp hIndices.1
  obtain ⟨s,hs⟩ := ZF.exists_range_of_setFunction hZF P hNative.1 hNative.2.1
  have hMap : MapsTo w s graph := ⟨hIndices.1.1,fun i x hx => (hs x).mpr ⟨i,hx⟩⟩
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hsSmall := ExistingOrdinalImage.ordinal_image_bound_l P hZF
    (ExistingCardinalBounds.omega_cardinal_l P hZF hw).1 ⟨id,hId.1⟩
    ((ForcingSupportSize.native_mapsTo hM w s graph).mp hMap)
    (fun x hx => by obtain ⟨i,hix⟩ := (hs x).mp hx; exact ⟨i,function_input hIndices.1.1 hix,hix⟩)
  have hsV : Subset s V := by
    intro x hx
    obtain ⟨i,hix⟩ := (hs x).mp hx
    exact hIndices.1.2 i x hix
  obtain ⟨base,futures,muls,hReordered,hCount,hSub,hBottom⟩ := ConstructionCountableReordering.construction hM
    hChoice hw hz hzw hv hc hJ hStages hT hIndex hCells hNew hData hGraph hD hDc hsV
    ((ForcingSupportSize.native_small hM s w).mpr hsSmall)
  refine ⟨base,hReordered.2.2.1 bottom base hBottom,hCount,?_⟩
  intro pi hpi
  exact alignment_in_base hM hw hz hzw hv hc hJ hReordered.2.2.1 hReordered.2.2.2.1
    hReordered.2.2.2.2.2.1 hBottom hReordered.2.2.2.2.1 hX hC hq hIndices
    (fun i x hx => hSub x ((hs x).mpr ⟨i,hx⟩)) hpi

def stabilizes {m : Nat} (D I mul q root pi : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D pi q q))
      (.existsE (.conj (ForcingComponentMove.move D.succ I.succ mul.succ q.succ pi.succ root.succ 0)
        (ConstructionComponentCofinal.encodedCommon D.succ I.succ mul.succ q.succ root.succ 0))))

theorem stabilizes_freeClosed {m : Nat} (D I mul q root pi : Fin m) :
    (stabilizes D I mul q root pi).FreeClosed := by
  simp -implicitDefEqProofs [stabilizes,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem stabilizes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root pi : Fin m) :
    Project.Formula.satisfies env (stabilizes D I mul q root pi) ↔ Stabilizes (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound pi) := by
  simp only [stabilizes,Stabilizes,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingComponentMove.move_semantics hM,
    ConstructionComponentCofinal.encodedCommon_semantics hM]
  rfl

def aligned {m : Nat} (w V labels GV q root chain base : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (stabilizes V.succ labels.succ GV.succ q.succ root.succ 0)
    (.existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ.succ))
      (.conj (.mem (.bound 0) (.bound base.succ.succ.succ))
        (ForcingGermAlignments.alignment V.succ.succ.succ labels.succ.succ.succ GV.succ.succ.succ q.succ.succ.succ root.succ.succ.succ chain.succ.succ.succ 2 1 0))))))

theorem aligned_freeClosed {m : Nat} (w V labels GV q root chain base : Fin m) : (aligned w V labels GV q root chain base).FreeClosed := by
  simp -implicitDefEqProofs [aligned,Definitional.Formula.FreeClosed,stabilizes_freeClosed,
    ForcingGermAlignments.alignment_freeClosed]

theorem aligned_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w V labels GV q root chain base : Fin m) :
    Project.Formula.satisfies env (aligned w V labels GV q root chain base) ↔ Aligned (env.bound w) (env.bound V) (env.bound labels) (env.bound GV) (env.bound q) (env.bound root) (env.bound chain) (env.bound base) := by
  simp only [aligned,Aligned,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,stabilizes_semantics hM,ForcingGermAlignments.alignment_semantics hM]
  rfl

def constructionSentence {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S bottom D)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D w)) (.imp (ConstructionComponentCarrier.carrier V labels GV q vertices) (.imp (ConstructionComponentCofinal.chain w V labels GV q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q V labels)) (.existsE (.conj (ConstructionConservativeHull.closure V.succ GV.succ e.succ 0) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 0 w.succ)) (aligned w.succ V.succ labels.succ GV.succ q.succ root.succ chain.succ 0))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionConservativeHull.closure_freeClosed,aligned_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,
      ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,
      ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed]

theorem construction_models {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),aligned_semantics hM,
    ConstructionConservativeHull.closure_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionCellRestriction.stages_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,
    ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,
    ConstructionStepCellSelection.atNew_semantics hM,ConstructionBlockIndex.data_semantics hM,
    ConstructionFlatStages.graph_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ConstructionComponentCofinal.chain_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain)).mp (construction_models w zero one V GV e I R bottom S index cells D kappa traces Indices A r history outerF labels q root vertices chain hL hChoice)


end PPAC.Migration.ConstructionCountableAlignments
