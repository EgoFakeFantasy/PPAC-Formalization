/- Pinned ClassFibers.localListOrdinal/localListEquiv/localList/mem_localList.
Enumerate the entire existing internal LocalName carrier by an internal ordinal;
collect every entry with the actual condition set. No replacement name universe. -/
import PPAC.Migration.ForcingLocalNames
import PPAC.Migration.ForcingOrdinalFixed
import PPAC.Migration.ConstructionConcreteCardinals
import PPAC.Migration.ConstructionDescentPlacement
import PPAC.Migration.ConstructibleSource

namespace PPAC.Migration.ForcingLocalList
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingPowerName (trueTest)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (v : Fin 7 → M.Carrier .set) {I K B w mu G F bound r A H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hp : ForcingProductFamily.Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingSupportFilter.Filter I G mu F)
    (hr : ForcingSupportSize.Injection (v 0) I r) (hSmall : ForcingSupportSize.Small (v 0) mu)
    (hRange : ForcingSupportedNames.Range (v 0) r A) (hFix : ForcingLabelPermutations.Fixing G A H) :
    ∃ X ordinal enum list,
      ForcingLocalNames.Carrier v G F bound H X ∧
      (Project.FirstOrderSemantics.reduct M).IsOrdinal ordinal ∧
      (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X ∧
      ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (v 6) list ∧
      ForcingOrdinalFixed.Fixed v G F H list := by
  obtain ⟨A',hA',hAI,hASmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hr hSmall
  have hAA := ForcingCohenOrderAction.image_unique hM hRange hA'
  subst A'
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hFix hAI
  have hHF := (hF H).mpr ⟨hGroup,A,H,hAI,hASmall,hFix,fun _ h => h⟩
  obtain ⟨X,hX⟩ := ForcingLocalNames.exists_carrier hM v G F bound H
  obtain ⟨ordinal,hCard,hEnum⟩ := ConstructionConcreteCardinals.cardinal_of_set hM hChoice X
  obtain ⟨enum,hEnum⟩ := hEnum
  obtain ⟨list,hList⟩ := ForcingCollectedName.exists_collected hM trueTest Fin.elim0 ordinal enum (v 6)
  have hFamily : ForcingOrdinalFixed.FixedFamily v G F H ordinal enum := by
    intro i hi name hin
    have hn := (hX name).mp (hEnum.1.1.output_mem_of_pairMember hin)
    exact ⟨hn.1.1,hn.2⟩
  have hInvariant : ForcingOrdinalFixed.Invariant trueTest Fin.elim0 v H ordinal :=
    fun _ _ _ _ _ _ _ _ _ _ _ => fun h => h
  exact ⟨X,ordinal,enum,list,hX,hCard.1,hEnum,hList,
    ForcingOrdinalFixed.collected_fixed hM trueTest Fin.elim0 v hp hG
      (ForcingNormalFilter.is_normal hM hw hMu hG hF) hGroup hHF hFamily hInvariant hList⟩

/-- The SAME enumerated list includes exactly the dense local-name values. -/
theorem mem_localList (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {G F bound H X ordinal enum list nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env (v 6))
    (hX : ForcingLocalNames.Carrier v G F bound H X)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (v 6) list)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (v 6)) :
    Forces false R env (v 6) nu list p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v 6) → MapRel R env q p →
        ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (v 6) ∧ MapRel R env s q ∧
          ∃ name, ForcingLocalNames.LocalName v G F bound H name ∧ Forces true R env (v 6) nu name s := by
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · intro h q hq hqp
    obtain ⟨s,name,t,hs,hsq,_,he,_,hEq⟩ := h.2 q hq hqp
    obtain ⟨_,i,_,hin,_⟩ := (ForcingCollectedName.edge_collected hM hList name t).mp he
    exact ⟨s,hs,hsq,name,(hX name).mp (hEnum.1.1.output_mem_of_pairMember hin),hEq⟩
  · intro h
    refine ⟨hp,fun q hq hqp => ?_⟩
    obtain ⟨s,hs,hsq,name,hn,hEq⟩ := h q hq hqp
    obtain ⟨i,hi,hin⟩ := hEnum.2 name ((hX name).mpr hn)
    exact ⟨s,name,s,hs,hsq,hs,(ForcingCollectedName.edge_collected hM hList name s).mpr
      ⟨hs,i,hi,hin,fun h => h⟩,hpre.1 s hs,hEq⟩

theorem localName_mem_localList (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {G F bound H X ordinal enum list nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env (v 6))
    (hX : ForcingLocalNames.Carrier v G F bound H X)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (v 6) list)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (v 6))
    (hNu : ForcingLocalNames.LocalName v G F bound H nu) : Forces false R env (v 6) nu list p :=
  (mem_localList hM R env v hpre hX hEnum hList hp).mpr
    (fun q hq _ => ⟨q,hq,hpre.1 q hq,nu,hNu,ForcingAtomicBasic.eq_refl hM hpre nu q hq⟩)

/-- All internal names and conditions, on this same collected list. -/
def laws {k n : Nat} (R : Formula (k+2)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F bound H list : Fin n) : Project.Formula 1 n :=
  let up2 : Fin n → Fin (n+2) := fun i => i.succ.succ
  let up3 : Fin n → Fin (n+3) := fun i => i.succ.succ.succ
  let up4 : Fin n → Fin (n+4) := fun i => i.succ.succ.succ.succ
  let up5 : Fin n → Fin (n+5) := fun i => i.succ.succ.succ.succ.succ
  let dense : Project.Formula 1 (n+2) := .forallE
    (.imp (.mem (.bound 0) (.bound (up3 (rho 6))))
      (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun i => up3 (base i)) 0 1))
        (.existsE (.conj (.mem (.bound 0) (.bound (up4 (rho 6))))
          (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun i => up4 (base i)) 0 1))
            (.existsE (.conj
              (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => up5 (rho j)) (up5 G) (up5 F) (up5 bound) (up5 H) 0))
              (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun i => up5 (base i)) (up5 (rho 6)) 4 0 1)))))))))
  let member := ProjectSyntax.encode id (ForcingAtomicRelations.forces false R (fun i => up2 (base i)) (up2 (rho 6)) 1 (up2 list) 0)
  .forallE (.forallE (.imp (.mem (.bound 0) (.bound (up2 (rho 6))))
    (.conj (.conj (.imp member dense) (.imp dense member))
      (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => up2 (rho j)) (up2 G) (up2 F) (up2 bound) (up2 H) 1)) member))))

theorem laws_freeClosed {k n : Nat} (R : Formula (k+2)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F bound H list : Fin n) : (laws R base rho G F bound H list).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (R : Formula (k+2)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F bound H list : Fin n) :
    Project.Formula.satisfies env (laws R base rho G F bound H list) ↔
      ∀ nu p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound (rho 6)) →
        ((Forces false R (fun i => env.bound (base i)) (env.bound (rho 6)) nu (env.bound list) p ↔
          ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env.bound (rho 6)) →
            MapRel R (fun i => env.bound (base i)) q p →
              ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (env.bound (rho 6)) ∧
                MapRel R (fun i => env.bound (base i)) s q ∧ ∃ name,
                  ForcingLocalNames.LocalName (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound H) name ∧
                  Forces true R (fun i => env.bound (base i)) (env.bound (rho 6)) nu name s) ∧
        (ForcingLocalNames.LocalName (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound H) nu →
          Forces false R (fun i => env.bound (base i)) (env.bound (rho 6)) nu (env.bound list) p)) := by
  simp only [laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLocalNames.localName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M)]
  constructor
  · intro h nu p hp
    exact ⟨⟨(h nu p hp).1.1,(h nu p hp).1.2⟩,(h nu p hp).2⟩
  · intro h nu p hp
    exact ⟨⟨(h nu p hp).1.mp,(h nu p hp).1.mpr⟩,(h nu p hp).2⟩

def constructionResult {k : Nat} (rho : Fin 7 → Fin k) (G F bound H mul : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+4) := fun i => i.succ.succ.succ.succ
  let body : Project.Formula 1 (k+4) :=
    .conj (ProjectSyntax.encode id (ForcingLocalNames.carrier (fun j => up (rho j)) (up G) (up F) (up bound) (up H) 3))
    (.conj (Project.Formula.isOrdinal (.bound 2))
    (.conj (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound 1) (.bound 2) (.bound 3))
    (.conj (ProjectSyntax.encode id (ForcingCollectedName.collected trueTest Fin.elim0 2 1 (up (rho 6)) 0))
    (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => up (rho j)) (up G) (up F) (up H) 0))
      (laws (orderFormula (rho 0) mul) up (fun j => up (rho j)) (up G) (up F) (up bound) (up H) 0)))))
  .existsE (.existsE (.existsE (.existsE body)))

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F bound r A H mul one : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A H))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
      (constructionResult rho G F bound H mul)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [constructionResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,laws_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F bound r A H mul one : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w mu G F bound r A H mul one)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M)]
  intro hw hMu hp hG hF hr hSmall hRange hFix hm
  obtain ⟨X,ordinal,enum,list,hX,hOrd,hEnum,hList,hFixed⟩ := construct hM hChoice (fun j => env (rho j)) hw hMu hp hG hF hr hSmall hRange hFix
  simp only [constructionResult,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLocalNames.carrier_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M),Project.Term.eval_bound]
  refine ⟨X,ordinal,enum,list,hX,hOrd,hEnum,hList,hFixed,?_⟩
  rw [laws_semantics hM]
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  intro nu p hp
  exact ⟨mem_localList hM (orderFormula (rho 0) mul) env (fun j => env (rho j)) hpre hX hEnum hList hp,
    fun hn => localName_mem_localList hM (orderFormula (rho 0) mul) env (fun j => env (rho j)) hpre hX hEnum hList hp hn⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F bound r A H mul one : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (constructionSentence rho I K B w mu G F bound r A H mul one))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (construction_models rho I K B w mu G F bound r A H mul one hL hChoice)

end PPAC.Migration.ForcingLocalList
