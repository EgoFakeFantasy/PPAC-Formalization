/- Pinned UniformImages.kernelRelation/kernelRelation_move/kernelGraph/
app_kernelGraph:16-59. Direct consumer: imageClassRelation and
nonwellorderable_image_bijection:243-276. The relation is the regular
existential composition of the two bounded applications, with no selected
function values or class representatives. Reuse the actual collector,
three-name stabilizer and complete source forcing formula. -/
import PPAC.Migration.ForcingRelationGraphFunctions
import PPAC.Migration.ForcingTupleStabilizer

namespace PPAC.Migration.ForcingKernelImage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingPairUnion (domain domain_semantics)
open ForcingStabilizer (Action)
open ForcingRelationGraphForcing (Holds Monotone Congruent Regular)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
universe u v v'
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Slots h,A,B,a,b. The witness is an HS name in the forcing interpretation. -/
def kernelFormula : Formula 5 :=
  .ex ((Formula.mem 3 1).conj ((Formula.mem 4 1).conj ((Formula.mem 5 2).conj
    ((Source.SetLanguage.edge 0 3 5).conj (Source.SetLanguage.edge 0 4 5)))))

private theorem args3_map {a : Type v} {b : Type v'} (f : a → b) (x y z : a) :
    (fun j => f (args3 x y z j)) = args3 (f x) (f y) (f z) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) j

def relation {k : Nat} (rho : Fin 7 → Fin k) (G F mul h A B : Fin k) : Formula (k+3) :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
    (Fin.lastCases (Fin.last (k+2)) (Fin.lastCases (Fin.last (k+1)).castSucc
      (args3 (up h) (up A) (up B)))) (up (rho 6)) (Fin.last k).castSucc.castSucc kernelFormula

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul h A B : Fin k) (p x y : M.Carrier .set) :
    Holds (relation rho G F mul h A B) env p x y ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases y (Fin.lastCases x (args3 (env h) (env A) (env B))))
        (env (rho 6)) p kernelFormula := by
  simp only [relation,Holds,ForcingFormula.formula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  have hv : (fun j => Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))
      (Fin.lastCases (Fin.last (k+2)) (Fin.lastCases (Fin.last (k+1)).castSucc
        (args3 h.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc)) j)) =
      Fin.lastCases y (Fin.lastCases x (args3 (env h) (env A) (env B))) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
      · simp only [Fin.lastCases_castSucc]
        simpa only [Fin.lastCases_castSucc] using congrFun
          (args3_map (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env)))
            h.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc) i
  rw [hv]

/-- Exact dense witness semantics of the source composition. -/
theorem kernel_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B a b : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases b (Fin.lastCases a (args3 h A B))) P p kernelFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          ∃ z, ForcingClassEvaluation.Predicate H env z ∧
            Forces false R env P a A r ∧ Forces false R env P b A r ∧ Forces false R env P z B r ∧
            Force R H env (args3 h a z) P r (Source.SetLanguage.edge 0 1 2) ∧
            Force R H env (args3 h b z) P r (Source.SetLanguage.edge 0 1 2) := by
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ z, _ ∧ _ ∧ _ ∧ _ ∧
    Force R H env (Fin.lastCases z (Fin.lastCases b (Fin.lastCases a (args3 h A B)))) P r
      (Source.SetLanguage.edge 0 3 5) ∧
    Force R H env (Fin.lastCases z (Fin.lastCases b (Fin.lastCases a (args3 h A B)))) P r
      (Source.SetLanguage.edge 0 4 5)) ↔ _
  constructor
  · intro hh q hq hqp
    obtain ⟨r,hr,hrq,z,hz,ha,hb,hzB,haz,hbz⟩ := hh q hq hqp
    exact ⟨r,hr,hrq,z,hz,ha,hb,hzB,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 6) 3 5).mp haz,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 6) 4 5).mp hbz⟩
  · intro hh q hq hqp
    obtain ⟨r,hr,hrq,z,hz,ha,hb,hzB,haz,hbz⟩ := hh q hq hqp
    exact ⟨r,hr,hrq,z,hz,ha,hb,hzB,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 6) 3 5).mpr haz,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 6) 4 5).mpr hbz⟩

theorem monotone (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A B : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Monotone (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relation rho G F mul h A B) env (env (rho 6)) (env G) (env F) := by
  intro p q x y hp hq hqp _ _ hh
  exact (relation_semantics env rho G F mul h A B q x y).mpr
    (ForcingFormula.mono hM hpre _ _ hp hq hqp
      ((relation_semantics env rho G F mul h A B p x y).mp hh))

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A B : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Congruent (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relation rho G F mul h A B) env (env (rho 6)) (env G) (env F) := by
  intro p x y x' y' _ _ _ _ hx hy
  rw [relation_semantics,relation_semantics]
  have hp := ForcingAtomicBasic.condition hM hx
  apply ForcingFormula.tuple_congr hM hpre kernelFormula _ _ p hp
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [Fin.lastCases_last] using hy
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hx
    · simpa only [Fin.lastCases_castSucc] using
        ForcingAtomicBasic.eq_refl hM hpre (args3 (env h) (env A) (env B) i) p hp

theorem regular (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A B : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Regular (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relation rho G F mul h A B) env (env (rho 6)) (env G) (env F) := by
  intro p x y hp _ _ hh
  apply (relation_semantics env rho G F mul h A B p x y).mpr
  apply ForcingFormula.of_dense hM hpre _ _ hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,hi⟩ := hh q hq hqp
  exact ⟨r,hr,hrq,(relation_semantics env rho G F mul h A B r x y).mp hi⟩

theorem relation_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A B : Fin k)
    {I K two w pi action p q x y x' y' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi action)
    (hh : Action (env (rho 6)) action (env h) (env h))
    (hA : Action (env (rho 6)) action (env A) (env A))
    (hB : Action (env (rho 6)) action (env B) (env B))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q action)
    (hxx : Action (env (rho 6)) action x x') (hyy : Action (env (rho 6)) action y y')
    (hi : Holds (relation rho G F mul h A B) env p x y) :
    Holds (relation rho G F mul h A B) env q x' y' := by
  apply (relation_semantics env rho G F mul h A B q x' y').mpr
  apply (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha kernelFormula
    (Fin.lastCases y (Fin.lastCases x (args3 (env h) (env A) (env B))))
    (Fin.lastCases y' (Fin.lastCases x' (args3 (env h) (env A) (env B))))
    (by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.lastCases_last] using hyy
      · refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hxx
        · simp only [Fin.lastCases_castSucc]
          exact Fin.cases hh (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))) i) hpW hpq).mp
  exact (relation_semantics env rho G F mul h A B p x y).mp hi

/-- Pinned app_kernelGraph, including the two bounds recovered by regularity. -/
theorem app_kernelGraph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B : Fin k)
    {I K two w graph p x y : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A graph)
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x y)
      (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
      Holds (relation rho G F mul h A B) env p x y := by
  rw [ForcingRelationGraphApplication.app_graph hM env rho G F mul top A A
    (relation rho G F mul h A B) (args3 graph x y) 0 1 2 hp hG hF ht hpre hA hA
    (monotone hM env rho G F mul h A B hpre) (congruent hM env rho G F mul h A B hpre)
    (regular hM env rho G F mul h A B hpre) hGraph hx hy hpW]
  constructor
  · exact fun hi => hi.2.2
  · intro hi
    have hd := (kernel_semantics hM hpre).mp ((relation_semantics env rho G F mul h A B p x y).mp hi)
    refine ⟨?_,?_,hi⟩
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hpW
      intro q hq hqp
      obtain ⟨r,hr,hrq,z,_,hxA,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hxA⟩
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hpW
      intro q hq hqp
      obtain ⟨r,hr,hrq,z,_,_,hyA,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hyA⟩

/-- Source kernelGraph and kernelGraph_fixed. The common support is produced,
not supplied. Both graph coordinates use the SAME A. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hh : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env h))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hB : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env B)) :
    ∃ support graph, ForcingConjugationGraph.Subgroup (env I) (env G) support ∧
      (Project.FirstOrderSemantics.reduct M).mem support (env F) ∧
      ForcingTupleStabilizer.TupleFixed (fun j => env (rho j)) (env G) (env (rho 6))
        (args3 (env h) (env A) (env B)) support ∧
      ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
        env (rho 6) top A A graph ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) support graph ∧
      (∀ x y p, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
        HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y →
        (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        (Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x y)
          (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
          Holds (relation rho G F mul h A B) env p x y)) := by
  obtain ⟨support,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM (fun j => env (rho j))
    hp hG hF (args3 (env h) (env A) (env B))
    (fun j => Fin.cases hh (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))) j)
  obtain ⟨J,f,hJ,hf⟩ := ForcingProductEntries.construct (t := env top) hM (ForcingHS.isName hA) (ForcingHS.isName hA)
  let Q := relation rho G F mul h A B
  let test := ForcingRelationGraph.testFormula (orderFormula (rho 0) mul) Q (rho 6) A A
  obtain ⟨graph,hGraph⟩ := ForcingCollectedName.exists_collected hM test env J f (env (rho 6))
  have hfamily := ForcingProductEntries.family_hs hM (fun j => env (rho j)) hp hG hF ht hA hA hJ hf
  have hPerm : ForcingCollectedHS.Permutes test env (fun j => env (rho j)) support J f (env (rho 6)) := by
    intro pi hpi action ha
    have hfix := ForcingTupleStabilizer.fixed_action hM hTuple hpi ha
    apply ForcingRelationGraphSupport.move_entries hM Q env rho I K two w G F mul top A A
      hp hG hF ((hG pi).mp (hS.1 pi hpi)) ha ht hA hA (hfix 1) (hfix 1) _ hJ hf
    intro p q x y x' y' hpW hpq _ _ hxx hyy hi
    exact relation_move hM env rho G F mul h A B hp hG hF ((hG pi).mp (hS.1 pi hpi)) ha
      (hfix 0) (hfix 1) (hfix 2) hpW hpq hxx hyy hi
  refine ⟨support,graph,hS,hSF,hTuple,⟨J,f,hJ,hf,hGraph⟩,
    ForcingCollectedHS.collect_HS hM test env (fun j => env (rho j)) hp hG hF hS hSF hfamily hPerm hGraph,?_,?_⟩
  · intro pi hpi action ha
    exact ForcingCollectedHS.fixed hM test env (fun j => env (rho j)) hp hG hS hfamily hPerm hGraph hpi ha
  · intro x y p hx hy hpW
    exact app_kernelGraph hM env rho G F mul top h A B hp hG hF ht hpre hA
      ⟨J,f,hJ,hf,hGraph⟩ hx hy hpW

/-- Universal application law on the SAME graph. Native binders prepend
variables; source forcing blocks remain intact under the existing encoder. -/
def application {k m : Nat} (rho : Fin 7 → Fin k) (G F mul h A B : Fin k)
    (base : Fin k → Fin m) (graph : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+3) := fun j => j.succ.succ.succ
  let rr : Fin k → Fin (m+3) := fun j => up (base j)
  let lhs := ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul)
    (domain rho G F) rr (args3 (up graph) 2 1) (rr (rho 6)) 0 (Source.SetLanguage.edge 0 1 2))
  let rhs := ProjectSyntax.encode id (ForcingRelationGraphSupport.relation (relation rho G F mul h A B) rr 0 2 1)
  .forallE (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (base (rho j)).succ)
      (base G).succ (base (rho 6)).succ (base F).succ 0))
    (.forallE (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (base (rho j)).succ.succ)
        (base G).succ.succ (base (rho 6)).succ.succ (base F).succ.succ 0))
      (.forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6)))) (.conj (.imp lhs rhs) (.imp rhs lhs)))))))

theorem application_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (rho : Fin 7 → Fin k) (G F mul h A B : Fin k) (base : Fin k → Fin m) (graph : Fin m) :
    Project.Formula.satisfies env
      (application rho G F mul h A B base graph) ↔
    ∀ x y p,
      HS actionFormula (fun j => env.bound (base (rho j))) (env.bound (base G)) (env.bound (base (rho 6))) (env.bound (base F)) x →
      HS actionFormula (fun j => env.bound (base (rho j))) (env.bound (base G)) (env.bound (base (rho 6))) (env.bound (base F)) y →
      (Project.FirstOrderSemantics.reduct M).mem p (env.bound (base (rho 6))) →
      (Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
        (args3 (env.bound graph) x y) (env.bound (base (rho 6))) p (Source.SetLanguage.edge 0 1 2) ↔
        Holds (relation rho G F mul h A B) (fun j => env.bound (base j)) p x y) := by
  simp only [application,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics,
    ForcingFormula.formula_semantics,ForcingRelationGraphSupport.relation_semantics,
    args3_map,id_eq]
  exact ⟨fun hh x y p hx hy hp => ⟨(hh x hx y hy p hp).1,(hh x hx y hy p hp).2⟩,
    fun hh x hx y hy p hp => ⟨(hh x y p hx hy hp).mp,(hh x y p hx hy hp).mpr⟩⟩

def result {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top h A B : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  .existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (up I) (up G) 1))
    (.conj (.mem (.bound 1) (.bound (up F)))
    (.conj (ProjectSyntax.encode id (ForcingTupleStabilizer.tupleFixed (fun j => up (rho j)) (up G) (up (rho 6))
      (args3 (up h) (up A) (up B)) 1))
    (.conj (ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      up (rho 6) top A A 0))
    (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 0))
    (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => up (rho j)) 1 0))
      (application rho G F mul h A B up 0))))))))

private def premises {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k) :
    List (Project.Formula 1 k) :=
  [ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K two w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
    ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
    ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
    ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
    ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F h),
    ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
    ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F B)]

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((premises rho I K two w G F mul top h A B).foldr
    (fun a b => .imp a b) (result rho I G F mul top h A B))
  freeClosed := by
    simp -implicitDefEqProofs [premises,result,application,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K two w G F mul top h A B)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics,ForcingLabelPermutations.carrier_semantics,
    ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics]
  intro hp hG hF ht hpre hh hA hB
  obtain ⟨support,graph,hS,hSF,hTuple,hGraph,hHS,hFixed,hApp⟩ :=
    construct hM env rho I K two w G F mul top h A B hp hG hF ht hpre hh hA hB
  simp only [result,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConjugationGraph.subgroup_semantics,ForcingTupleStabilizer.tupleFixed_semantics,
    ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,ForcingSupportedNames.supported_semantics,
    application_semantics hM,args3_map,id_eq]
  exact ⟨support,graph,hS,hSF,hTuple,hGraph,hHS,hFixed,hApp⟩

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K two w G F mul top h A B)) :=
  ModelTransfer.derives (fun _ hM => models rho I K two w G F mul top h A B hM)

end PPAC.Migration.ForcingKernelImage
