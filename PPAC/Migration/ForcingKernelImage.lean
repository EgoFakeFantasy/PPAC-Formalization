/- Pinned UniformImages.kernelRelation/kernelRelation_move/kernelGraph/
app_kernelGraph, app_kernelGraph_value and kernel_class_same_value:16-90.
Direct consumer: imageClassRelation and
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

/- Source RelationCalculus mapsTo_value/mapsTo_unique, specialized by
app_kernelGraph_value. Consume the FULL source function formula. -/
private theorem mapsTo_value (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q h A B x y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (hx : ForcingClassEvaluation.Predicate H env x) (hy : ForcingClassEvaluation.Predicate H env y)
    (hxA : Forces false R env P x A q)
    (hxy : Force R H env (args3 h x y) P q (Source.SetLanguage.edge 0 1 2)) :
    Forces false R env P y B q := by
  rw [Source.SetLanguage.mapsTo,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 x hx
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxA
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq)
  apply hh
  exact (ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 5) 3 4).mpr hxy

private theorem mapsTo_function (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2)) :
    Force R H env (Source.SetLanguage.args2 h A) P p (Source.SetLanguage.functionOn 0 1) := by
  rw [Source.SetLanguage.mapsTo,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp]
  have hh := hf.1
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp] at hh
  exact hh

private theorem mapsTo_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q h A B x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (hx : ForcingClassEvaluation.Predicate H env x) (hy : ForcingClassEvaluation.Predicate H env y)
    (hz : ForcingClassEvaluation.Predicate H env z)
    (hxA : Forces false R env P x A q)
    (hxy : Force R H env (args3 h x y) P q (Source.SetLanguage.edge 0 1 2))
    (hxz : Force R H env (args3 h x z) P q (Source.SetLanguage.edge 0 1 2)) :
    Forces true R env P y z q := by
  have hfunc := ForcingFormula.mono hM hpre (Source.SetLanguage.functionOn 0 1) _ hp hq hqp
    (mapsTo_function hM hpre hp hf)
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hq,ForcingFormula.force_conj] at hfunc
  have htotal := (ForcingFormula.force_all hM hpre hq _ _).mp hfunc.2 x hx
  have htotal := (ForcingFormula.force_imp hM hpre hq _ _ _).mp htotal q hq (hpre.1 q hq) hxA
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,t,ht,hxt,huniq⟩ := (ForcingFormula.force_ex R H env _ P q _).mp htotal r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have compare (u : M.Carrier .set) (hu : ForcingClassEvaluation.Predicate H env u)
      (hxu : Force R H env (args3 h x u) P q (Source.SetLanguage.edge 0 1 2)) :
      Forces true R env P u t s := by
    have hu' := (ForcingFormula.force_all hM hpre hs _ _).mp huniq u hu
    have hu' := (ForcingFormula.force_imp hM hpre hs _ _ _).mp hu' s hs (hpre.1 s hs)
    apply hu'
    apply (ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 5) 2 4).mpr
    exact ForcingFormula.mono hM hpre _ _ hq hs hsq hxu
  exact ⟨s,hs,hsr,ForcingAtomicLaws.eq_trans hM hpre (compare y hy hxy)
    (ForcingAtomicBasic.eq_symm hM (compare z hz hxz))⟩

private theorem kernel_value (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q h A B a b y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (ha : ForcingClassEvaluation.Predicate H env a) (_hb : ForcingClassEvaluation.Predicate H env b)
    (hy : ForcingClassEvaluation.Predicate H env y)
    (haA : Forces false R env P a A q)
    (hay : Force R H env (args3 h a y) P q (Source.SetLanguage.edge 0 1 2)) :
    Force R H env (Fin.lastCases b (Fin.lastCases a (args3 h A B))) P q kernelFormula ↔
      Forces false R env P b A q ∧ Force R H env (args3 h b y) P q (Source.SetLanguage.edge 0 1 2) := by
  rw [kernel_semantics hM hpre]
  constructor
  · intro hi
    have hd (r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P)
        (hrq : MapRel R env r q) :
        ∃ t, (Project.FirstOrderSemantics.reduct M).mem t P ∧ MapRel R env t r ∧
          Forces false R env P b A t ∧ Force R H env (args3 h b y) P t (Source.SetLanguage.edge 0 1 2) := by
      obtain ⟨t,ht,htr,z,hz,haA',hbA,_,haz,hbz⟩ := hi r hr hrq
      have htq := hpre.2 t r q ht hr hq htr hrq
      have htp := hpre.2 t q p ht hq hp htq hqp
      have he := mapsTo_unique hM hpre hp ht htp hf ha hz hy haA' haz
        (ForcingFormula.mono hM hpre _ _ hq ht htq hay)
      have hc := ForcingFormula.tuple_congr (H := H) hM hpre (Source.SetLanguage.edge (0 : Fin 3) 1 2)
        (args3 h b z) (args3 h b y) t ht
        (fun j => Fin.cases (ForcingAtomicBasic.eq_refl hM hpre h t ht)
          (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre b t ht) (Fin.cases he (fun j => Fin.elim0 j))) j)
      exact ⟨t,ht,htr,hbA,hc.mp hbz⟩
    constructor
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hq
      intro r hr hrq
      obtain ⟨t,ht,htr,hbA,_⟩ := hd r hr hrq
      exact ⟨t,ht,htr,hbA⟩
    · apply ForcingFormula.of_dense hM hpre _ _ hq
      intro r hr hrq
      obtain ⟨t,ht,htr,_,hby⟩ := hd r hr hrq
      exact ⟨t,ht,htr,hby⟩
  · rintro ⟨hbA,hby⟩ r hr hrq
    have hyB := mapsTo_value hM hpre hp hq hqp hf ha hy haA hay
    exact ⟨r,hr,hpre.1 r hr,y,hy,ForcingAtomicBasic.mem_mono hM hpre hr hrq haA,
      ForcingAtomicBasic.mem_mono hM hpre hr hrq hbA,ForcingAtomicBasic.mem_mono hM hpre hr hrq hyB,
      ForcingFormula.mono hM hpre _ _ hq hr hrq hay,ForcingFormula.mono hM hpre _ _ hq hr hrq hby⟩

/-- Pinned UniformImages.app_kernelGraph_value:61-78. -/
theorem app_kernelGraph_value    (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B : Fin k)
    {I K two w graph p q a b y : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A graph)
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a)
    (hb : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) b)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hqW : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (haA : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) q)
    (hay : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) a y)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph a b)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2) ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b (env A) q ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) b y)
          (env (rho 6)) q (Source.SetLanguage.edge 0 1 2) := by
  rw [app_kernelGraph hM env rho G F mul top h A B hp hG hF ht hpre hA hGraph ha hb hqW,
    relation_semantics]
  exact kernel_value hM hpre hpW hqW hqp hf
    ((domain_semantics env rho G F a).mpr ha) ((domain_semantics env rho G F b).mpr hb)
    ((domain_semantics env rho G F y).mpr hy) haA hay

/-- Pinned kernel_class_same_value:80-90, for the actual separated names. -/
theorem kernel_class_same_value    (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B : Fin k)
    {I K two w graph p q a b y ca cb : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A graph)
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a)
    (hb : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) b)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hqW : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (haA : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) q)
    (hay : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) a y)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2))
    (hbA : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b (env A) q)
    (hby : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) b y)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2))
    (hcaHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) ca)
    (hcbHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) cb)
    (hca : ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) graph a ca)
    (hcb : ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) graph b cb) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) ca cb q := by
  apply ForcingBasicSetAxioms.eq_of_same_members hM hpre hcaHS hcbHS hqW
  intro x hx r hr hrq
  have hrp := hpre.2 r q p hr hqW hpW hrq hqp
  rw [ForcingRelationClass.mem_class hM hpre hca hr,ForcingRelationClass.mem_class hM hpre hcb hr,
    app_kernelGraph_value hM env rho G F mul top h A B hp hG hF ht hpre hA hGraph ha hx hy hpW hr hrp hf
      (ForcingAtomicBasic.mem_mono hM hpre hr hrq haA) (ForcingFormula.mono hM hpre _ _ hqW hr hrq hay),
    app_kernelGraph_value hM env rho G F mul top h A B hp hG hF ht hpre hA hGraph hb hx hy hpW hr hrp hf
      (ForcingAtomicBasic.mem_mono hM hpre hr hrq hbA) (ForcingFormula.mono hM hpre _ _ hqW hr hrq hby)]

/-- Consume the existing exact class constructor twice; no supplied classes. -/
theorem construct_equal_classes    (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B : Fin k)
    {I K two w graph p q a b y : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A graph)
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a)
    (hb : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) b)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hqW : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (haA : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) q)
    (hay : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) a y)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2))
    (hbA : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b (env A) q)
    (hby : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) b y)
      (env (rho 6)) q (Source.SetLanguage.edge 0 1 2))
    (hGraphHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph) :
    ∃ ca cb, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) ca ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) cb ∧
      ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) graph a ca ∧
      ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) graph b cb ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) ca cb q := by
  obtain ⟨ca,hcaHS,hca⟩ := ForcingRelationClass.exists_class hM env rho G F mul hp hG hF hA hGraphHS ha
  obtain ⟨cb,hcbHS,hcb⟩ := ForcingRelationClass.exists_class hM env rho G F mul hp hG hF hA hGraphHS hb
  exact ⟨ca,cb,hcaHS,hcbHS,hca,hcb,kernel_class_same_value hM env rho G F mul top h A B
    hp hG hF ht hpre hA hGraph ha hb hy hpW hqW hqp hf haA hay hbA hby hcaHS hcbHS hca hcb⟩

private def valuePremises {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) : List (Project.Formula 1 k) :=
  premises rho I K two w G F mul top h A B ++
  [ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul)
      (relation rho G F mul h A B) id (rho 6) top A A graph),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F a),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F b),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F y),
   .mem (.bound p) (.bound (rho 6)),.mem (.bound q) (.bound (rho 6)),
   ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id q p),
   ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
     id (args3 h A B) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2)),
   ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) a A q),
   ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
     id (args3 h a y) (rho 6) q (Source.SetLanguage.edge 0 1 2))]

def valueResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul h A graph a b y q : Fin k) : Project.Formula 1 k :=
  let lhs := ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
    id (args3 graph a b) (rho 6) q (Source.SetLanguage.edge 0 1 2))
  let rhs : Project.Formula 1 k := .conj
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) b A q))
    (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
      id (args3 h b y) (rho 6) q (Source.SetLanguage.edge 0 1 2)))
  .conj (.imp lhs rhs) (.imp rhs lhs)

def valueSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((valuePremises rho I K two w G F mul top h A B graph a b y p q).foldr
    (fun a b => .imp a b) (valueResult rho G F mul h A graph a b y q))
  freeClosed := by
    simp -implicitDefEqProofs [valuePremises,premises,valueResult,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem value_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (valueSentence rho I K two w G F mul top h A B graph a b y p q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [valuePremises,premises,List.foldr_append,List.foldr,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,ForcingRelationGraph.graph_semantics,
    ForcingMapConditions.rel_semantics,ForcingFormula.formula_semantics,ForcingAtomicRelations.forces_semantics,args3_map,id_eq]
  intro hp hG hF ht hpre _hHS hA _hB hGraph ha hb hy hpW hqW hqp hf haA hay
  have hv := app_kernelGraph_value hM env rho G F mul top h A B hp hG hF ht hpre hA hGraph ha hb hy hpW hqW hqp hf haA hay
  simp only [valueResult,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingFormula.formula_semantics,
    ForcingAtomicRelations.forces_semantics,args3_map,id_eq]
  exact ⟨hv.mp,hv.mpr⟩

theorem value_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (valueSentence rho I K two w G F mul top h A B graph a b y p q)) :=
  ModelTransfer.derives (fun _ hM => value_models rho I K two w G F mul top h A B graph a b y p q hM)

def classResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul A graph a b q : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  .existsE (.existsE (.conj
    (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 1))
    (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 0))
    (.conj (ProjectSyntax.encode id (ForcingRelationClass.relationClass (orderFormula (rho 0) mul) (domain rho G F)
      up (up (rho 6)) (up A) (up graph) (up a) 1))
    (.conj (ProjectSyntax.encode id (ForcingRelationClass.relationClass (orderFormula (rho 0) mul) (domain rho G F)
      up (up (rho 6)) (up A) (up graph) (up b) 0))
      (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) up (up (rho 6)) 1 0 (up q))))))))

private def classPremises {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) : List (Project.Formula 1 k) :=
  valuePremises rho I K two w G F mul top h A B graph a b y p q ++
  [ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) b A q),
   ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
     id (args3 h b y) (rho 6) q (Source.SetLanguage.edge 0 1 2)),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F graph)]

def classSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((classPremises rho I K two w G F mul top h A B graph a b y p q).foldr
    (fun a b => .imp a b) (classResult rho G F mul A graph a b q))
  freeClosed := by
    simp -implicitDefEqProofs [classPremises,valuePremises,premises,classResult,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem class_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (classSentence rho I K two w G F mul top h A B graph a b y p q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [classPremises,valuePremises,premises,List.foldr_append,List.foldr,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,ForcingRelationGraph.graph_semantics,
    ForcingMapConditions.rel_semantics,ForcingFormula.formula_semantics,ForcingAtomicRelations.forces_semantics,args3_map,id_eq]
  intro hp hG hF ht hpre _hHS hA _hB hGraph ha hb hy hpW hqW hqp hf haA hay hbA hby hGraphHS
  obtain ⟨ca,cb,hcaHS,hcbHS,hca,hcb,he⟩ := construct_equal_classes hM env rho G F mul top h A B
    hp hG hF ht hpre hA hGraph ha hb hy hpW hqW hqp hf haA hay hbA hby hGraphHS
  simp only [classResult,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics,
    ForcingRelationClass.relationClass_semantics,ForcingAtomicRelations.forces_semantics,id_eq]
  exact ⟨ca,cb,hcaHS,hcbHS,hca,hcb,he⟩

theorem class_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w G F mul top h A B graph a b y p q : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (classSentence rho I K two w G F mul top h A B graph a b y p q)) :=
  ModelTransfer.derives (fun _ hM => class_models rho I K two w G F mul top h A B graph a b y p q hM)

/- Pinned UniformImages.imageClassRelation:93-169. The extra internal class
witness is the unique genuine separated name, by the existing class_unique;
it is not a chosen representative of a quotient. -/
def ImageHolds {k : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (P h A E p y C : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ a ca, ForcingClassEvaluation.Predicate H env a ∧ ForcingClassEvaluation.Predicate H env ca ∧
        ForcingRelationClass.Class R H env P A E a ca ∧ Forces false R env P a A r ∧
        Force R H env (args3 h a y) P r (Source.SetLanguage.edge 0 1 2) ∧ Forces true R env P C ca r

def imageHolds {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P h A E p y C : Fin m) : Formula m :=
  let up2 : Fin m → Fin (m+2) := fun j => j.castSucc.castSucc
  let up4 : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let a : Fin (m+4) := (Fin.last (m+2)).castSucc
  let ca : Fin (m+4) := Fin.last (m+3)
  let r : Fin (m+4) := (Fin.last (m+1)).castSucc.castSucc
  let body := (MinimalPredicates.pred H (fun j => up4 (base j)) a).conj
    ((MinimalPredicates.pred H (fun j => up4 (base j)) ca).conj
    ((ForcingRelationClass.relationClass R H (fun j => up4 (base j)) (up4 P) (up4 A) (up4 E) a ca).conj
    ((ForcingAtomicRelations.forces false R (fun j => up4 (base j)) (up4 P) a (up4 A) r).conj
    ((ForcingFormula.formula R H (fun j => up4 (base j)) (args3 (up4 h) a (up4 y)) (up4 P) r
      (Source.SetLanguage.edge 0 1 2)).conj
      (ForcingAtomicRelations.forces true R (fun j => up4 (base j)) (up4 P) (up4 C) ca r)))))
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) (up2 P)).conj
        ((ReplacementPredicates.rel R (fun j => up2 (base j)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (.ex (.ex body)))))))

theorem imageHolds_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P h A E p y C : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (imageHolds R H base P h A E p y C) ↔
      ImageHolds R H (fun j => env (base j)) (env P) (env h) (env A) (env E) (env p) (env y) (env C) := by
  simp only [imageHolds,ImageHolds,Formula.Realize,ForcingMapConditions.rel_semantics,
    ForcingClassEvaluation.predicate_semantics,ForcingRelationClass.relationClass_semantics,
    ForcingAtomicRelations.forces_semantics,ForcingFormula.formula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc,args3_map]
  rfl

def imageRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul h A E : Fin k) : Formula (k+3) :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  imageHolds (orderFormula (rho 0) mul) (domain rho G F) up (up (rho 6)) (up h) (up A) (up E)
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem imageRelation_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul h A E : Fin k) (p y C : M.Carrier .set) :
    Holds (imageRelation rho G F mul h A E) env p y C ↔
      ImageHolds (orderFormula (rho 0) mul) (domain rho G F) env
        (env (rho 6)) (env h) (env A) (env E) p y C := by
  unfold Holds imageRelation
  rw [imageHolds_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

private theorem image_mono_core {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P h A E p q y C : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hi : ImageHolds R H env P h A E p y C) : ImageHolds R H env P h A E q y C := by
  intro r hr hrq
  exact hi r hr (hpre.2 r q p hr hq hp hrq hqp)

private theorem image_regular_core {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P h A E p y C : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hi : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ImageHolds R H env P h A E r y C) :
    ImageHolds R H env P h A E p y C := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hh⟩ := hi q hq hqp
  obtain ⟨s,hs,hsr,a,ca,ha⟩ := hh r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,a,ca,ha⟩

private theorem image_congr_core (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P h A E p y y' C C' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hy : Forces true R env P y y' p) (hC : Forces true R env P C C' p) :
    ImageHolds R H env P h A E p y C ↔ ImageHolds R H env P h A E p y' C' := by
  have hp := ForcingAtomicBasic.condition hM hy
  have step {y y' C C' : M.Carrier .set} (hy : Forces true R env P y y' p)
      (hC : Forces true R env P C C' p) (hi : ImageHolds R H env P h A E p y C) :
      ImageHolds R H env P h A E p y' C' := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,a,ca,ha,hca,hClass,haA,hay,he⟩ := hi q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    have hy' := ForcingAtomicBasic.eq_mono hM hpre hr hrp hy
    have hc := ForcingFormula.tuple_congr (H := H) hM hpre (Source.SetLanguage.edge (0 : Fin 3) 1 2)
      (args3 h a y) (args3 h a y') r hr
      (fun j => Fin.cases (ForcingAtomicBasic.eq_refl hM hpre h r hr)
        (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre a r hr) (Fin.cases hy' (fun j => Fin.elim0 j))) j)
    exact ⟨r,hr,hrq,a,ca,ha,hca,hClass,haA,hc.mp hay,
      ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM
        (ForcingAtomicBasic.eq_mono hM hpre hr hrp hC)) he⟩
  exact ⟨step hy hC,step (ForcingAtomicBasic.eq_symm hM hy) (ForcingAtomicBasic.eq_symm hM hC)⟩

theorem image_monotone {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A E : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Monotone (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) := by
  intro p q y C hp hq hqp _ _ hi
  exact (imageRelation_semantics env rho G F mul h A E q y C).mpr
    (image_mono_core hpre hp hq hqp ((imageRelation_semantics env rho G F mul h A E p y C).mp hi))

theorem image_congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A E : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Congruent (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) := by
  intro p y C y' C' _ _ _ _ hy hC
  rw [imageRelation_semantics,imageRelation_semantics]
  exact image_congr_core hM hpre hy hC

theorem image_regular {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A E : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Regular (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) := by
  intro p y C _ _ _ hi
  apply (imageRelation_semantics env rho G F mul h A E p y C).mpr
  apply image_regular_core hpre
  intro q hq hqp
  obtain ⟨r,hr,hrq,hh⟩ := hi q hq hqp
  exact ⟨r,hr,hrq,(imageRelation_semantics env rho G F mul h A E r y C).mp hh⟩

/-- Pinned imageClassRelation_one:130-143. -/
theorem image_one    (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B E : Fin k)
    {I K two w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hE : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A (env E))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.One (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp y C D hy _ _ hC hD
  have hyHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy
  have hC := (imageRelation_semantics env rho G F mul h A E q y C).mp hC
  have hD := (imageRelation_semantics env rho G F mul h A E q y D).mp hD
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,a,ca,ha,hca,haClass,haA,hay,hCa⟩ := hC r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,htc,hts,b,cb,hb,hcb,hbClass,hbA,hby,hDb⟩ := hD s hs hsq
  have htp := hpre.2 t q p htc hq hpW (hpre.2 t s q htc hs hq hts hsq) hqp
  have hc := kernel_class_same_value hM env rho G F mul top h A B hp hG hF ht hpre hA hE
    ((domain_semantics env rho G F a).mp ha) ((domain_semantics env rho G F b).mp hb) hyHS
    hpW htc htp hf (ForcingAtomicBasic.mem_mono hM hpre htc hts haA)
    (ForcingFormula.mono hM hpre _ _ hs htc hts hay) hbA hby
    ((domain_semantics env rho G F ca).mp hca) ((domain_semantics env rho G F cb).mp hcb) haClass hbClass
  exact ⟨t,htc,hpre.2 t s r htc hs hr hts hsr,ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_mono hM hpre htc hts hCa)
    (ForcingAtomicLaws.eq_trans hM hpre hc (ForcingAtomicBasic.eq_symm hM hDb))⟩

/-- Pinned imageClassRelation_inj:145-169. -/
theorem image_inj    (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top h A B E : Fin k)
    {I K two w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hE : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A (env E))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.Injective (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp y z C hy hz _ hY hZ
  have hyHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy
  have hzHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz
  have hY := (imageRelation_semantics env rho G F mul h A E q y C).mp hY
  have hZ := (imageRelation_semantics env rho G F mul h A E q z C).mp hZ
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,a,ca,ha,_hca,haClass,haA,hay,hCa⟩ := hY r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,htc,hts,b,cb,hb,_hcb,hbClass,hbA,hbz,hCb⟩ := hZ s hs hsq
  have htp := hpre.2 t q p htc hq hpW (hpre.2 t s q htc hs hq hts hsq) hqp
  have ham := ForcingAtomicBasic.mem_mono hM hpre htc hts haA
  have haym := ForcingFormula.mono hM hpre _ _ hs htc hts hay
  have haHS := (domain_semantics env rho G F a).mp ha
  have hbHS := (domain_semantics env rho G F b).mp hb
  have haa : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a ca t :=
    (ForcingRelationClass.mem_class hM hpre haClass htc).mpr ⟨ham,
      (app_kernelGraph_value hM env rho G F mul top h A B hp hG hF ht hpre hA hE haHS haHS hyHS
        hpW htc htp hf ham haym).mpr ⟨ham,haym⟩⟩
  have heab := ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre htc hts hCa)) hCb
  have hab := (ForcingRelationClass.mem_class hM hpre hbClass htc).mp
    ((ForcingAtomicLaws.mem_congr_right hM hpre heab).mp haa)
  have haz := ((app_kernelGraph_value hM env rho G F mul top h A B hp hG hF ht hpre hA hE hbHS haHS hzHS
    hpW htc htp hf hbA hbz).mp hab.2).2
  exact ⟨t,htc,hpre.2 t s r htc hs hr hts hsr,mapsTo_unique hM hpre hpW htc htp hf
    ha ((domain_semantics env rho G F y).mpr hyHS) ((domain_semantics env rho G F z).mpr hzHS) ham haym haz⟩

/-- Pinned imageClassRelation_move:118-128, consuming the already fixed
kernel graph. The public moves theorem below discharges this fixedness
from the SAME graph's constructed three-name support. -/
theorem image_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul h A E : Fin k)
    {I K two w pi action p p' y y' C C' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (haction : MapRel actionFormula (fun j => env (rho j)) pi action)
    (hAHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hEHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hfixh : Action (env (rho 6)) action (env h) (env h))
    (hfixA : Action (env (rho 6)) action (env A) (env A))
    (hfixE : Action (env (rho 6)) action (env E) (env E))
    (_hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpp : PureKuratowski.PairMember M p p' action)
    (hyy : Action (env (rho 6)) action y y') (hCC : Action (env (rho 6)) action C C')
    (hi : ImageHolds (orderFormula (rho 0) mul) (domain rho G F) env
      (env (rho 6)) (env h) (env A) (env E) p y C) :
    ImageHolds (orderFormula (rho 0) mul) (domain rho G F) env
      (env (rho 6)) (env h) (env A) (env E) p' y' C' := by
  have hdata := (mapRel_action _ _ _).mp haction
  have har := ForcingProductFamily.action_permutation hdata
  have ho := ForcingProductFamily.order hM (env mul) hp hpi hdata
  obtain ⟨inv,hinv,hpii⟩ := ForcingConditionGraphs.exists_inverse hM hpi
  obtain ⟨ia,hia⟩ := ForcingProductFamily.exists_action hM hp hinv
  obtain ⟨conj,hconj,hc⟩ := ForcingConjugationGraph.exists_graph hM hG hpi hinv hpii
  have hctx := ForcingSeparation.normal_context hM (fun j => env (rho j)) hp hG hF hpi hinv hpii hconj hc
    haction ((mapRel_action _ _ _).mpr hia)
  intro q' hq' hqp'
  obtain ⟨q,hq,hqq⟩ := har.2.2 q' hq'
  have hqp : MapRel (orderFormula (rho 0) mul) env q p :=
    (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q p).mpr
      ((ho q p q' p' hqq hpp).mpr ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q' p').mp hqp'))
  obtain ⟨r,hr,hrq,a,ca,ha,hca,hClass,haA,hay,he⟩ := hi q hq hqp
  obtain ⟨r',hrr,_⟩ := har.1.1.2 r hr
  have hr' := har.1.2 r r' hrr
  have hrq' : MapRel (orderFormula (rho 0) mul) env r' q' :=
    (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r' q').mpr
      ((ho r q r' q' hrr hqq).mp ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r q).mp hrq))
  obtain ⟨a',haa⟩ := ForcingNameConjugacy.exists_action hM har.1 a
  have ha'HS := ForcingHSAction.hs_action hM hctx a ((domain_semantics env rho G F a).mp ha) a' haa
  obtain ⟨ca',hca'HS,hClass'⟩ := ForcingRelationClass.exists_class hM env rho G F mul hp hG hF hAHS hEHS ha'HS
  have hcaAct := ForcingRelationClassMove.relationClass_move hM env rho G F mul hp hG hF hpi haction
    (ForcingHS.isName hAHS) (ForcingHS.isName hca'HS) hfixA hfixE haa hClass hClass'
  have hmem := (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi haction (.mem (0 : Fin 2) 1)
    (Source.SetLanguage.args2 a (env A)) (Source.SetLanguage.args2 a' (env A))
    (fun j => Fin.cases haa (Fin.cases hfixA (fun j => Fin.elim0 j)) j) hr hrr).mp haA
  have happ := (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi haction (Source.SetLanguage.edge 0 1 2)
    (args3 (env h) a y) (args3 (env h) a' y')
    (fun j => Fin.cases hfixh (Fin.cases haa (Fin.cases hyy (fun j => Fin.elim0 j))) j) hr hrr).mp hay
  have heq := (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi haction (.equal (0 : Fin 2) 1)
    (Source.SetLanguage.args2 C ca) (Source.SetLanguage.args2 C' ca')
    (fun j => Fin.cases hCC (Fin.cases hcaAct (fun j => Fin.elim0 j)) j) hr hrr).mp he
  exact ⟨r',hr',hrq',a',ca',(domain_semantics env rho G F a').mpr ha'HS,
    (domain_semantics env rho G F ca').mpr hca'HS,hClass',hmem,happ,heq⟩

theorem image_moves (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K two w G F mul h A B E S : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hTuple : ForcingTupleStabilizer.TupleFixed (fun j => env (rho j)) (env G) (env (rho 6))
      (args3 (env h) (env A) (env B)) (env S))
    (hFixed : ForcingSupportedNames.Supported (fun j => env (rho j)) (env S) (env E)) :
    ForcingRelationGraphSupport.Moves (imageRelation rho G F mul h A E) env rho G F S := by
  intro pi hpi action ha p q y C y' C' hpW hpq _ _ hyy hCC hi
  have hfix := ForcingTupleStabilizer.fixed_action hM hTuple hpi ha
  apply (imageRelation_semantics env rho G F mul h A E q y' C').mpr
  exact image_move hM env rho G F mul h A E hp hG hF ((hG pi).mp ((hTuple pi).mp hpi).1) ha hA hE
    (hfix 0) (hfix 1) (hFixed pi hpi action ha) hpW hpq hyy hCC
    ((imageRelation_semantics env rho G F mul h A E p y C).mp hi)

/-- Change only parameter slots; the collected graph and every recursion
witness remain the SAME internal sets. Reuse the existing forcing congruence. -/
private theorem kernel_graph_reindex {k n : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin n → M.Carrier .set) (base : Fin k → Fin n) (he : ∀ j, other (base j) = env j)
    (rho : Fin 7 → Fin k) (G F mul top h A B : Fin k) (E : M.Carrier .set) :
    ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul h A B)
      env (rho 6) top A A E ↔
    ForcingRelationGraph.Graph (orderFormula (base (rho 0)) (base mul))
      (relation (fun j => base (rho j)) (base G) (base F) (base mul) (base h) (base A) (base B))
      other (base (rho 6)) (base top) (base A) (base A) E := by
  let R := orderFormula (rho 0) mul
  let T := orderFormula (base (rho 0)) (base mul)
  let H := domain rho G F
  let J := domain (fun j => base (rho j)) (base G) (base F)
  have hR (x y : M.Carrier .set) : MapRel R env x y ↔ MapRel T other x y := by
    simp only [R,T,ForcingProductSymmetry.orderFormula_semantics,he]
  have hH (x : M.Carrier .set) : ForcingClassEvaluation.Predicate H env x ↔ ForcingClassEvaluation.Predicate J other x := by
    simp only [H,J,domain_semantics,he]
  have hQ (p x y : M.Carrier .set) : Holds (relation rho G F mul h A B) env p x y ↔
      Holds (relation (fun j => base (rho j)) (base G) (base F) (base mul) (base h) (base A) (base B)) other p x y := by
    rw [relation_semantics,relation_semantics]
    simp only [he]
    exact ForcingSeparation.force_congr hR hH kernelFormula _ _ _
  have hTest (i p : M.Carrier .set) :
      MapRel (ForcingRelationGraph.testFormula R (relation rho G F mul h A B) (rho 6) A A) env i p ↔
      MapRel (ForcingRelationGraph.testFormula T
        (relation (fun j => base (rho j)) (base G) (base F) (base mul) (base h) (base A) (base B))
        (base (rho 6)) (base A) (base A)) other i p := by
    rw [ForcingRelationGraph.testFormula_semantics,ForcingRelationGraph.testFormula_semantics]
    simp only [ForcingRelationGraph.Test,he]
    apply exists_congr; intro a
    apply exists_congr; intro b
    apply exists_congr; intro x
    apply exists_congr; intro c
    apply exists_congr; intro y
    apply exists_congr; intro d
    exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (ForcingSeparation.atomic_congr hR false _ _ _ _) (and_congr
        (ForcingSeparation.atomic_congr hR false _ _ _ _) (hQ p x y)))))
  dsimp only [R,T] at hTest
  unfold ForcingRelationGraph.Graph
  simp only [he]
  apply exists_congr; intro carrier
  apply exists_congr; intro entries
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,hTest]

def imageResult {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top h A B : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  let ra : Fin 7 → Fin (k+2) := fun j => up (rho j)
  let R := orderFormula (ra 0) (up mul)
  let H := domain ra (up G) (up F)
  let Q := imageRelation ra (up G) (up F) (up mul) (up h) (up A) 0
  let tail : Project.Formula 1 (k+2) := .forallE (.imp (.mem (.bound 0) (.bound (ra 6).succ))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H Fin.succ
      (args3 (up h).succ (up A).succ (up B).succ) (ra 6).succ 0 (Source.SetLanguage.mapsTo 0 1 2)))
      (.conj (ProjectSyntax.encode id (ForcingRelationGraphFunctions.one R (ForcingRelationGraphApplication.actionAt ra)
        Q Fin.succ (ra 6).succ (up G).succ (up F).succ 0))
        (ProjectSyntax.encode id (ForcingRelationGraphFunctions.injective R (ForcingRelationGraphApplication.actionAt ra)
          Q Fin.succ (ra 6).succ (up G).succ (up F).succ 0)))))
  let fields : List (Project.Formula 1 (k+2)) :=
    [ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (up I) (up G) 1),
     .mem (.bound 1) (.bound (up F)),
     ProjectSyntax.encode id (ForcingTupleStabilizer.tupleFixed ra (up G) (ra 6) (args3 (up h) (up A) (up B)) 1),
     ProjectSyntax.encode id (ForcingRelationGraph.graph R (relation ra (up G) (up F) (up mul) (up h) (up A) (up B))
       id (ra 6) (up top) (up A) (up A) 0),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula ra (up G) (ra 6) (up F) 0),
     ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll ra 1 0),
     ProjectSyntax.encode id (ForcingRelationGraphForcing.monotone R (ForcingRelationGraphApplication.actionAt ra) Q id (ra 6) (up G) (up F)),
     ProjectSyntax.encode id (ForcingRelationGraphForcing.congruent R (ForcingRelationGraphApplication.actionAt ra) Q id (ra 6) (up G) (up F)),
     ProjectSyntax.encode id (ForcingRelationGraphForcing.regular R (ForcingRelationGraphApplication.actionAt ra) Q id (ra 6) (up G) (up F)),
     ProjectSyntax.encode id (ForcingRelationGraphSupport.moves Q id ra (up G) (up F) 1)]
  .existsE (.existsE (fields.foldr (fun a b => .conj a b) tail))

def imageSentence {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((premises rho I K two w G F mul top h A B).foldr
    (fun a b => .imp a b) (imageResult rho I G F mul top h A B))
  freeClosed := by
    simp -implicitDefEqProofs [premises,imageResult,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem image_models {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (imageSentence rho I K two w G F mul top h A B)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq]
  intro hp hG hF ht hpre hh hA hB
  obtain ⟨S,E,hS,hSF,hTuple,hGraph,hEHS,hFixed,_⟩ := construct hM env rho I K two w G F mul top h A B
    hp hG hF ht hpre hh hA hB
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  let ra : Fin 7 → Fin (k+2) := fun j => up (rho j)
  let other : Fin (k+2) → M.Carrier .set := Fin.cases E (Fin.cases S env)
  have he (j : Fin k) : other (up j) = env j := rfl
  have hEVal : other (0 : Fin (k+2)) = E := rfl
  have hSVal : other (1 : Fin (k+2)) = S := by
    change Fin.cases E (Fin.cases S env) (Fin.succ (0 : Fin (k+1))) = S
    rw [Fin.cases_succ,Fin.cases_zero]
  have hp' : Presentation (other (ra 0)) (other (up I)) (other (up K)) (other (up two)) (other (up w))
      (other (ra 1)) (other (ra 2)) (other (ra 3)) (other (ra 4)) (other (ra 5)) (other (ra 6)) := by
    simpa only [ra,he] using hp
  have hG' : ForcingLabelPermutations.Carrier (other (up I)) (other (up G)) := by simpa only [he] using hG
  have hF' : ForcingNormalFilter.Normal (other (up I)) (other (up G)) (other (up F)) := by simpa only [he] using hF
  have ht' : ForcingWithTopCarrier.Empty (other (up top)) := by simpa only [he] using ht
  have hA' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other (up A)) := by
    simpa only [ra,he] using hA
  have hE' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 0) := by
    simpa only [ra,he,hEVal] using hEHS
  have hTuple' : ForcingTupleStabilizer.TupleFixed (fun j => other (ra j)) (other (up G)) (other (ra 6))
      (args3 (other (up h)) (other (up A)) (other (up B))) (other 1) := by
    simpa only [ra,he,hSVal,hEVal] using hTuple
  have hFixed' : ForcingSupportedNames.Supported (fun j => other (ra j)) (other 1) (other 0) := by
    simpa only [ra,he,hSVal,hEVal] using hFixed
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (ra 0) (up mul)) other x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,ra,he]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (ra 0) (up mul)) other (other (ra 6)) := by
    constructor
    · intro p hpW
      exact (hR p p).mp (hpre.1 p hpW)
    · intro p q r hpW hqW hrW hpq hqr
      exact (hR p r).mp (hpre.2 p q r hpW hqW hrW ((hR p q).mpr hpq) ((hR q r).mpr hqr))
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) (up mul))
      (relation ra (up G) (up F) (up mul) (up h) (up A) (up B)) other (ra 6) (up top) (up A) (up A) (other 0) :=
    (kernel_graph_reindex env other up he rho G F mul top h A B E).mp hGraph
  have hMono := image_monotone other ra (up G) (up F) (up mul) (up h) (up A) 0 hpre'
  have hCong := image_congruent hM other ra (up G) (up F) (up mul) (up h) (up A) 0 hpre'
  have hReg := image_regular other ra (up G) (up F) (up mul) (up h) (up A) 0 hpre'
  have hMove := image_moves hM other ra (up I) (up K) (up two) (up w) (up G) (up F) (up mul)
    (up h) (up A) (up B) 0 1 hp' hG' hF' hA' hE' hTuple' hFixed'
  have hFunctions (p : M.Carrier .set) (hpW : (Project.FirstOrderSemantics.reduct M).mem p (other (ra 6)))
      (hf : Force (orderFormula (ra 0) (up mul)) (domain ra (up G) (up F)) other
        (args3 (other (up h)) (other (up A)) (other (up B))) (other (ra 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
      ForcingRelationGraphFunctions.One (orderFormula (ra 0) (up mul)) (ForcingRelationGraphApplication.actionAt ra)
        (imageRelation ra (up G) (up F) (up mul) (up h) (up A) 0) other (other (ra 6)) (other (up G)) (other (up F)) p ∧
      ForcingRelationGraphFunctions.Injective (orderFormula (ra 0) (up mul)) (ForcingRelationGraphApplication.actionAt ra)
        (imageRelation ra (up G) (up F) (up mul) (up h) (up A) 0) other (other (ra 6)) (other (up G)) (other (up F)) p :=
    ⟨image_one hM other ra (up G) (up F) (up mul) (up top) (up h) (up A) (up B) 0 hp' hG' hF' ht' hpre' hA' hGraph' hpW hf,
      image_inj hM other ra (up G) (up F) (up mul) (up top) (up h) (up A) (up B) 0 hp' hG' hF' ht' hpre' hA' hGraph' hpW hf⟩
  simp only [imageResult,List.foldr,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingTupleStabilizer.tupleFixed_semantics,ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,
    ForcingSupportedNames.supported_semantics,ForcingRelationGraphForcing.monotone_semantics,ForcingRelationGraphForcing.congruent_semantics,
    ForcingRelationGraphForcing.regular_semantics,ForcingRelationGraphSupport.moves_semantics,ForcingFormula.formula_semantics,
    ForcingRelationGraphFunctions.one_semantics,ForcingRelationGraphFunctions.injective_semantics,args3_map,id_eq]
  exact ⟨S,E,hS,hSF,hTuple',hGraph',hE',hFixed',hMono,hCong,hReg,hMove,hFunctions⟩

theorem image_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top h A B : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (imageSentence rho I K two w G F mul top h A B)) :=
  ModelTransfer.derives (fun _ hM => image_models rho I K two w G F mul top h A B hM)

end PPAC.Migration.ForcingKernelImage
