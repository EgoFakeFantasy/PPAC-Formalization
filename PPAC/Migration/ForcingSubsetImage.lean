/- Pinned SliceGeometry.defaultRelation_unique_on/subsetImageGraph/subset_image_surjection.
Reuse the accepted default relation and actual tuple-supported graph constructor. -/
import PPAC.Migration.ForcingDefaultRelation

namespace PPAC.Migration.ForcingSubsetImage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingDefaultRelation (Default)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Unlike the earlier global partial-uniqueness lemma, source only assumes
functionality ON A. The two genuine applications have the same member of A. -/
theorem unique_on (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q f A B D d a y z : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hf : Force R H env (args3 f A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (ha : Predicate H env a) (hy : Predicate H env y) (hz : Predicate H env z)
    (hA : Forces false R env P a A q)
    (hY : Default R H env P f D d a y q) (hZ : Default R H env P f D d a z q) :
    Forces true R env P y z q := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,hLeft | hRight⟩ := (ForcingDefaultRelation.default_iff hM hpre hq).mp hY r hr hrq
  · obtain ⟨t,ht,hts,hLeft' | hRight'⟩ := (ForcingDefaultRelation.default_iff hM hpre hq).mp hZ s hs
      (hpre.2 s r q hs hr hq hsr hrq)
    · have htq := hpre.2 t s r ht hs hr hts hsr
      have htq' := hpre.2 t r q ht hr hq htq hrq
      exact ⟨t,ht,htq,ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht
        (hpre.2 t q p ht hq hp htq' hqp) hf ha hy hz
        (ForcingAtomicBasic.mem_mono hM hpre ht htq' hA)
        (ForcingFormula.mono hM hpre _ _ hs ht hts hLeft.1) hLeft'.1⟩
    · exact (hRight'.1 t ht (hpre.1 t ht) y hy
        (ForcingFormula.mono hM hpre _ _ hs ht hts hLeft.1)
        (ForcingAtomicBasic.mem_mono hM hpre ht hts hLeft.2)).elim
  · obtain ⟨t,ht,hts,hLeft' | hRight'⟩ := (ForcingDefaultRelation.default_iff hM hpre hq).mp hZ s hs
      (hpre.2 s r q hs hr hq hsr hrq)
    · exact (hRight.1 t ht hts z hz hLeft'.1 hLeft'.2).elim
    · exact ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,ForcingAtomicLaws.eq_trans hM hpre
        (ForcingAtomicBasic.eq_mono hM hpre ht hts hRight.2)
        (ForcingAtomicBasic.eq_symm hM hRight'.2)⟩

/-- A finite syntactic parameter tuple; every value is an internal set. -/
def four {α : Type v} (f A D d : α) : Fin 4 → α :=
  Fin.cases f (Fin.cases A (Fin.cases D (Fin.cases d Fin.elim0)))

private theorem four_map {α : Type v} {β : Type u} (g : α → β) (f A D d : α) :
    (fun j => g (four f A D d j)) = four (g f) (g A) (g D) (g d) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) j

/-- Source defaultRelation bounded by A and D, with no new choice of defaults. -/
def subsetFormula : Formula 6 :=
  (Formula.mem 4 1).conj ((Formula.mem 5 2).conj (ForcingDefaultRelation.defaultFormula.rename
    (ForcingMapCalculus.five (0 : Fin 6) 2 3 4 5)))

def relation {k : Nat} (rho : Fin 7 → Fin k) (G F mul f A D d : Fin k) : Formula (k+3) :=
  ForcingMapCalculus.relationOf rho G F mul (four f A D d) subsetFormula

theorem relation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f A D d : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p a y : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    ForcingRelationGraphForcing.Holds (relation rho G F mul f A D d) env p a y ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env D) p ∧
      Default (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6))
        (env f) (env D) (env d) a y p := by
  rw [relation,ForcingMapCalculus.relationOf_semantics]
  simp only [subsetFormula,ForcingFormula.force_conj,ForcingSound.rename hM hpre _ _ _ _ hp]
  rfl

/-- Full source subset_image_surjection, for the actual raw bounded-default
collector. The graph and common support are constructed below in models. -/
theorem graph_surjection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top f A target D d : Fin k) {graph p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hD : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env D))
    (hd : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env d))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho G F mul f A D d)
      env (rho 6) top A D graph)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) (env A) (env target)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2))
    (hSub : ForcingPowerName.SubsetF (orderFormula (rho 0) mul) (domain rho G F) env
      (env (rho 6)) p (env D) (env target))
    (hMem : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env D) p) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env A) (env D))
      (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let Q := relation rho G F mul f A D d
  let ns := four f A D d
  have hMaps := ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hp hf
  apply ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top A D Q
    (args3 graph (env A) (env D)) 0 1 2 hPres hG hF ht hpre hA hD
    (ForcingMapCalculus.monotone hM env rho G F mul ns subsetFormula hpre)
    (ForcingMapCalculus.congruent hM env rho G F mul ns subsetFormula hpre)
    (ForcingMapCalculus.regular hM env rho G F mul ns subsetFormula hpre) hGraph rfl rfl ?_ ?_ ?_ hp
  · intro a ha q hq hqp haA r hr hrq
    obtain ⟨s,hs,hsr,y,hy,hyD,hDefault⟩ := ForcingDefaultRelation.total hM hpre hq
      ((domain_semantics env rho G F (env d)).mpr hd) (ForcingAtomicBasic.mem_mono hM hpre hq hqp hMem) r hr hrq
    exact ⟨s,hs,hsr,y,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F y).mp hy),hyD,(relation_semantics hM env rho G F mul f A D d hpre hs).mpr
      ⟨ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) haA,hyD,hDefault⟩⟩
  · intro q hq hqp a y z ha hy hz hY hZ
    obtain ⟨haA,_hyD,hDefaultY⟩ := (relation_semantics hM env rho G F mul f A D d hpre hq).mp hY
    obtain ⟨_haA,_hzD,hDefaultZ⟩ := (relation_semantics hM env rho G F mul f A D d hpre hq).mp hZ
    exact unique_on hM hpre hp hq hqp hMaps
      ((domain_semantics env rho G F a).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp ha))
      ((domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy))
      ((domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz))
      haA hDefaultY hDefaultZ
  · intro y hy q hq hqp hyD r hr hrq
    have hyHS := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
    obtain ⟨s,hs,hsr,a,ha,haA,hApp⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hf hyHS
      hq hqp (hSub y hyHS q hq hqp hyD) hr hrq
    have hsD := ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hyD
    exact ⟨s,hs,hsr,a,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F a).mp ha),haA,(relation_semantics hM env rho G F mul f A D d hpre hs).mpr
      ⟨haA,hsD,ForcingDefaultRelation.of_app hM hpre hs hApp hsD⟩⟩

/-- Source subset-image implication at EVERY internal condition, keeping the
full source surjection and the single explicitly given default. -/
def laws {n m : Nat} (rho : Fin 7 → Fin n) (G F mul f A target D d : Fin n)
    (base : Fin n → Fin m) (graph : Fin m) : Project.Formula 1 m :=
  let rr : Fin n → Fin (m+1) := fun j => (base j).succ
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  .forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6))))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H rr
      (args3 (rr f) (rr A) (rr target)) (rr (rho 6)) 0 (Source.SetLanguage.surjection 0 1 2)))
      (.imp (ProjectSyntax.encode id (ForcingPowerName.subsetF R H rr (rr (rho 6)) 0 (rr D) (rr target)))
        (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces false R rr (rr (rho 6)) (rr d) (rr D) 0))
          (ProjectSyntax.encode id (ForcingFormula.formula R H rr
            (args3 graph.succ (rr A) (rr D)) (rr (rho 6)) 0 (Source.SetLanguage.surjection 0 1 2)))))))

def result {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top f A target D d : Fin k) : Project.Formula 1 k :=
  ForcingMapCalculus.produced rho I G F mul top (four f A D d) subsetFormula 1 2
    (laws (fun j => (rho j).succ) G.succ F.succ mul.succ f.succ A.succ target.succ D.succ d.succ Fin.succ 0)

theorem result_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top f A target D d : Fin k) :
    (result rho I G F mul top f A target D d).FreeClosed := by
  simp -implicitDefEqProofs [result,ForcingMapCalculus.produced,laws,List.foldr,
    Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f A target D d : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F D),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F d)].foldr
      Definitional.Formula.imp (result rho I G F mul top f A target D d))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,result_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f A target D d : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F mul top f A target D d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq]
  intro hPres hG hF ht hpre hf hA hD hd
  have hNames (j : Fin 4) : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F)
      (env (four f A D d j)) :=
    Fin.cases hf (Fin.cases hA (Fin.cases hD (Fin.cases hd (fun i => Fin.elim0 i)))) j
  obtain ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed⟩ := ForcingMapCalculus.actual_reuse hM env rho I K B w G F mul top
    (four f A D d) subsetFormula 1 2 hPres hG hF ht hNames
  let other : Fin (k+1) → M.Carrier .set := Fin.cases S env
  let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have he (j : Fin k) : other j.succ = env j := rfl
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (ra 0) mul.succ) other x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,ra,he]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (ra 0) mul.succ) other (other (ra 6)) := by
    constructor
    · intro p hp
      exact (hR p p).mp (hpre.1 p hp)
    · intro p q r hp hq hr hpq hqr
      exact (hR p r).mp (hpre.2 p q r hp hq hr ((hR p q).mpr hpq) ((hR q r).mpr hqr))
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) mul.succ)
      (relation ra G.succ F.succ mul.succ f.succ A.succ D.succ d.succ)
      other (ra 6) top.succ A.succ D.succ J := by
    have hns : (fun j => (four f A D d j).succ) = four f.succ A.succ D.succ d.succ :=
      four_map (fun j : Fin k => j.succ) f A D d
    have hDom : four f A D d (1 : Fin 4) = A := rfl
    have hCod : four f A D d (2 : Fin 4) = D := rfl
    simpa only [relation,hns,hDom,hCod] using hGraph
  have hFunctions (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p (other (ra 6))) :=
    graph_surjection hM other ra I.succ K.succ B.succ w.succ G.succ F.succ mul.succ top.succ
      f.succ A.succ target.succ D.succ d.succ hPres hG hF ht hpre' hA hD hd hGraph' hp
  simp only [result,ForcingMapCalculus.produced,laws,List.foldr,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingTupleStabilizer.tupleFixed_semantics,ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,
    ForcingEquivariantMix.fixedAll_semantics,ForcingFormula.formula_semantics,ForcingPowerName.subsetF_semantics,
    ForcingAtomicRelations.forces_semantics,four_map,id_eq]
  exact ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed,hFunctions⟩

/-- Ordinary nativeZF original proof kernel; no L or Choice assumption. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f A target D d : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F mul top f A target D d)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul top f A target D d hM)

end PPAC.Migration.ForcingSubsetImage
