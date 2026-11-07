/- Fixed UniformImages.imageQuotient/imageQuotientGraph:177-240.
Reuse the already constructed kernel graph, literal quotientName collector,
and general relation-graph forcing theorems. No representative choices. -/
import PPAC.Migration.ForcingKernelImage
import PPAC.Migration.ForcingNonwellorderableQuotient

namespace PPAC.Migration.ForcingImageQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingPairUnion (domain domain_semantics)
open ForcingRelationGraphForcing (Holds)
open ForcingKernelImage (imageRelation ImageHolds)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
universe u v v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Eliminate the complete original surjection formula, retaining mapsTo. -/
private theorem surjection_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.surjection 0 1 2)) :
    Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2) := by
  rw [Source.SetLanguage.surjection,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_conj] at hf
  exact hf.1

private theorem surjection_onto (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B y q r : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.surjection 0 1 2))
    (hy : ForcingClassEvaluation.Predicate H env y)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hyB : Forces false R env P y B q)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ a, ForcingClassEvaluation.Predicate H env a ∧ Forces false R env P a A s ∧
        Force R H env (args3 h a y) P s (Source.SetLanguage.edge 0 1 2) := by
  rw [Source.SetLanguage.surjection,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 y hy
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hyB
  obtain ⟨s,hs,hsr,a,ha,haA,hay⟩ := hh r hr hrq
  exact ⟨s,hs,hsr,a,ha,haA,
    (ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 5) 4 3).mp hay⟩

private theorem mapsTo_total (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B a q r : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (ha : ForcingClassEvaluation.Predicate H env a)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (haA : Forces false R env P a A q)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ y, ForcingClassEvaluation.Predicate H env y ∧ Forces false R env P y B s ∧
        Force R H env (args3 h a y) P s (Source.SetLanguage.edge 0 1 2) := by
  rw [Source.SetLanguage.mapsTo,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_conj] at hf
  have hv := hf.2
  have hh := hf.1
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_conj] at hh
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh.2 a ha
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp haA
  obtain ⟨s,hs,hsr,y,hy,hay,_⟩ := hh r hr hrq
  have hApp : Force R H env (args3 h a y) P s (Source.SetLanguage.edge 0 1 2) :=
    (ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 4) 2 3).mp hay
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hsp := hpre.2 s q p hs hq hp hsq hqp
  have hyB := (ForcingFormula.force_all hM hpre hp _ _).mp hv a ha
  have hyB := (ForcingFormula.force_all hM hpre hp _ _).mp hyB y hy
  have hyB := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hyB s hs hsp
    (ForcingAtomicBasic.mem_mono hM hpre hs hsq haA)
  have hyB := (ForcingFormula.force_imp hM hpre hs _ _ _).mp hyB s hs (hpre.1 s hs)
    ((ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 5) 3 4).mpr hApp)
  exact ⟨s,hs,hsr,y,hy,hyB,hApp⟩


section Quotient
variable {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
variable (I K two w mu G F mul c top bit A h B E Q : Fin k)
variable (hM : FirstOrder.Theory.Models M nativeZF)
variable (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w)
  (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
variable (hG : ForcingLabelPermutations.Carrier (env I) (env G))
variable (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
variable (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
variable (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
variable (hc : ForcingConditionGraphs.FunctionOn (env K) (env c))
variable (ht : ForcingWithTopCarrier.Empty (env top))
variable (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env A))
variable (hEHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
variable (hQ : ForcingQuotientName.Quotient env rho G F mul I K c top bit A E (env Q))
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
include hM hp hG hF hw hMu hc ht hLabels hEHS hQ hpre

/-- Exact mem_imageQuotient: every internal HS class and condition, with
actual separated class witnesses, not selected quotient representatives. -/
theorem mem_imageQuotient {C p : M.Carrier .set}
    (hCHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) C)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) C (env Q) p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
          (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
          MapRel (orderFormula (rho 0) mul) env r q ∧ ∃ a ca,
            HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a ∧
            HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) ca ∧
            ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env
              (env (rho 6)) (env A) (env E) a ca ∧
            Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) r ∧
            Forces true (orderFormula (rho 0) mul) env (env (rho 6)) C ca r := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels).1
  rw [ForcingQuotientName.mem_quotient_iff_isClass hM env rho G F mul I K c top bit A E
    hp hG hF hw hMu hc ht hLabels hEHS hQ hCHS hpre hpW,
    ForcingRelationClass.forces_isClass hM env rho G F mul hp hG hNormal hpre hpW
      (args3 C (env A) (env E)) 0 1 2 hCHS hA hEHS]
  rfl

/-- Source imageQuotientGraph_mapsTo:203-214, the dense totality input. -/
theorem image_total {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingRelationGraphFunctions.Total (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) (env B) (env Q) p := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels).1
  intro y hy q hq hqp hyB r hr hrq
  have hyHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy
  obtain ⟨s,hs,hsr,a,ha,haA,hay⟩ := surjection_onto hM hpre hpW hf
    ((domain_semantics env rho G F y).mpr hyHS) hq hqp hyB hr hrq
  have haHS := (domain_semantics env rho G F a).mp ha
  obtain ⟨ca,hca,hclass⟩ := ForcingRelationClass.exists_class hM env rho G F mul hp hG hNormal hA hEHS haHS
  refine ⟨s,hs,hsr,ca,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hca,?_,?_⟩
  · apply (mem_imageQuotient env rho I K two w mu G F mul c top bit A E Q hM hp hG hF hw hMu hc ht hLabels hEHS hQ hpre hca hs).mpr
    intro t htc hts
    exact ⟨t,htc,hpre.1 t htc,a,ca,haHS,hca,hclass,
      ForcingAtomicBasic.mem_mono hM hpre htc hts haA,ForcingAtomicBasic.eq_refl hM hpre ca t htc⟩
  · apply (ForcingKernelImage.imageRelation_semantics env rho G F mul h A E s y ca).mpr
    intro t htc hts
    exact ⟨t,htc,hpre.1 t htc,a,ca,ha,(domain_semantics env rho G F ca).mpr hca,hclass,
      ForcingAtomicBasic.mem_mono hM hpre htc hts haA,
      ForcingFormula.mono hM hpre _ _ hs htc hts hay,ForcingAtomicBasic.eq_refl hM hpre ca t htc⟩

/-- Source imageQuotientGraph_surjection:227-240, the dense onto input. -/
theorem image_onto {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingRelationGraphFunctions.Onto (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (imageRelation rho G F mul h A E) env (env (rho 6)) (env G) (env F) (env B) (env Q) p := by
  intro C hCHS q hq hqp hCQ r hr hrq
  have hCHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hCHS
  obtain ⟨s,hs,hsr,a,ca,ha,hca,hclass,haA,hCca⟩ :=
    (mem_imageQuotient env rho I K two w mu G F mul c top bit A E Q hM hp hG hF hw hMu hc ht hLabels hEHS hQ hpre hCHS hq).mp hCQ r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hsp := hpre.2 s q p hs hq hpW hsq hqp
  obtain ⟨t,htc,hts,y,hy,hyB,hay⟩ := mapsTo_total hM hpre hpW
    (surjection_mapsTo hM hpre hpW hf) ((domain_semantics env rho G F a).mpr ha)
    hs hsp haA hs (hpre.1 s hs)
  refine ⟨t,htc,hpre.2 t s r htc hs hr hts hsr,y,
    (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr ((domain_semantics env rho G F y).mp hy),hyB,?_⟩
  apply (ForcingKernelImage.imageRelation_semantics env rho G F mul h A E t y C).mpr
  intro b hb hbt
  have hbs := hpre.2 b t s hb htc hs hbt hts
  exact ⟨b,hb,hpre.1 b hb,a,ca,(domain_semantics env rho G F a).mpr ha,
    (domain_semantics env rho G F ca).mpr hca,hclass,ForcingAtomicBasic.mem_mono hM hpre hb hbs haA,
    ForcingFormula.mono hM hpre _ _ htc hb hbt hay,ForcingAtomicBasic.eq_mono hM hpre hb hbs hCca⟩


/-- Literal source app_imageQuotientGraph:197-201 on the collected graph. -/
theorem app_imageQuotientGraph {J y C p : M.Carrier .set}
    (hBHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env B))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (imageRelation rho G F mul h A E) env (rho 6) top B Q J)
    (hyHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hCHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) C)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J y C)
      (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env B) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) C (env Q) p ∧
      ImageHolds (orderFormula (rho 0) mul) (domain rho G F) env
        (env (rho 6)) (env h) (env A) (env E) p y C := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hQHS := (ForcingQuotientName.hs_and_fixed hM env rho G F mul I K c top bit A E
    hp hG hF hw hMu hc ht hLabels hEHS hQ).1
  rw [← ForcingKernelImage.imageRelation_semantics env rho G F mul h A E p y C]
  exact ForcingRelationGraphApplication.app_graph hM env rho G F mul top B Q
    (imageRelation rho G F mul h A E) (args3 J y C) (0 : Fin 3) 1 2 hp hG hNormal ht hpre hBHS hQHS
    (ForcingKernelImage.image_monotone env rho G F mul h A E hpre)
    (ForcingKernelImage.image_congruent hM env rho G F mul h A E hpre)
    (ForcingKernelImage.image_regular env rho G F mul h A E hpre) hGraph hyHS hCHS hpW

/-- All three full source function conclusions on the SAME raw image graph.
The Total/One/Onto/Injective obligations are discharged here, not supplied. -/
theorem image_graph_forces {J p : M.Carrier .set}
    (hBHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env B))
    (hKernel : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (ForcingKernelImage.relation rho G F mul h A B) env (rho 6) top A A (env E))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (imageRelation rho G F mul h A E) env (rho 6) top B Q J)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env h) (env A) (env B))
      (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env B) (env Q))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2) ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env B) (env Q))
      (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2) ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env B) (env Q))
      (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels).1
  have hQHS := (ForcingQuotientName.hs_and_fixed hM env rho G F mul I K c top bit A E
    hp hG hF hw hMu hc ht hLabels hEHS hQ).1
  have hMono := ForcingKernelImage.image_monotone env rho G F mul h A E hpre
  have hCong := ForcingKernelImage.image_congruent hM env rho G F mul h A E hpre
  have hReg := ForcingKernelImage.image_regular env rho G F mul h A E hpre
  have hTot := image_total env rho I K two w mu G F mul c top bit A h B E Q hM
    hp hG hF hw hMu hc ht hLabels hEHS hQ hpre hpW hf
  have hOnto := image_onto env rho I K two w mu G F mul c top bit A h B E Q hM
    hp hG hF hw hMu hc ht hLabels hEHS hQ hpre hpW hf
  have hMaps := surjection_mapsTo hM hpre hpW hf
  have hOne := ForcingKernelImage.image_one hM env rho G F mul top h A B E
    hp hG hNormal ht hpre hA hKernel hpW hMaps
  have hInj := ForcingKernelImage.image_inj hM env rho G F mul top h A B E
    hp hG hNormal ht hpre hA hKernel hpW hMaps
  let v := args3 J (env B) (env Q)
  exact ⟨ForcingRelationGraphFunctions.graph_mapsTo hM env rho G F mul top B Q
      (imageRelation rho G F mul h A E) v (0 : Fin 3) 1 2 hp hG hNormal ht hpre hBHS hQHS
      hMono hCong hReg hGraph rfl rfl hTot hOne hpW,
    ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top B Q
      (imageRelation rho G F mul h A E) v (0 : Fin 3) 1 2 hp hG hNormal ht hpre hBHS hQHS
      hMono hCong hReg hGraph rfl rfl hTot hOne hOnto hpW,
    ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top B Q
      (imageRelation rho G F mul h A E) v (0 : Fin 3) 1 2 hp hG hNormal ht hpre hBHS hQHS
      hMono hCong hReg hGraph rfl rfl hTot hOne hInj hpW⟩

end Quotient


private theorem args3_map {α : Type v} {β : Type v2} (f : α → β) (a b c : α) :
    (fun j => f (args3 a b c j)) = args3 (f a) (f b) (f c) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

/-- All internal conditions, retaining the complete original surjection input. -/
def functionLaws {n m : Nat} (rho : Fin 7 → Fin n) (G F mul h A B Q : Fin n)
    (base : Fin n → Fin m) (J : Fin m) : Project.Formula 1 m :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let rr : Fin n → Fin (m+1) := fun j => (base j).succ
  let output := fun phi : Formula 3 => ProjectSyntax.encode id
    (ForcingFormula.formula R H rr (args3 J.succ (rr B) (rr Q)) (rr (rho 6)) 0 phi)
  .forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6))))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H rr
      (args3 (rr h) (rr A) (rr B)) (rr (rho 6)) 0 (Source.SetLanguage.surjection 0 1 2)))
      (.conj (output (Source.SetLanguage.mapsTo 0 1 2))
        (.conj (output (Source.SetLanguage.surjection 0 1 2)) (output (Source.SetLanguage.injection 0 1 2))))))

theorem functionLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (rho : Fin 7 → Fin n) (G F mul h A B Q : Fin n) (base : Fin n → Fin m) (J : Fin m) :
    Project.Formula.satisfies env (functionLaws rho G F mul h A B Q base J) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound (base (rho 6))) →
        Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
          (args3 (env.bound (base h)) (env.bound (base A)) (env.bound (base B)))
          (env.bound (base (rho 6))) p (Source.SetLanguage.surjection 0 1 2) →
        Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
          (args3 (env.bound J) (env.bound (base B)) (env.bound (base Q)))
          (env.bound (base (rho 6))) p (Source.SetLanguage.mapsTo 0 1 2) ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
          (args3 (env.bound J) (env.bound (base B)) (env.bound (base Q)))
          (env.bound (base (rho 6))) p (Source.SetLanguage.surjection 0 1 2) ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
          (args3 (env.bound J) (env.bound (base B)) (env.bound (base Q)))
          (env.bound (base (rho 6))) p (Source.SetLanguage.injection 0 1 2) := by
  simp only [functionLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingFormula.formula_semantics,args3_map,id_eq]
  rfl

/-- Universal source membership law, with every internal HS class parameter. -/
def membershipLaw {n m : Nat} (rho : Fin 7 → Fin n) (G F mul A E Q : Fin n)
    (base : Fin n → Fin m) : Project.Formula 1 m :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let rr : Fin n → Fin (m+2) := fun j => (base j).succ.succ
  let lhs := ProjectSyntax.encode id (ForcingAtomicRelations.forces false R rr (rr (rho 6)) 1 (rr Q) 0)
  let rhs := ProjectSyntax.encode id (ForcingFormula.formula R H rr (args3 1 (rr A) (rr E))
    (rr (rho 6)) 0 (ForcingEligibility.isClass 0 1 2))
  .forallE (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula
    (fun j => (base (rho j)).succ) (base G).succ (base (rho 6)).succ (base F).succ 0))
    (.forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6)))) (.conj (.imp lhs rhs) (.imp rhs lhs)))))

theorem membershipLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (rho : Fin 7 → Fin n) (G F mul A E Q : Fin n) (base : Fin n → Fin m) :
    Project.Formula.satisfies env (membershipLaw rho G F mul A E Q base) ↔
      ∀ C, HS actionFormula (fun j => env.bound (base (rho j)))
        (env.bound (base G)) (env.bound (base (rho 6))) (env.bound (base F)) C →
        ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound (base (rho 6))) →
          (Forces false (orderFormula (rho 0) mul) (fun j => env.bound (base j))
            (env.bound (base (rho 6))) C (env.bound (base Q)) p ↔
          Force (orderFormula (rho 0) mul) (domain rho G F) (fun j => env.bound (base j))
            (args3 C (env.bound (base A)) (env.bound (base E))) (env.bound (base (rho 6))) p
            (ForcingEligibility.isClass 0 1 2)) := by
  simp only [membershipLaw,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics,
    ForcingFormula.formula_semantics,ForcingAtomicRelations.forces_semantics,args3_map,id_eq]
  exact ⟨fun hh C hC p hp => ⟨(hh C hC p hp).1,(hh C hC p hp).2⟩,
    fun hh C hC p hp => ⟨(hh C hC p hp).mp,(hh C hC p hp).mpr⟩⟩

/-- The support, kernel graph, quotient and representative-free image graph
are all produced. Their raw collector witnesses and common support are kept. -/
def result {k : Nat} (rho : Fin 7 → Fin k) (I K G F mul c top bit A h B : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  let ra : Fin 7 → Fin (k+3) := fun j => up (rho j)
  let R := orderFormula (ra 0) (up mul)
  let QR := imageRelation ra (up G) (up F) (up mul) (up h) (up A) 1
  let fields : List (Project.Formula 1 (k+4)) :=
    [ProjectSyntax.encode Fin.succ (ForcingConjugationGraph.subgroup (up I) (up G) 2),
     .mem (.bound 3) (.bound (up F).succ),
     ProjectSyntax.encode id (ForcingTupleStabilizer.tupleFixed (fun j => (ra j).succ) (up G).succ (ra 6).succ
       (args3 (up h).succ (up A).succ (up B).succ) 3),
     ProjectSyntax.encode id (ForcingRelationGraph.graph R
       (ForcingKernelImage.relation ra (up G) (up F) (up mul) (up h) (up A) (up B))
       Fin.succ (ra 6) (up top) (up A) (up A) 2),
     ProjectSyntax.encode Fin.succ (ForcingHS.hs actionFormula ra (up G) (ra 6) (up F) 1),
     ProjectSyntax.encode Fin.succ (ForcingEquivariantMix.fixedAll ra 2 1),
     ProjectSyntax.encode id (ForcingQuotientName.quotient ra (up G) (up F) (up mul) (up I) (up K)
       (up c) (up top) (up bit) (up A) 1 Fin.succ 1),
     ProjectSyntax.encode Fin.succ (ForcingHS.hs actionFormula ra (up G) (ra 6) (up F) 0),
     ProjectSyntax.encode Fin.succ (ForcingEquivariantMix.fixedAll ra 2 0),
     ProjectSyntax.encode id (ForcingRelationGraph.graph R QR Fin.succ (ra 6) (up top) (up B) 0 0),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (ra j).succ) (up G).succ (ra 6).succ (up F).succ 0),
     ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (ra j).succ) 3 0),
     membershipLaw ra (up G) (up F) (up mul) (up A) 1 0 Fin.succ]
  .existsE (.existsE (.existsE (.existsE (fields.foldr (fun a b => .conj a b)
    (functionLaws ra (up G) (up F) (up mul) (up h) (up A) (up B) 0 Fin.succ 0)))))

private def premises {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A h B : Fin k) : List (Project.Formula 1 k) :=
  [Project.Formula.isOmega (.bound w),
   Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
   ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K two w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
   ProjectSyntax.encode id (Source.SetLanguage.functionOn c K),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit A),
   ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F h),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F B)]

def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A h B : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((premises rho I K two w mu G F mul c top bit A h B).foldr
    (fun a b => .imp a b) (result rho I K G F mul c top bit A h B))
  freeClosed := by
    simp -implicitDefEqProofs [premises,result,functionLaws,membershipLaw,List.foldr,
      Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed]


/-- Assemble the four actual source witnesses in every native ZF model.
The following original-kernel theorem is the delivery endpoint. -/
theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A h B : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K two w mu G F mul c top bit A h B)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),
    SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingSupportFilter.filter_semantics,
    ForcingConditionGraphs.functionOn_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingLabelSet.labelSet_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq]
  intro hw hMu hp hG hF hc ht hLabels hpre hh hB
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels).1
  obtain ⟨S,E,hS,hSF,hTuple,hKernel,hEHS,hFixed,_⟩ :=
    ForcingKernelImage.construct hM env rho I K two w G F mul top h A B hp hG hNormal ht hpre hh hA hB
  let up2 : Fin k → Fin (k+2) := fun j => j.succ.succ
  let ra2 : Fin 7 → Fin (k+2) := fun j => up2 (rho j)
  let env2 : Fin (k+2) → M.Carrier .set := Fin.cases E (Fin.cases S env)
  obtain ⟨Q,hQ2⟩ := ForcingQuotientName.exists_quotient hM env2 ra2 (up2 G) (up2 F) (up2 mul)
    (up2 I) (up2 K) (up2 c) (up2 top) (up2 bit) (up2 A) 0 hp hG hF hw hMu hc ht hLabels hEHS
  let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  let ra : Fin 7 → Fin (k+3) := fun j => up (rho j)
  let other : Fin (k+3) → M.Carrier .set := Fin.cases Q env2
  have he (j : Fin k) : other (up j) = env j := rfl
  have hEVal : other (1 : Fin (k+3)) = E := by
    change Fin.cases Q env2 (Fin.succ (0 : Fin (k+2))) = E
    rw [Fin.cases_succ]; rfl
  have hSVal : other (2 : Fin (k+3)) = S := by
    change Fin.cases Q env2 (Fin.succ (Fin.succ (0 : Fin (k+1)))) = S
    rw [Fin.cases_succ]; change Fin.cases E (Fin.cases S env) (Fin.succ (0 : Fin (k+1))) = S
    rw [Fin.cases_succ,Fin.cases_zero]
  have hQVal : other (0 : Fin (k+3)) = Q := rfl
  have hp' : Presentation (other (ra 0)) (other (up I)) (other (up K)) (other (up two)) (other (up w))
      (other (ra 1)) (other (ra 2)) (other (ra 3)) (other (ra 4)) (other (ra 5)) (other (ra 6)) := by
    simpa only [ra,he] using hp
  have hG' : ForcingLabelPermutations.Carrier (other (up I)) (other (up G)) := by simpa only [he] using hG
  have hF' : ForcingSupportFilter.Filter (other (up I)) (other (up G)) (other (up mu)) (other (up F)) := by
    simpa only [he] using hF
  have hNormal' : ForcingNormalFilter.Normal (other (up I)) (other (up G)) (other (up F)) := by
    simpa only [he] using hNormal
  have hA' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other (up A)) := by
    simpa only [ra,he] using hA
  have hB' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other (up B)) := by
    simpa only [ra,he] using hB
  have hE' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 1) := by
    simpa only [ra,he,hEVal] using hEHS
  have hS' : ForcingConjugationGraph.Subgroup (other (up I)) (other (up G)) (other 2) := by
    simpa only [he,hSVal] using hS
  have hSF' : (Project.FirstOrderSemantics.reduct M).mem (other 2) (other (up F)) := by
    simpa only [he,hSVal] using hSF
  have hTuple' : ForcingTupleStabilizer.TupleFixed (fun j => other (ra j)) (other (up G)) (other (ra 6))
      (args3 (other (up h)) (other (up A)) (other (up B))) (other 2) := by
    simpa only [ra,he,hSVal] using hTuple
  have hFixed' : ForcingSupportedNames.Supported (fun j => other (ra j)) (other 2) (other 1) := by
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
  have hKernel' : ForcingRelationGraph.Graph (orderFormula (ra 0) (up mul))
      (ForcingKernelImage.relation ra (up G) (up F) (up mul) (up h) (up A) (up B))
      other (ra 6) (up top) (up A) (up A) (other 1) := by
    simpa only [hEVal] using (ForcingKernelImage.kernel_graph_transport env other up he rho G F mul top h A B E).mp hKernel
  have hQuotient : ForcingQuotientName.Quotient other ra (up G) (up F) (up mul) (up I)
      (up K) (up c) (up top) (up bit) (up A) 1 (other 0) :=
    (ForcingNonwellorderableQuotient.quotient_transport env2 other Fin.succ (fun _ => rfl)
      ra2 (up2 G) (up2 F) (up2 mul) (up2 I) (up2 K) (up2 c) (up2 top) (up2 bit) (up2 A) 0 Q).mpr hQ2
  have hQdata := ForcingQuotientName.hs_and_fixed hM other ra (up G) (up F) (up mul) (up I)
    (up K) (up c) (up top) (up bit) (up A) 1 hp' hG' hF' hw hMu hc ht hLabels hE' hQuotient
  have hQfixed : ForcingSupportedNames.Supported (fun j => other (ra j)) (other 2) (other 0) := by
    intro pi hpi action ha
    exact hQdata.2 pi (hS'.1 pi hpi) action ha (hFixed' pi hpi action ha)
  have hBfixed : ForcingSupportedNames.Supported (fun j => other (ra j)) (other 2) (other (up B)) := by
    intro pi hpi action ha
    exact ForcingTupleStabilizer.fixed_action hM hTuple' hpi ha (2 : Fin 3)
  have hMoves := ForcingKernelImage.image_moves hM other ra (up I) (up K) (up two) (up w)
    (up G) (up F) (up mul) (up h) (up A) (up B) 1 2 hp' hG' hNormal' hA' hE' hTuple' hFixed'
  obtain ⟨J,hGraph,hJHS,hJfixed⟩ := ForcingRelationGraphSupport.construct hM
    (imageRelation ra (up G) (up F) (up mul) (up h) (up A) 1) other ra
    (up I) (up K) (up two) (up w) (up G) (up F) 2 (up mul) (up top) (up B) 0
    hp' hG' hNormal' hS' ht hB' hQdata.1 hBfixed hQfixed hMoves hSF'
  have hFunctions (p : M.Carrier .set)
      (hpW : (Project.FirstOrderSemantics.reduct M).mem p (other (ra 6)))
      (hf : Force (orderFormula (ra 0) (up mul)) (domain ra (up G) (up F)) other
        (args3 (other (up h)) (other (up A)) (other (up B))) (other (ra 6)) p (Source.SetLanguage.surjection 0 1 2)) :=
    image_graph_forces other ra (up I) (up K) (up two) (up w) (up mu) (up G) (up F)
      (up mul) (up c) (up top) (up bit) (up A) (up h) (up B) 1 0 hM
      hp' hG' hF' hw hMu hc ht hLabels hE' hQuotient hpre' hB' hKernel' hGraph hpW hf
  simp only [result,List.foldr,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConjugationGraph.subgroup_semantics,ForcingTupleStabilizer.tupleFixed_semantics,
    ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,ForcingSupportedNames.supported_semantics,
    ForcingQuotientName.quotient_semantics,membershipLaw_semantics hM,functionLaws_semantics hM,args3_map,id_eq]
  refine ⟨S,E,Q,J,hS',hSF',hTuple',hKernel',hE',hFixed',hQuotient,hQdata.1,hQfixed,hGraph,hJHS,hJfixed,?_,hFunctions⟩
  intro C hCHS p hpW
  exact ForcingQuotientName.mem_quotient_iff_isClass hM other ra (up G) (up F) (up mul) (up I)
    (up K) (up c) (up top) (up bit) (up A) 1 hp' hG' hF' hw hMu hc ht hLabels hE' hQuotient hCHS hpre' hpW

/-- Original YesMetaZFC proof kernel, with every raw source witness constructed. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A h B : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K two w mu G F mul c top bit A h B)) :=
  ModelTransfer.derives (fun _ hM => models rho I K two w mu G F mul c top bit A h B hM)


/-- Reuse the complete source function-formula eliminator without changing its existing proof. -/
theorem surjection_mapsTo_reuse (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.surjection 0 1 2)) :
    Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2) :=
  surjection_mapsTo hM hpre hp hf


/-- Reuse the complete source function-formula eliminator without changing its existing proof. -/
theorem surjection_onto_reuse (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B y q r : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.surjection 0 1 2))
    (hy : ForcingClassEvaluation.Predicate H env y)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hyB : Forces false R env P y B q)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ a, ForcingClassEvaluation.Predicate H env a ∧ Forces false R env P a A s ∧
        Force R H env (args3 h a y) P s (Source.SetLanguage.edge 0 1 2) :=
  surjection_onto hM hpre hp hf hy hq hqp hyB hr hrq


/-- Reuse the complete source function-formula eliminator without changing its existing proof. -/
theorem mapsTo_total_reuse (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p h A B a q r : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 h A B) P p (Source.SetLanguage.mapsTo 0 1 2))
    (ha : ForcingClassEvaluation.Predicate H env a)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (haA : Forces false R env P a A q)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ y, ForcingClassEvaluation.Predicate H env y ∧ Forces false R env P y B s ∧
        Force R H env (args3 h a y) P s (Source.SetLanguage.edge 0 1 2) :=
  mapsTo_total hM hpre hp hf ha hq hqp haA hr hrq


/-- Instantiate the already proved closed object sentence at actual inputs;
no raw kernel, quotient, image graph or final function law is assumed. -/
theorem result_from_inputs {k : Nat} (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A h B : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env.bound w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env.bound w) (env.bound mu))
    (hp : Presentation (env.bound (rho 0)) (env.bound I) (env.bound K) (env.bound two) (env.bound w)
      (env.bound (rho 1)) (env.bound (rho 2)) (env.bound (rho 3)) (env.bound (rho 4)) (env.bound (rho 5)) (env.bound (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env.bound I) (env.bound G))
    (hF : ForcingSupportFilter.Filter (env.bound I) (env.bound G) (env.bound mu) (env.bound F))
    (hc : ForcingConditionGraphs.FunctionOn (env.bound K) (env.bound c))
    (ht : ForcingWithTopCarrier.Empty (env.bound top))
    (hLabels : ForcingLabelSet.LabelSet (env.bound (rho 6)) (env.bound I) (env.bound K) (env.bound c) (env.bound top) (env.bound bit) (env.bound A))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env.bound (env.bound (rho 6)))
    (hh : HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) (env.bound h))
    (hB : HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) (env.bound B)) :
    Project.Formula.satisfies env (result rho I K G F mul c top bit A h B) := by
  have hs := models rho I K two w mu G F mul c top bit A h B hM
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),
    SetTheory.Structure.satisfiesSentence_iff] at hs
  have hs := (Project.Formula.satisfies_forallClosure_iff env.free _).mp (hs env.free) env.bound
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingSupportFilter.filter_semantics,
    ForcingConditionGraphs.functionOn_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingLabelSet.labelSet_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq] at hs
  exact hs hw hMu hp hG hF hc ht hLabels hpre hh hB

end PPAC.Migration.ForcingImageQuotient
