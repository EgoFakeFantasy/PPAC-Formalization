/- Fixed TailGraphs.BinaryRelation.app_graph, on the actual Product HS domain.
The action reindexing below preserves the exact stabilizer/HS definition. -/
import PPAC.Migration.ForcingPairFormula
import PPAC.Migration.ForcingRelationGraphForcing

namespace PPAC.Migration.ForcingRelationGraphApplication
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingHS (HS)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingRelationGraphForcing (Holds Monotone Congruent Regular)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def actionAt {n : Nat} (rho : Fin 7 → Fin n) : Formula (n+2) :=
  ReplacementPredicates.rel actionFormula (fun j => (rho j).castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1))

theorem actionAt_semantics {n : Nat} (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n)
    (g a : M.Carrier .set) :
    MapRel (actionAt rho) env g a ↔ MapRel actionFormula (fun j => env (rho j)) g a := by
  unfold MapRel actionAt
  rw [ForcingMapConditions.rel_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem hs_actionAt {n : Nat} (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n)
    (G P F sigma : M.Carrier .set) :
    HS (actionAt rho) env G P F sigma ↔ HS actionFormula (fun j => env (rho j)) G P F sigma := by
  simp only [ForcingHS.HS,ForcingHS.Closed,ForcingStabilizer.Symmetric,
    ForcingStabilizer.Stabilizer,ForcingStabilizer.Fixed,actionAt_semantics]

theorem app_graph (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul t X Y : Fin n)
    (Q : Formula (n+3)) (v : Fin m → M.Carrier .set) (f x y : Fin m) {I K B w p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hmono : Monotone (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hcongr : Congruent (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hregular : Regular (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y (v f))
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v x))
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v y))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.edge f x y) ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (v x) (env X) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (v y) (env Y) p ∧ Holds Q env p (v x) (v y) := by
  have htW := (hpres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env r (env t) :=
    fun r _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r (env t)).mpr (Or.inl ht)
  obtain ⟨b,hb⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env t) (v x) (v y)
  exact (ForcingPairFormula.app_iff_mem_opair hM env rho G F mul v f x y hpres hG hF ht hpre hx hy hb hp).trans
    (ForcingRelationGraphForcing.pair_mem_graph hM (orderFormula (rho 0) mul) (actionAt rho) Q env (rho 6) G F t X Y
      hpre htW htop ((hs_actionAt env rho _ _ _ _).mpr hX) ((hs_actionAt env rho _ _ _ _).mpr hY)
      hmono hcongr hregular hgraph ((hs_actionAt env rho _ _ _ _).mpr hx) ((hs_actionAt env rho _ _ _ _).mpr hy) hb hp)

def applicationSentence {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name x y p : Fin n) : Source.Sentence :=
  (((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingWithTopCarrier.empty t).imp
    ((ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F X).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F Y).imp
    ((ForcingRelationGraphForcing.monotone (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp
    ((ForcingRelationGraphForcing.congruent (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp
    ((ForcingRelationGraphForcing.regular (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp
    ((ForcingRelationGraph.graph (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F x).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F y).imp
    ((Formula.mem p (rho 6)).imp
    ((ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge name x y)).iff
      ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x X p).conj
        ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) y Y p).conj
          (ForcingRelationGraphSupport.relation Q id p x y))))))))))))))))))).close

theorem application_models {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name x y p : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (applicationSentence Q rho I K B w G F mul t X Y name x y p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpres hG hF ht hpre hX hY hmono hcongr hregular hgraph hx hy hp
  have h := app_graph hM env rho G F mul t X Y Q env name x y
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)
    ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY)
    ((ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hmono)
    ((ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hcongr)
    ((ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hregular)
    ((ForcingRelationGraph.graph_semantics (M := M) env (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).mp hgraph)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F x).mp hx)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F y).mp hy) hp
  constructor
  · intro hf
    obtain ⟨hx,hy,hQ⟩ := h.mp ((ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge name x y)).mp hf)
    exact ⟨(ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) x X p).mpr hx,
      (ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) y Y p).mpr hy,
      (ForcingRelationGraphSupport.relation_semantics (M := M) env Q id p x y).mpr hQ⟩
  · rintro ⟨hx,hy,hQ⟩
    exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge name x y)).mpr
      (h.mpr ⟨(ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) x X p).mp hx,
        (ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) y Y p).mp hy,
        (ForcingRelationGraphSupport.relation_semantics (M := M) env Q id p x y).mp hQ⟩)

theorem application_kernel_certificate {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name x y p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (applicationSentence Q rho I K B w G F mul t X Y name x y p)) :=
  ModelTransfer.derives (fun _ hM => application_models Q rho I K B w G F mul t X Y name x y p hM)

end PPAC.Migration.ForcingRelationGraphApplication
