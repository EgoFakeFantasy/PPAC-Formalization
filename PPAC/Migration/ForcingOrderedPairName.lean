/- Fixed OrbitNames.Name.opair and Name.smul_opair, consumed by
TailGraphs.productEntry and BinaryRelation.graph, then AssignedGraphs.assignmentGraph.
Compose the existing literal PairName, HS closure and condition-map recursion. -/
import PPAC.Migration.ForcingProductHSPair

namespace PPAC.Migration.ForcingOrderedPairName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingPairName (PairName)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def orderedPairName {n : Nat} (t sigma tau output : Fin n) : Formula n :=
  .ex (.ex ((ForcingPairName.pairName t.castSucc.castSucc sigma.castSucc.castSucc
    sigma.castSucc.castSucc (Fin.last n).castSucc).conj
    ((ForcingPairName.pairName t.castSucc.castSucc sigma.castSucc.castSucc
      tau.castSucc.castSucc (Fin.last (n+1))).conj
    (ForcingPairName.pairName t.castSucc.castSucc (Fin.last n).castSucc
      (Fin.last (n+1)) output.castSucc.castSucc))))

def OrderedPairName (t sigma tau output : M.Carrier .set) : Prop :=
  ∃ a b, PairName t sigma sigma a ∧ PairName t sigma tau b ∧ PairName t a b output

theorem orderedPairName_semantics {n : Nat} (v : Fin n → M.Carrier .set)
    (t sigma tau output : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (orderedPairName t sigma tau output) ↔ OrderedPairName (v t) (v sigma) (v tau) (v output) := by
  simp only [orderedPairName,OrderedPairName,Formula.Realize,
    ForcingPairName.pairName_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_orderedPairName (hM : FirstOrder.Theory.Models M nativeZF)
    (t sigma tau : M.Carrier .set) : ∃ output, OrderedPairName t sigma tau output := by
  obtain ⟨a,ha⟩ := ForcingPairName.exists_pairName hM t sigma sigma
  obtain ⟨b,hb⟩ := ForcingPairName.exists_pairName hM t sigma tau
  obtain ⟨output,ho⟩ := ForcingPairName.exists_pairName hM t a b
  exact ⟨output,a,b,ha,hb,ho⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {t sigma tau x y : M.Carrier .set}
    (hx : OrderedPairName t sigma tau x) (hy : OrderedPairName t sigma tau y) : x = y := by
  obtain ⟨a,b,ha,hb,hx⟩ := hx
  obtain ⟨c,d,hc,hd,hy⟩ := hy
  have hac := ForcingPairName.unique hM ha hc
  have hbd := ForcingPairName.unique hM hb hd
  subst c; subst d
  exact ForcingPairName.unique hM hx hy

theorem isName (hM : FirstOrder.Theory.Models M nativeZF)
    {P t sigma tau name : M.Carrier .set} (hn : OrderedPairName t sigma tau name)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (hs : ForcingNames.IsName P sigma) (hu : ForcingNames.IsName P tau) :
    ForcingNames.IsName P name := by
  obtain ⟨a,b,ha,hb,hn⟩ := hn
  exact ForcingPairName.isName hM hn ht
    (ForcingPairName.isName hM ha ht hs hs) (ForcingPairName.isName hM hb ht hs hu)

theorem orderedPair_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t sigma tau name : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t)
    (hs : ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F sigma)
    (hu : ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F tau)
    (hn : OrderedPairName t sigma tau name) :
    ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F name := by
  obtain ⟨a,b,ha,hb,hn⟩ := hn
  exact ForcingProductHSPair.pair_hs hM v hp hG hF ht
    (ForcingProductHSPair.pair_hs hM v hp hG hF ht hs hs ha)
    (ForcingProductHSPair.pair_hs hM v hp hG hF ht hs hu hb) hn

theorem map_orderedPairName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set}
    (hf : ForcingMapConditions.IsFunction f params)
    {t sigma tau name q x y output : M.Carrier .set} (h : OrderedPairName t sigma tau name)
    (ht : ForcingMapConditions.MapRel f params t q)
    (hs : ForcingMapConditions.Mapped f params sigma x)
    (hu : ForcingMapConditions.Mapped f params tau y)
    (ho : ForcingMapConditions.Mapped f params name output) : OrderedPairName q x y output := by
  obtain ⟨a,b,ha,hb,hn⟩ := h
  obtain ⟨c,hc⟩ := ForcingMapConditions.exists_mapping hM f params hf a
  obtain ⟨d,hd⟩ := ForcingMapConditions.exists_mapping hM f params hf b
  exact ⟨c,d,ForcingPairName.map_pairName hM hf ha ht hs hs hc,
    ForcingPairName.map_pairName hM hf hb ht hs hu hd,
    ForcingPairName.map_pairName hM hf hn ht hc hd ho⟩

def existenceSentence : Source.Sentence := (Formula.ex (orderedPairName (0 : Fin 4) 1 2 3)).close

def uniquenessSentence : Source.Sentence :=
  ((orderedPairName (0 : Fin 5) 1 2 3).imp ((orderedPairName 0 1 2 4).imp (.equal 3 4))).close

def nameSentence : Source.Sentence :=
  ((orderedPairName (1 : Fin 5) 2 3 4).imp ((Formula.mem 1 0).imp
    ((ForcingNames.isName 0 2).imp ((ForcingNames.isName 0 3).imp (ForcingNames.isName 0 4))))).close

def mappingSentence {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n) : Source.Sentence :=
  ((ForcingMapConditions.function f id).imp ((orderedPairName t sigma tau name).imp
    ((ReplacementPredicates.rel f id t q).imp ((ForcingMapConditions.mapping f id sigma x).imp
      ((ForcingMapConditions.mapping f id tau y).imp ((ForcingMapConditions.mapping f id name output).imp
        (orderedPairName q x y output))))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, ho⟩ := exists_orderedPairName hM (v 0) (v 1) (v 2)
  refine ⟨output, ?_⟩
  let env : Fin 4 → M.Carrier .set := Fin.lastCases output v
  apply (orderedPairName_semantics (M := M) env 0 1 2 3).mpr
  exact ho

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((orderedPairName_semantics (M := M) v 0 1 2 3).mp hx) ((orderedPairName_semantics (M := M) v 0 1 2 4).mp hy)

theorem name_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence nameSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h ht hs hu
  exact (ForcingNames.isName_semantics (M := M) v 0 4).mpr
    (isName hM ((orderedPairName_semantics (M := M) v 1 2 3 4).mp h) ht
      ((ForcingNames.isName_semantics (M := M) v 0 2).mp hs) ((ForcingNames.isName_semantics (M := M) v 0 3).mp hu))

theorem mapping_models {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (mappingSentence f t sigma tau name q x y output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hf h ht hs hu ho
  exact (orderedPairName_semantics (M := M) v q x y output).mpr
    (map_orderedPairName hM ((ForcingMapConditions.function_semantics (M := M) v f id).mp hf)
      ((orderedPairName_semantics (M := M) v t sigma tau name).mp h)
      ((ForcingMapConditions.rel_semantics (M := M) v f id t q).mp ht)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id sigma x).mp hs)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id tau y).mp hu)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id name output).mp ho))

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)
theorem uniqueness_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)
theorem name_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence nameSentence) :=
  ModelTransfer.derives (fun _ hM => name_models hM)
theorem mapping_kernel_certificate {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (mappingSentence f t sigma tau name q x y output)) :=
  ModelTransfer.derives (fun _ hM => mapping_models f t sigma tau name q x y output hM)

def hsSentence : Source.Sentence :=
  let rho : Fin 7 → Fin 17 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  ((ForcingProductFamily.presentation (0 : Fin 17) 7 8 9 10 1 2 3 4 5 6).imp
    ((ForcingLabelPermutations.carrier (7 : Fin 17) 11).imp
      ((ForcingNormalFilter.normal (7 : Fin 17) 11 12).imp
        ((ForcingWithTopCarrier.empty (13 : Fin 17)).imp
          ((ForcingHS.hs ForcingProductFamily.actionFormula rho 11 6 12 14).imp
            ((ForcingHS.hs ForcingProductFamily.actionFormula rho 11 6 12 15).imp
              ((orderedPairName (13 : Fin 17) 14 15 16).imp
                (ForcingHS.hs ForcingProductFamily.actionFormula rho 11 6 12 16)))))))).close

theorem hs_models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence hsSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF ht hs hu hn
  let rho : Fin 7 → Fin 17 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  apply (ForcingHS.hs_semantics (M := M) env ForcingProductFamily.actionFormula rho 11 6 12 16).mpr
  exact orderedPair_hs hM (fun i => env (rho i))
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env 13).mp ht)
    ((ForcingHS.hs_semantics (M := M) env ForcingProductFamily.actionFormula rho 11 6 12 14).mp hs)
    ((ForcingHS.hs_semantics (M := M) env ForcingProductFamily.actionFormula rho 11 6 12 15).mp hu)
    ((orderedPairName_semantics (M := M) env 13 14 15 16).mp hn)

theorem hs_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence hsSentence) :=
  ModelTransfer.derives (fun _ hM => hs_models hM)


end PPAC.Migration.ForcingOrderedPairName
