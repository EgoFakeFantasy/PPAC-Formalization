/- Fixed TailGraphs.ProductEntries/productEntry. Build the internal Cartesian
index set and actual ordered-pair-name function; reuse native functional image
and set-function construction, then discharge the existing collector FamilyHS. -/
import PPAC.Migration.ForcingOrderedPairName
import PPAC.Migration.ForcingCollectedHS
import PPAC.Migration.ForcingSupportSize

namespace PPAC.Migration.ForcingProductEntries
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open SetTheory.Definitional
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingOrderedPairName (OrderedPairName)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (t i output : M.Carrier .set) : Prop :=
  ∃ a b x p y q, PureKuratowski.Code M i a b ∧ PureKuratowski.Code M a x p ∧
    PureKuratowski.Code M b y q ∧ OrderedPairName t x y output

def value {n : Nat} (t i output : Fin n) : Formula n :=
  .ex (.ex (.ex (.ex (.ex (.ex ((PairSyntax.ordered i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc.castSucc.castSucc (Fin.last (n+3)).castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (n+4)).castSucc (Fin.last (n+5))).conj
    (ForcingOrderedPairName.orderedPairName t.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc.castSucc.castSucc (Fin.last (n+4)).castSucc output.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)))))))))

theorem value_semantics {n : Nat} (v : Fin n → M.Carrier .set) (t i output : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (value t i output) ↔
      Value (v t) (v i) (v output) := by
  simp only [value,Value,Formula.Realize,KuratowskiZF.source_code,
    ForcingOrderedPairName.orderedPairName_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {t i v w : M.Carrier .set} (hv : Value t i v) (hw : Value t i w) : v = w := by
  obtain ⟨a,b,x,p,y,q,hi,ha,hb,hv⟩ := hv
  obtain ⟨a',b',x',p',y',q',hi',ha',hb',hw⟩ := hw
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hi hi'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ha ha'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hb hb'
  exact ForcingOrderedPairName.unique hM hv hw

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    {P t X Y J i : M.Carrier .set} (hX : ForcingNames.IsName P X) (hY : ForcingNames.IsName P Y)
    (hJ : ForcingCohenCoordinates.Cartesian X Y J)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) : ∃ v, Value t i v := by
  obtain ⟨a,ha,b,hb,hi⟩ := (hJ i).mp hi
  obtain ⟨x,p,hxp,_,_⟩ := ForcingNames.edges hX a ha
  obtain ⟨y,q,hyq,_,_⟩ := ForcingNames.edges hY b hb
  obtain ⟨v,hv⟩ := ForcingOrderedPairName.exists_orderedPairName hM t x y
  exact ⟨v,a,b,x,p,y,q,hi,hxp,hyq,hv⟩

def Graph (t J f : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn J f ∧ ∀ i v,
    PureKuratowski.PairMember M i v f ↔ (Project.FirstOrderSemantics.reduct M).mem i J ∧ Value t i v

def graph {n : Nat} (t J f : Fin n) : Formula n :=
  (Source.SetLanguage.functionOn f J).conj (.all (.all
    ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))).iff
    ((Formula.mem (Fin.last n).castSucc J.castSucc.castSucc).conj
    (value t.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))))))

theorem graph_semantics {n : Nat} (v : Fin n → M.Carrier .set) (t J f : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (graph t J f) ↔ Graph (v t) (v J) (v f) := by
  simp only [graph,Graph,Source.Formula.iff,Formula.Realize,
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,
    value_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun v =>
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {P t X Y : M.Carrier .set}
    (hX : ForcingNames.IsName P X) (hY : ForcingNames.IsName P Y) :
    ∃ J f, ForcingCohenCoordinates.Cartesian X Y J ∧ Graph t J f := by
  obtain ⟨J,hJ⟩ := ForcingCohenCoordinates.exists_cartesian hM X Y
  let schema : Project.BinarySchema 1 :=
    { body := ProjectSyntax.encode id (value (2 : Fin 3) 1 0), freeClosed := ProjectSyntax.freeClosed .. }
  let e : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => t, free := fun _ => t }
  have he i v : schema.denote e i v ↔ Value t i v := by
    exact (GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM) (value (2 : Fin 3) 1 0) id ((e.push i).push v)).trans
      (value_semantics (M := M) ((e.push i).push v).bound 2 1 0)
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∃ v, schema.denote e i v := by
    intro i hi
    obtain ⟨v,hv⟩ := exists_value hM hX hY hJ hi
    exact ⟨v,(he i v).mpr hv⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ v w,
      schema.denote e i v → schema.denote e i w → v = w :=
    fun _ _ _ _ hv hw => value_unique hM ((he _ _).mp hv) ((he _ _).mp hw)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema e J ht hu
  obtain ⟨f,hf,hg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM) schema e ht hu
    (fun i v hi hv => (hA v).mpr ⟨i,hi,hv⟩)
  exact ⟨J,f,hJ,((ForcingSupportSize.native_mapsTo hM J A f).mpr hf).1,
    fun i v => (hg i v).trans (and_congr_right fun _ => he i v)⟩

theorem family_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t X Y J f : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t)
    (hX : ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F X)
    (hY : ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F Y)
    (hJ : ForcingCohenCoordinates.Cartesian X Y J) (hf : Graph t J f) :
    ForcingCollectedHS.FamilyHS v G (v 6) F J f := by
  intro i output hi hout
  obtain ⟨a,ha,b,hb,hcode⟩ := (hJ i).mp hi
  obtain ⟨_,a',b',x,p,y,q,hcode',hx,hy,hn⟩ := (hf.2 i output).mp hout
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact ForcingOrderedPairName.orderedPair_hs hM v hp hG hF ht
    (ForcingHS.child hX ⟨a,hx,ha⟩) (ForcingHS.child hY ⟨b,hy,hb⟩) hn

def constructionSentence : Source.Sentence :=
  ((ForcingNames.isName (0 : Fin 4) 2).imp ((ForcingNames.isName (0 : Fin 4) 3).imp
    (.ex (.ex ((ForcingCohenCoordinates.cartesian (2 : Fin 6) 3 4).conj (graph 1 4 5)))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hX hY
  obtain ⟨J,f,hJ,hf⟩ := construct (t := v 1) hM
    ((ForcingNames.isName_semantics (M := M) v 0 2).mp hX)
    ((ForcingNames.isName_semantics (M := M) v 0 3).mp hY)
  let env : Fin 6 → M.Carrier .set := Fin.lastCases f (Fin.lastCases J v)
  refine ⟨J,f,?_,?_⟩
  · exact (ForcingCohenCoordinates.cartesian_semantics (M := M) env 2 3 4).mpr hJ
  · exact (graph_semantics (M := M) env 1 4 5).mpr hf

theorem construction_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

def hsSentence : Source.Sentence :=
  let rho : Fin 7 → Fin 18 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  ((ForcingProductFamily.presentation (0 : Fin 18) 7 8 9 10 1 2 3 4 5 6).imp
    ((ForcingLabelPermutations.carrier (7 : Fin 18) 11).imp
      ((ForcingNormalFilter.normal (7 : Fin 18) 11 12).imp
        ((ForcingWithTopCarrier.empty (13 : Fin 18)).imp
          ((ForcingHS.hs ForcingProductFamily.actionFormula rho 11 6 12 14).imp
            ((ForcingHS.hs ForcingProductFamily.actionFormula rho 11 6 12 15).imp
              ((ForcingCohenCoordinates.cartesian (14 : Fin 18) 15 16).imp
                ((graph (13 : Fin 18) 16 17).imp (ForcingCollectedHS.familyHS rho 11 6 12 16 17))))))))).close

theorem hs_models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence hsSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF ht hs hu hJ hf
  let rho : Fin 7 → Fin 18 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  apply (ForcingCollectedHS.familyHS_semantics (M := M) env rho 11 6 12 16 17).mpr
  exact family_hs hM (fun i => env (rho i))
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env 13).mp ht)
    ((ForcingHS.hs_semantics (M := M) env ForcingProductFamily.actionFormula rho 11 6 12 14).mp hs)
    ((ForcingHS.hs_semantics (M := M) env ForcingProductFamily.actionFormula rho 11 6 12 15).mp hu)
    ((ForcingCohenCoordinates.cartesian_semantics (M := M) env 14 15 16).mp hJ)
    ((graph_semantics (M := M) env 13 16 17).mp hf)

theorem hs_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence hsSentence) :=
  ModelTransfer.derives (fun _ hM => hs_models hM)



end PPAC.Migration.ForcingProductEntries
