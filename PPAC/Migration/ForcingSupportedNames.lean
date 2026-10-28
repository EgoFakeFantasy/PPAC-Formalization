/- Pinned OrbitNames.smul_name_eq_of_diagram_eq:238 and
LocalQuotients.supported_mono:122. Consumers: active_equal_independent and
support_descent. Reuse actual Product action, native inverse/composition graphs,
and literal name inverse/composition/injectivity. No name-orbit quotient. -/
import PPAC.Migration.ForcingEquivariantMix
import PPAC.Migration.ConstructionPlacementPasting

namespace PPAC.Migration.ForcingSupportedNames
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingLabelPermutations (Carrier Fixing)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingStabilizer (Action)
open ReplacementPredicates (paramsUp rel)
open ConstructionPlacementPasting (AgreesOn)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Supported (v : Fin 7 → M.Carrier .set) (H sigma : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g H → ∀ A,
    MapRel actionFormula v g A → Action (v 6) A sigma sigma

theorem supported_semantics {n : Nat} (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n)
    (H sigma : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (ForcingEquivariantMix.fixedAll rho H sigma) ↔
        Supported (fun j => env (rho j)) (env H) (env sigma) :=
  ForcingEquivariantMix.fixedAll_semantics env rho H sigma

theorem supported_mono {v : Fin 7 → M.Carrier .set} {G J K HJ HK sigma : M.Carrier .set}
    (hJ : Fixing G J HJ) (hK : Fixing G K HK)
    (hJK : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x K)
    (hs : Supported v HJ sigma) : Supported v HK sigma := by
  intro g hg A hA
  obtain ⟨hgG,hfix⟩ := (hK g).mp hg
  exact hs g ((hJ g).mpr ⟨hgG,fun x hx => hfix x (hJK x hx)⟩) A hA

/-- Source-language adapter of the existing exact AgreesOn graph contract. -/
def agrees {n : Nat} (J pi rho : Fin n) : Formula n :=
  .all (.all ((Formula.mem (Fin.last n).castSucc J.castSucc.castSucc).imp
    ((Source.SetLanguage.edge rho.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))).imp
      (Source.SetLanguage.edge pi.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))))))

theorem agrees_semantics {n : Nat} (env : Fin n → M.Carrier .set) (J pi rho : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (agrees J pi rho) ↔
      AgreesOn (env J) (env pi) (env rho) := by
  simp only [agrees,AgreesOn,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem name_eq_of_agree (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G J H sigma pi rho A Bact x y : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : Carrier I G) (hH : Fixing G J H)
    (hJI : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z I)
    (hn : ForcingNames.IsName (v 6) sigma) (hsup : Supported v H sigma)
    (hpi : Permutation I pi) (hrho : Permutation I rho) (hAgree : AgreesOn J pi rho)
    (hA : MapRel actionFormula v pi A) (hB : MapRel actionFormula v rho Bact)
    (hx : Action (v 6) A sigma x) (hy : Action (v 6) Bact sigma y) : x = y := by
  obtain ⟨inv,hi,hri⟩ := ForcingConditionGraphs.exists_inverse hM hrho
  obtain ⟨delta,hd,hcomp⟩ := ForcingConditionGraphs.exists_composition hM hi hpi
  have hfix : ForcingLabelPermutations.Fixes J delta := by
    intro z hz
    obtain ⟨a,hza,_⟩ := hrho.1.1.2 z (hJI z hz)
    exact (hcomp z z).mpr ⟨hJI z hz,a,hAgree z a hz hza,(hri z a).mp hza⟩
  have hdH := (hH delta).mpr ⟨(hG delta).mpr hd,hfix⟩
  obtain ⟨C,hC⟩ := ForcingProductFamily.exists_action hM hp hi
  obtain ⟨D,hD⟩ := ForcingProductFamily.exists_action hM hp hd
  have ha := (mapRel_action v pi A).mp hA
  have hb := (mapRel_action v rho Bact).mp hB
  have hpa := ForcingProductFamily.action_permutation ha
  have hpb := ForcingProductFamily.action_permutation hb
  have hpc := ForcingProductFamily.action_permutation hC
  have hpd := ForcingProductFamily.action_permutation hD
  have hBC := ForcingProductCovariance.inverse hM hp hrho hri hb hC
  have hCA := ForcingProductFamily.multiplication hM hp hpi hcomp hC ha hD
  have hDfix := hsup delta hdH D ((mapRel_action v delta D).mpr hD)
  obtain ⟨back,hback⟩ := ForcingNameConjugacy.exists_action hM hpc.1 x
  have hDb := ForcingNameConjugacy.composition hM hpc.1 hpa.1 hCA hx hback
  have hbs := ForcingNameConjugacy.unique hM hpd.1 hDb hDfix
  have hxBack : Action (v 6) C x sigma := hbs ▸ hback
  have hyBack := ForcingNameConjugacy.inverse_action hM hpb.1 hpc.1 hBC hn hy
  exact ForcingNameConjugacy.injective hM hpc
    (ForcingNameConjugacy.name_preservation hM hpa.1 hn hx)
    (ForcingNameConjugacy.name_preservation hM hpb.1 hn hy) hxBack hyBack

/-- Exact range equation of the supplied internal diagram; no range constructor. -/
def Range (D p J : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z J ↔
    ∃ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t D ∧ PureKuratowski.PairMember M t z p

def range {n : Nat} (D p J : Fin n) : Formula n :=
  .all ((Formula.mem (Fin.last n) J.castSucc).iff
    (.ex ((Formula.mem (Fin.last (n+1)) D.castSucc.castSucc).conj
      (Source.SetLanguage.edge p.castSucc.castSucc (Fin.last (n+1)) (Fin.last n).castSucc))))

theorem range_semantics {n : Nat} (env : Fin n → M.Carrier .set) (D p J : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (range D p J) ↔
      Range (env D) (env p) (env J) := by
  simp only [range,Range,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

theorem agree_of_same_diagram {D I p J pi rho q : M.Carrier .set}
    (hp : ForcingSupportSize.Injection D I p) (hJ : Range D p J)
    (hP : CompositionGraph D pi p q) (hR : CompositionGraph D rho p q) : AgreesOn J pi rho := by
  intro z a hz hza
  obtain ⟨t,ht,htz⟩ := (hJ z).mp hz
  have hta := (hR t a).mpr ⟨ht,z,htz,hza⟩
  obtain ⟨_,b,htb,hba⟩ := (hP t a).mp hta
  have he := ForcingConditionGraphs.function_unique hp.1.1 htb htz
  exact he ▸ hba

theorem name_eq_of_same_diagram (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G p J H sigma pi rho q A Bact x y : M.Carrier .set}
    (hpres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : Carrier I G) (hH : Fixing G J H)
    (hp : ForcingSupportSize.Injection (v 0) I p) (hJ : Range (v 0) p J)
    (hn : ForcingNames.IsName (v 6) sigma) (hsup : Supported v H sigma)
    (hpi : Permutation I pi) (hrho : Permutation I rho)
    (hP : CompositionGraph (v 0) pi p q) (hR : CompositionGraph (v 0) rho p q)
    (hA : MapRel actionFormula v pi A) (hB : MapRel actionFormula v rho Bact)
    (hx : Action (v 6) A sigma x) (hy : Action (v 6) Bact sigma y) : x = y := by
  have hJI (z : M.Carrier .set) (hz : (Definitional.Project.FirstOrderSemantics.reduct M).mem z J) : (Definitional.Project.FirstOrderSemantics.reduct M).mem z I := by
    obtain ⟨t,_,htz⟩ := (hJ z).mp hz
    exact hp.1.2 t z htz
  exact name_eq_of_agree hM v hpres hG hH hJI hn hsup hpi hrho
    (agree_of_same_diagram hp hJ hP hR) hA hB hx hy

def sentence {n : Nat} (v : Fin 7 → Fin n) (I K B w G p J H sigma pi rho q A Bact x y : Fin n) : Source.Sentence :=
  ((ForcingProductFamily.presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingLabelPermutations.fixing G J H).imp
      ((Source.SetLanguage.injection p (v 0) I).imp ((range (v 0) p J).imp
        ((ForcingNames.isName (v 6) sigma).imp ((ForcingEquivariantMix.fixedAll v H sigma).imp
          ((ForcingConditionGraphs.permutation I pi).imp ((ForcingConditionGraphs.permutation I rho).imp
            ((ForcingConditionGraphs.compositionGraph (v 0) pi p q).imp
              ((ForcingConditionGraphs.compositionGraph (v 0) rho p q).imp
                ((rel actionFormula v pi A).imp ((rel actionFormula v rho Bact).imp
                  ((ForcingStabilizer.action (v 6) A sigma x).imp
                    ((ForcingStabilizer.action (v 6) Bact sigma y).imp (.equal x y)))))))))))))))).close

theorem models {n : Nat} (v : Fin 7 → Fin n) (I K B w G p J H sigma pi rho q A Bact x y : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence v I K B w G p J H sigma pi rho q A Bact x y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hH hdiag hJ hn hsup hpi hrho hP hR hA hB hx hy
  exact name_eq_of_same_diagram hM (fun j => env (v j))
    ((ForcingProductFamily.presentation_semantics (M := M) env (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G J H).mp hH)
    ((ForcingSupportSize.injection_semantics (M := M) env p (v 0) I).mp hdiag)
    ((range_semantics (M := M) env (v 0) p J).mp hJ)
    ((ForcingNames.isName_semantics (M := M) env (v 6) sigma).mp hn)
    ((supported_semantics (M := M) env v H sigma).mp hsup)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env I pi).mp hpi)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env I rho).mp hrho)
    ((ForcingConditionGraphs.compositionGraph_semantics (M := M) env (v 0) pi p q).mp hP)
    ((ForcingConditionGraphs.compositionGraph_semantics (M := M) env (v 0) rho p q).mp hR)
    ((ForcingMapConditions.rel_semantics (M := M) env actionFormula v pi A).mp hA)
    ((ForcingMapConditions.rel_semantics (M := M) env actionFormula v rho Bact).mp hB)
    ((ForcingStabilizer.action_semantics (M := M) env (v 6) A sigma x).mp hx)
    ((ForcingStabilizer.action_semantics (M := M) env (v 6) Bact sigma y).mp hy)

theorem kernel_certificate {n : Nat} (v : Fin 7 → Fin n) (I K B w G p J H sigma pi rho q A Bact x y : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence v I K B w G p J H sigma pi rho q A Bact x y)) :=
  ModelTransfer.derives (fun _ hM => models v I K B w G p J H sigma pi rho q A Bact x y hM)

end PPAC.Migration.ForcingSupportedNames
