/- Pinned ForcingNames.Name.pair_HS -> SymmetricSets.Name.pair.
The original stabilizer-intersection argument, using the actual ProductNames
family, existing normal filter, native intersection and literal pairName. -/
import PPAC.Migration.ForcingProductStabilizer
import PPAC.Migration.ForcingNormalFilter
import PPAC.Migration.ForcingPairName

namespace PPAC.Migration.ForcingProductHSPair
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingHS (HS)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem pair_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t sigma tau name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t)
    (hs : HS actionFormula v G (v 6) F sigma) (hu : HS actionFormula v G (v 6) F tau)
    (hn : ForcingPairName.PairName t sigma tau name) : HS actionFormula v G (v 6) F name := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  have hname := ForcingPairName.isName hM hn htW (ForcingHS.isName hs) (ForcingHS.isName hu)
  apply ForcingHS.intro_hs hM actionFormula v G (v 6) F name hname
  · obtain ⟨S, hS, hSF⟩ := ForcingHS.symmetric_of_hs hs
    obtain ⟨T, hT, hTF⟩ := ForcingHS.symmetric_of_hs hu
    obtain ⟨H, hH⟩ := SetTheory.KP.intersection_exists_d
      (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S T
    obtain ⟨U, hU⟩ := ForcingStabilizer.exists_stabilizer hM actionFormula v G (v 6) name
    refine ⟨U, hU, hF.2.1 H U (hF.2.2.1 S T H hSF hTF hH)
      (ForcingProductStabilizer.subgroup hM v hp hG hname hU) ?_⟩
    intro g hg
    obtain ⟨hgS, hgT⟩ := (hH g).mp hg
    obtain ⟨hgG, a, hga, haFix⟩ := (hS g).mp hgS
    obtain ⟨_, b, hgb, hbFix⟩ := (hT g).mp hgT
    have ha := (mapRel_action v g a).mp hga
    have hb := (mapRel_action v g b).mp hgb
    have hab := ForcingProductFamily.unique hM ha hb
    subst b
    have har := ForcingProductFamily.action_permutation ha
    have hf := ForcingConditionAction.act_function (args2 (v 6) a) (0 : Fin 2) 1 har.1
    have htop : ForcingConditionAction.Act (v 6) a t t :=
      Or.inl ⟨htW, ForcingProductFamily.top_fixed hp ht ha⟩
    obtain ⟨out, hout⟩ := ForcingNameConjugacy.exists_action hM har.1 name
    have houtPair := ForcingPairName.map_pairName hM hf hn
      ((ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 t t).mpr htop)
      haFix hbFix hout
    have heq := ForcingPairName.unique hM houtPair hn
    exact (hU g).mpr ⟨hgG, a, hga, heq ▸ hout⟩
  · intro child condition he
    rcases ((ForcingPairName.edge_pairName hM hn child condition).mp he).1 with he | he
    · exact he ▸ hs
    · exact he ▸ hu

/-- Use the already constructed support family; no new normality assumption. -/
theorem pair_of_filter (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w omega mu G F t sigma tau name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G)
    (hw : (Definitional.Project.FirstOrderSemantics.reduct M).IsOmega omega)
    (hmu : (Definitional.Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) omega mu)
    (hF : ForcingSupportFilter.Filter I G mu F) (ht : ForcingWithTopCarrier.Empty t)
    (hs : HS actionFormula v G (v 6) F sigma) (hu : HS actionFormula v G (v 6) F tau)
    (hn : ForcingPairName.PairName t sigma tau name) : HS actionFormula v G (v 6) F name :=
  pair_hs hM v hp hG (ForcingNormalFilter.is_normal hM hw hmu hG hF) ht hs hu hn

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 17 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  ((ForcingProductFamily.presentation (0 : Fin 17) 7 8 9 10 1 2 3 4 5 6).imp
    ((ForcingLabelPermutations.carrier (7 : Fin 17) 11).imp
      ((ForcingNormalFilter.normal (7 : Fin 17) 11 12).imp
        ((ForcingWithTopCarrier.empty (13 : Fin 17)).imp
          ((ForcingHS.hs actionFormula rho 11 6 12 14).imp
            ((ForcingHS.hs actionFormula rho 11 6 12 15).imp
              ((ForcingPairName.pairName (13 : Fin 17) 14 15 16).imp
                (ForcingHS.hs actionFormula rho 11 6 12 16)))))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF ht hs hu hn
  let rho : Fin 7 → Fin 17 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  apply (ForcingHS.hs_semantics (M := M) env actionFormula rho 11 6 12 16).mpr
  exact pair_hs hM (fun i => env (rho i))
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env 13).mp ht)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho 11 6 12 14).mp hs)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho 11 6 12 15).mp hu)
    ((ForcingPairName.pairName_semantics (M := M) env 13 14 15 16).mp hn)

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingProductHSPair
