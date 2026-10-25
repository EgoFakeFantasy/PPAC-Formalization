/- Source MulAction.stabilizer used by ForcingNames.pair_HS/union_HS.
The name action is the constructed ProductNames action, not an assumed group
operation on names. Reuse graph operations and all accepted name-action laws. -/
import PPAC.Migration.ForcingProductCovariance

namespace PPAC.Migration.ForcingProductStabilizer
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingStabilizer (Stabilizer)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem subgroup (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G sigma S : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hn : ForcingNames.IsName (v 6) sigma)
    (hS : Stabilizer actionFormula v G (v 6) sigma S) : ForcingConjugationGraph.Subgroup I G S := by
  refine ⟨fun g hg => ((hS g).mp hg).1, ?_, ?_, ?_⟩
  · obtain ⟨e, he, heId⟩ := ForcingLabelPermutations.identity_mem hM hG
    obtain ⟨a, ha⟩ := ForcingProductFamily.exists_action hM hp ((hG e).mp he)
    have haId := ForcingProductFamily.identity hM hp heId ha
    exact ⟨e, (hS e).mpr ⟨he, a, (mapRel_action v e a).mpr ha,
      ForcingConditionAction.name_identity hM (args2 (v 6) a) (0 : Fin 2) 1 haId sigma hn⟩, heId⟩
  · intro g hg
    obtain ⟨hgG, a, hga, hfixed⟩ := (hS g).mp hg
    have ha := (mapRel_action v g a).mp hga
    obtain ⟨i, hi, hgi⟩ := ForcingLabelPermutations.inverse_mem hM hG hgG
    obtain ⟨b, hb⟩ := ForcingProductFamily.exists_action hM hp ((hG i).mp hi)
    have hab := ForcingProductCovariance.inverse hM hp ((hG g).mp hgG) hgi ha hb
    exact ⟨i, (hS i).mpr ⟨hi, b, (mapRel_action v i b).mpr hb,
      ForcingNameConjugacy.inverse_action hM (ForcingProductFamily.action_permutation ha).1
        (ForcingProductFamily.action_permutation hb).1 hab hn hfixed⟩, hgi⟩
  · intro g h hg hh
    obtain ⟨hgG, a, hga, hgaFix⟩ := (hS g).mp hg
    obtain ⟨hhG, b, hhb, hhbFix⟩ := (hS h).mp hh
    have ha := (mapRel_action v g a).mp hga
    have hb := (mapRel_action v h b).mp hhb
    obtain ⟨t, ht, hght⟩ := ForcingLabelPermutations.composition_mem hM hG hgG hhG
    obtain ⟨c, hc⟩ := ForcingProductFamily.exists_action hM hp ((hG t).mp ht)
    have habc := ForcingProductFamily.multiplication hM hp ((hG h).mp hhG) hght ha hb hc
    exact ⟨t, (hS t).mpr ⟨ht, c, (mapRel_action v t c).mpr hc,
      ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation ha).1
        (ForcingProductFamily.action_permutation hb).1 habc hhbFix hgaFix⟩, hght⟩

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 14 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  ((ForcingProductFamily.presentation (0 : Fin 14) 7 8 9 10 1 2 3 4 5 6).imp
    ((ForcingLabelPermutations.carrier (7 : Fin 14) 11).imp
      ((ForcingNames.isName (6 : Fin 14) 12).imp
        ((ForcingStabilizer.stabilizer actionFormula rho 11 6 12 13).imp
          (ForcingConjugationGraph.subgroup (7 : Fin 14) 11 13))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hn hS
  let rho : Fin 7 → Fin 14 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  apply (ForcingConjugationGraph.subgroup_semantics (M := M) env 7 11 13).mpr
  exact subgroup hM (fun i => env (rho i))
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG)
    ((ForcingNames.isName_semantics (M := M) env 6 12).mp hn)
    ((ForcingStabilizer.stabilizer_semantics (M := M) env actionFormula rho 11 6 12 13).mp hS)

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingProductStabilizer
