/- Pinned ForcingNames.Name.union_HS -> SymmetricSets.Name.union.
Reuse the literal union name and its shared condition-map proof. The actual
ProductNames order is needed only on conditions occurring in IsName entries. -/
import PPAC.Migration.ForcingProductStabilizer
import PPAC.Migration.ForcingNormalFilter
import PPAC.Migration.ForcingUnionAction
import PPAC.Migration.ForcingProductSymmetry

namespace PPAC.Migration.ForcingProductHSUnion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingHS (HS)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem union_hs (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (mul : Fin n)
    {I K B w G F sigma name : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hs : HS actionFormula (fun j => env (rho j)) G (env (rho 6)) F sigma)
    (hn : ForcingUnionName.UnionName (orderFormula (rho 0) mul) env (env (rho 6)) sigma name) :
    HS actionFormula (fun j => env (rho j)) G (env (rho 6)) F name := by
  let v := fun j => env (rho j)
  have hsName := ForcingHS.isName hs
  have hname := ForcingUnionName.isName hM hn hsName
  apply ForcingHS.intro_hs hM actionFormula v G (v 6) F name hname
  · obtain ⟨S, hS, hSF⟩ := ForcingHS.symmetric_of_hs hs
    obtain ⟨U, hU⟩ := ForcingStabilizer.exists_stabilizer hM actionFormula v G (v 6) name
    refine ⟨U, hU, hF.2.1 S U hSF (ForcingProductStabilizer.subgroup hM v hp hG hname hU) ?_⟩
    intro g hg
    obtain ⟨hgG, a, hga, haFix⟩ := (hS g).mp hg
    have ha := (mapRel_action v g a).mp hga
    have har := ForcingProductFamily.action_permutation ha
    have hf := ForcingConditionAction.act_function (args2 (v 6) a) (0 : Fin 2) 1 har.1
    have horder := ForcingProductFamily.order hM (env mul) hp ((hG g).mp hgG) ha
    obtain ⟨out, hout⟩ := ForcingNameConjugacy.exists_action hM har.1 name
    have houtUnion : ForcingUnionName.UnionName (orderFormula (rho 0) mul) env (v 6) sigma out := by
      apply ForcingUnionAction.map_unionName_restricted hM hf (v 6)
        (fun x => (Definitional.Project.FirstOrderSemantics.reduct M).mem x (v 6))
        (fun _ hx => hx) ?_ ?_ ?_ hn haFix hout ?_
      · intro x y hx hxy
        exact ForcingConditionAction.act_into har.1 hx
          ((ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 x y).mp hxy)
      · intro y hy
        obtain ⟨x, hx, hxy⟩ := har.2.2 y hy
        exact ⟨x, hx, (ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 x y).mpr
          (Or.inl ⟨hx, hxy⟩)⟩
      · intro x y x' y' hx hy hxx hyy
        rw [orderFormula_semantics, orderFormula_semantics]
        exact (horder x y x' y'
          ((ForcingConditionAction.act_inside hx).mp
            ((ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 x x').mp hxx))
          ((ForcingConditionAction.act_inside hy).mp
            ((ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 y y').mp hyy))).symm
      · intro chi p child r hpEdge hrEdge
        have hc := ForcingNames.child_condition hsName hpEdge
        exact ⟨hc.1, (ForcingNames.child_condition hc.2 hrEdge).1⟩
    have heq := ForcingUnionName.unique hM houtUnion hn
    exact (hU g).mpr ⟨hgG, a, hga, heq ▸ hout⟩
  · intro child q he
    obtain ⟨chi, p, r, hpEdge, hrEdge, _, _, _⟩ := (ForcingUnionName.edge_unionName hM hn child q).mp he
    exact ForcingHS.child (ForcingHS.child hs hpEdge) hrEdge

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
    ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
      ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
        ((ForcingHS.hs actionFormula rho 11 6 12 14).imp
          ((ForcingUnionName.unionName (orderFormula (0 : Fin 16) 13) id 6 14 15).imp
            (ForcingHS.hs actionFormula rho 11 6 12 15)))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hs hn
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  apply (ForcingHS.hs_semantics (M := M) env actionFormula rho 11 6 12 15).mpr
  exact union_hs hM env rho 13
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho 11 6 12 14).mp hs)
    ((ForcingUnionName.unionName_semantics (M := M) env (orderFormula (0 : Fin 16) 13) id 6 14 15).mp hn)

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingProductHSUnion
