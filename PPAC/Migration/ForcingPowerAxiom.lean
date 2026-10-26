/- Pinned SymmetricSets.forces_powerSet, returned to the original native kernel.
All HS names are quantified; the bound is local to normalization of one name. -/
import PPAC.Migration.ForcingPowerName

namespace PPAC.Migration.ForcingPowerAxiom
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingClassEvaluation (Predicate)
open ForcingHS (HS)
open ForcingPowerName (Bound Subset SubsetF)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Supply a parameter slot for an arbitrary internal sigma, preserving the
same order relation, atomic recursion and HS domain. -/
theorem exists_at_value (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w sigma : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma) :
    ∃ bound name, Bound (env (rho 6)) sigma bound ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ∀ child p, PureKuratowski.PairMember M child p name ↔
        HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) child ∧
        Subset child bound ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
        SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p child sigma := by
  let ext : Fin (k+1) → M.Carrier .set := Fin.lastCases sigma env
  let ra := fun j => (rho j).castSucc
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let S := orderFormula (rho 0).castSucc mul.castSucc
  let J := domain ra G.castSucc F.castSucc
  have hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y := by
    intro x y
    simp only [R,S,ForcingProductSymmetry.orderFormula_semantics,ext,Fin.lastCases_castSucc]
  have hH : ∀ x, Predicate H env x ↔ Predicate J ext x := by
    intro x
    simp only [H,J,domain_semantics,ext,ra,Fin.lastCases_castSucc]
  have hpre' : PreorderOn S ext (env (rho 6)) := by
    refine ⟨fun p hp => (hR p p).mp (hpre.1 p hp),?_⟩
    intro p q r hp hq hr hpq hqr
    exact (hR p r).mp (hpre.2 p q r hp hq hr ((hR p q).mpr hpq) ((hR q r).mpr hqr))
  have hp' : Presentation (ext (ra 0)) I K B w (ext (ra 1)) (ext (ra 2))
      (ext (ra 3)) (ext (ra 4)) (ext (ra 5)) (ext (ra 6)) := by
    simpa only [ext,ra,Fin.lastCases_castSucc] using hp
  have hG' : ForcingLabelPermutations.Carrier I (ext G.castSucc) := by
    simpa only [ext,Fin.lastCases_castSucc] using hG
  have hF' : ForcingNormalFilter.Normal I (ext G.castSucc) (ext F.castSucc) := by
    simpa only [ext,Fin.lastCases_castSucc] using hF
  have hs' : HS actionFormula (fun j => ext (ra j)) (ext G.castSucc) (ext (ra 6)) (ext F.castSucc) (ext (Fin.last k)) := by
    simpa only [ext,ra,Fin.lastCases_last,Fin.lastCases_castSucc] using hs
  have hpre'' : PreorderOn (orderFormula (ra 0) mul.castSucc) ext (ext (ra 6)) := by
    simpa only [S,ext,ra,Fin.lastCases_castSucc] using hpre'
  obtain ⟨bound,name,hb,hn,he⟩ := ForcingPowerName.exists_power hM ext ra G.castSucc F.castSucc mul.castSucc (Fin.last k)
    hp' hG' hF' hpre'' hs'
  refine ⟨bound,name,?_,?_,?_⟩
  · simpa only [ext,ra,Fin.lastCases_last,Fin.lastCases_castSucc] using hb
  · simpa only [ext,ra,Fin.lastCases_castSucc] using hn
  · intro child p
    have he' : PureKuratowski.PairMember M child p name ↔
        HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) child ∧
        Subset child bound ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
        SubsetF S J ext (env (rho 6)) p child sigma := by
      simpa only [S,J,ext,ra,Fin.lastCases_last,Fin.lastCases_castSucc] using he child p
    rw [← ForcingPowerName.subset_relation_congr hR hH] at he'
    exact he'

theorem forces_powerSet (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.powerSet := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let P := env (rho 6)
  unfold Source.SetLanguage.powerSet
  apply (ForcingFormula.force_all hM hpre hcond _ _).mpr
  intro sigma hs
  have hs' := (domain_semantics env rho G F sigma).mp hs
  obtain ⟨bound,name,hb,hn,he⟩ := exists_at_value hM env rho G F mul hp hG hF hpre hs'
  apply (ForcingFormula.force_ex R H env _ P p _).mpr
  intro q hq _
  refine ⟨q,hq,hpre.1 q hq,name,(domain_semantics env rho G F name).mpr hn,?_⟩
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro nu hnu
  let vv : Fin 3 → M.Carrier .set := Fin.lastCases nu (Fin.lastCases name (Fin.lastCases sigma Fin.elim0))
  have hsub : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P →
      (Force R H env vv P r (Source.SetLanguage.subset 2 0) ↔ SubsetF R H env P r nu sigma) := by
    intro r hr
    simpa only [vv,show (2 : Fin 3) = Fin.last 2 from rfl,
      show (0 : Fin 3) = ((Fin.last 0).castSucc).castSucc from rfl,
      Fin.lastCases_last,Fin.lastCases_castSucc] using ForcingPowerName.forces_subset hM hpre hr vv 2 0
  have hmem : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P →
      (Forces false R env P nu name r ↔ SubsetF R H env P r nu sigma) := by
    intro r hr
    exact ForcingPowerName.mem_power hM env rho G F mul hp hG hF hpre hs'
      ((domain_semantics env rho G F nu).mp hnu) hb he hr
  simp only [Source.Formula.iff,ForcingFormula.force_conj,ForcingFormula.force_imp hM hpre hq,
    ForcingFormula.force_mem,show (2 : Fin 3) = Fin.last 2 from rfl,
    show (1 : Fin 3) = (Fin.last 1).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun r hr _ hm => (hsub r hr).mpr ((hmem r hr).mp hm),
    fun r hr _ hf => (hmem r hr).mpr ((hsub r hr).mp hf)⟩

/-- The original Power Set sentence in the actual HS interpretation, under
source algebra/presentation/normality premises, in the original native kernel. -/
def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp
            (ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.powerSet)))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hG hF hc
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.powerSet).mpr
  have hz : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hz]
  exact forces_powerSet hM env rho 11 12 13 hp' hG' hF' hpre hc

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingPowerAxiom
