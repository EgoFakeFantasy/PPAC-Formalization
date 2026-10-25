/- Pinned ForcingNames.ConditionAction.Name.check_HS.
Consumer: SymmetricSystem.Name.check in SymmetricSets.lean:108-110.
Use the already constructed checkName, its exact child equation and fixed
condition action. Membership induction comes from the existing native schema. -/
import PPAC.Migration.ForcingHS
import PPAC.Migration.ForcingCheckNameLaws

namespace PPAC.Migration.ForcingHSCheck
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingHS (HS hs)
open ForcingCheckName (Checked checkName)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def atSet {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m)
    (G P F t x : Fin m) : Formula m :=
  .all ((checkName t.castSucc x.castSucc (Fin.last m)).imp
    (hs A (paramsUp rho) G.castSucc P.castSucc F.castSucc (Fin.last m)))

theorem atSet_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P F t x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (atSet A rho G P F t x) ↔
      ∀ name, Checked (env t) (env x) name → HS A (fun i => env (rho i)) (env G) (env P) (env F) name := by
  simp only [atSet,Formula.Realize,ForcingCheckName.checkName_semantics (M := M),ForcingHS.hs_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem check_hs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F t : M.Carrier .set)
    (htop : (Definitional.Project.FirstOrderSemantics.reduct M).mem G F)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (hAction : ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G →
      ∃ r, MapRel A params g r ∧ ForcingConditionGraphs.Endomap P r ∧ ForcingConditionAction.Act P r t t) :
    ∀ x name, Checked t x name → HS A params G P F name := by
  let inputs : Fin (k+4) → M.Carrier .set := Fin.lastCases t (Fin.lastCases F (Fin.lastCases P (Fin.lastCases G params)))
  let matrix := atSet A (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
    (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hm : ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x inputs) matrix ↔
      ∀ name, Checked t x name → HS A params G P F name := by
    intro x
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      atSet_semantics (M := M) (Fin.lastCases x inputs) A (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
        (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hall := ForcingCheckName.formula_induction hM matrix inputs (by
    intro x ih
    apply (hm x).mpr
    intro name hn
    apply ForcingHS.intro_hs hM A params G P F name (ForcingCheckNameLaws.isName hM ht x name hn)
    · refine ⟨G,?_,htop⟩
      intro g
      constructor
      · intro hg
        obtain ⟨r,hgr,hr,hfixed⟩ := hAction g hg
        have hf := ForcingConditionAction.act_function (args2 P r) (0 : Fin 2) 1 hr
        obtain ⟨output,ho⟩ := ForcingMapConditions.exists_mapping hM
          (ForcingConditionAction.actFormula (0 : Fin 2) 1) (args2 P r) hf name
        have he := ForcingCheckNameLaws.action_fixed hM (args2 P r) (0 : Fin 2) 1 hr hfixed hn ho
        exact ⟨hg,r,hgr,he ▸ ho⟩
      · exact fun h => h.1
    · intro tau condition he
      obtain ⟨y,hy,hchecked,_⟩ := (ForcingCheckName.edge_checkName hM hn tau condition).mp he
      exact (hm y).mp (ih y hy) tau hchecked)
  intro x
  exact (hm x).mp (hall x)

def fixedFamily {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P t : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) G.castSucc).imp (.ex
    ((ReplacementPredicates.rel A (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).conj
      ((ForcingConditionGraphs.endomap P.castSucc.castSucc (Fin.last (m+1))).conj
        (ForcingConditionAction.act P.castSucc.castSucc (Fin.last (m+1)) t.castSucc.castSucc t.castSucc.castSucc)))))

theorem fixedFamily_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fixedFamily A rho G P t) ↔
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g (env G) →
        ∃ r, MapRel A (fun i => env (rho i)) g r ∧ ForcingConditionGraphs.Endomap (env P) r ∧
          ForcingConditionAction.Act (env P) r (env t) (env t) := by
  simp only [fixedFamily,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingConditionGraphs.endomap_semantics (M := M),ForcingConditionAction.act_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {k : Nat} (A : Formula (k+2)) (G P F t x name : Fin k) : Source.Sentence :=
  ((Formula.mem G F).imp ((Formula.mem t P).imp ((fixedFamily A id G P t).imp
    ((checkName t x name).imp (hs A id G P F name))))).close

theorem models {k : Nat} (A : Formula (k+2)) (G P F t x name : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence A G P F t x name)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env htop ht ha hn
  exact (ForcingHS.hs_semantics (M := M) env A id G P F name).mpr
    (check_hs hM A env (env G) (env P) (env F) (env t) htop ht
      ((fixedFamily_semantics (M := M) env A id G P t).mp ha) (env x) (env name)
      ((ForcingCheckName.checkName_semantics (M := M) env t x name).mp hn))

theorem kernel_certificate {k : Nat} (A : Formula (k+2)) (G P F t x name : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence A G P F t x name)) :=
  ModelTransfer.derives (fun _ hM => models A G P F t x name hM)

end PPAC.Migration.ForcingHSCheck
