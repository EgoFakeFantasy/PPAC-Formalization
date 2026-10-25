/- Pinned SymmetricNames.forces_symmetry for ProductNames.actionHom.
The actual uniform action and support-defined filter discharge both HS-domain
contexts. No order-preservation or HS-closure assumption remains in the native
sentence; concrete monoid/conical partial-order assembly is a separate consumer. -/
import PPAC.Migration.ForcingProductCovariance

namespace PPAC.Migration.ForcingProductSymmetry
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingProductCovariance (SystemData systemData systemData_semantics)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reindex the existing seven-parameter action into the actual forcing environment. -/
def actionFormula {k : Nat} (rho : Fin 7 → Fin k) : Formula (k+2) :=
  ForcingProductFamily.action (rho 0).castSucc.castSucc (rho 1).castSucc.castSucc
    (rho 2).castSucc.castSucc (rho 3).castSucc.castSucc (rho 4).castSucc.castSucc
    (rho 5).castSucc.castSucc (rho 6).castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))

theorem actionFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (pi a : M.Carrier .set) :
    MapRel (actionFormula rho) env pi a ↔
      MapRel ForcingProductFamily.actionFormula (fun j => env (rho j)) pi a := by
  rw [ForcingProductFamily.mapRel_action]
  unfold MapRel actionFormula
  rw [ForcingProductFamily.action_semantics]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

theorem context_reindex {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    {G F c r i : M.Carrier .set}
    (h : ForcingStabilizerTransport.Context ForcingProductFamily.actionFormula
      (fun j => env (rho j)) G (env (rho 6)) F c r i) :
    ForcingStabilizerTransport.Context (actionFormula rho) env G (env (rho 6)) F c r i := by
  obtain ⟨⟨ht, hp⟩, hc, hr, hi, hri, hcov, hF⟩ := h
  refine ⟨⟨?_, ?_⟩, hc, hr, hi, hri, ?_, hF⟩
  · intro g hg
    obtain ⟨a, ha⟩ := ht g hg
    exact ⟨a, (actionFormula_semantics env rho g a).mpr ha⟩
  · intro g a hg ha
    exact hp g a hg ((actionFormula_semantics env rho g a).mp ha)
  · intro g h s t hg hh hgh hgs hht
    exact hcov g h s t hg hh hgh ((actionFormula_semantics env rho g s).mp hgs)
      ((actionFormula_semantics env rho h t).mp hht)

def orderFormula {k : Nat} (D mul : Fin k) : Formula (k+2) :=
  ForcingWithTopAction.le D.castSucc.castSucc mul.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))

theorem orderFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (D mul : Fin k)
    (p q : M.Carrier .set) : MapRel (orderFormula D mul) env p q ↔
      ForcingWithTopAction.Le (env D) (env mul) p q := by
  unfold MapRel orderFormula
  rw [ForcingWithTopAction.le_semantics]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Construct the reverse conjugation graph; the forward action data are reused. -/
theorem reverse_context (hM : FirstOrder.Theory.Models M nativeZF) {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c r i : M.Carrier .set}
    (h : SystemData v I K B w G F mu pi inv c r i) :
    ∃ d, ForcingStabilizerTransport.Context ForcingProductFamily.actionFormula v G (v 6) F d i r := by
  obtain ⟨hp, hG, hpi, hinv, hpii, _, _, hA, hB, hF⟩ := h
  have hir : InverseGraph inv pi := fun x y => (hpii y x).symm
  obtain ⟨d, hd, hdg⟩ := ForcingConjugationGraph.exists_graph hM hG hinv hpi hir
  exact ⟨d, ForcingProductCovariance.context hM v hp hG hinv hpi hir hd hdg hB hA hF⟩

theorem domain_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F r i : Fin k)
    {I K B w mu pi inv c : M.Carrier .set}
    (h : SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c (env r) (env i)) :
    ForcingFormulaSymmetry.DomainTransport (ForcingConditionAction.actFormula (rho 6) r)
      (ForcingHS.predicate (actionFormula rho) G (rho 6) F) env := by
  have hf := context_reindex env rho (ForcingProductCovariance.context_of_data hM h)
  obtain ⟨d, hb⟩ := reverse_context hM h
  exact ForcingHSAction.domain_transport_graphs hM (actionFormula rho) env G (rho 6) F r i c d
    hf (context_reindex env rho hb)

theorem order_on (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul r : Fin k)
    {I K B w G F mu pi inv c i : M.Carrier .set}
    (h : SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env r) i) :
    ForcingAtomicSymmetry.OrderOn (orderFormula (rho 0) mul) env (env (rho 6)) (env r) := by
  obtain ⟨hp, _, hpi, _, _, _, _, hA, _, _⟩ := h
  have ho := ForcingProductFamily.order hM (env mul) hp hpi hA
  intro x y a b hx hy hxa hyb
  rw [orderFormula_semantics, orderFormula_semantics]
  exact (ho x y a b ((ForcingConditionAction.act_inside hx).mp hxa)
    ((ForcingConditionAction.act_inside hy).mp hyb)).symm

/-- The source formula remains arbitrary; quantifiers range over the actual all-rank HS predicate. -/
def sentence {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c r i mul p p' : Fin k)
    (v v' : Fin n → Fin k) (phi : Formula n) : Source.Sentence :=
  ((systemData rho I K B w G F mu pi inv c r i).imp
    (ForcingFormulaSymmetry.conclusion (ForcingConditionAction.actFormula (rho 6) r)
      (orderFormula (rho 0) mul) (ForcingHS.predicate (actionFormula rho) G (rho 6) F)
      v v' (rho 6) p p' phi)).close

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c r i mul p p' : Fin k)
    (v v' : Fin n → Fin k) (phi : Formula n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence rho I K B w G F mu pi inv c r i mul p p' v v' phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h
  have hdata := (systemData_semantics env rho I K B w G F mu pi inv c r i).mp h
  have hc := ForcingProductCovariance.context_of_data hM hdata
  exact ForcingFormulaSymmetry.conclusion_models hM (ForcingConditionAction.actFormula (rho 6) r)
    (orderFormula (rho 0) mul) (ForcingHS.predicate (actionFormula rho) G (rho 6) F)
    v v' (rho 6) p p' phi env
    (ForcingAtomicSymmetry.action_transport (orderFormula (rho 0) mul) env (rho 6) r hc.2.2.1
      (order_on hM env rho mul r hdata))
    (domain_transport hM env rho G F r i hdata)

theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c r i mul p p' : Fin k)
    (v v' : Fin n → Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence rho I K B w G F mu pi inv c r i mul p p' v v' phi)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mu pi inv c r i mul p p' v v' phi hM)

end PPAC.Migration.ForcingProductSymmetry
