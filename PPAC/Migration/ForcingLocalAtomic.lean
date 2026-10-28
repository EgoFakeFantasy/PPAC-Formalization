/- Pinned LocalQuotients.localAtomic:447 / localSetoid:459 and
ForcingQuotient.AtomicData.eqG_refl/symm/trans. Conditions are actual Cohen
conditions; their filter is upward closed for the forcing order. -/
import PPAC.Migration.ForcingLocalNameDescent

namespace PPAC.Migration.ForcingLocalAtomic
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingPowerName (Subset)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingSupportingRoot (Code code_mem exists_code code_le)
open ForcingAtomicRelations (Forces)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source GenericFilter = order ideal of the opposite forcing order.
No dense-set meeting assumption is needed for the local quotient laws. -/
def CohenFilter (X g : M.Carrier .set) : Prop :=
  Subset g X ∧ (∃ d, (Project.FirstOrderSemantics.reduct M).mem d g) ∧
    (∀ d q, (Project.FirstOrderSemantics.reduct M).mem d g →
      (Project.FirstOrderSemantics.reduct M).mem q X → Subset q d →
        (Project.FirstOrderSemantics.reduct M).mem q g) ∧
    ∀ d e, (Project.FirstOrderSemantics.reduct M).mem d g →
      (Project.FirstOrderSemantics.reduct M).mem e g →
        ∃ f, (Project.FirstOrderSemantics.reduct M).mem f g ∧ Subset d f ∧ Subset e f

def cohenFilter {k : Nat} (X g : Fin k) : Formula k :=
  (Source.SetLanguage.subset g X).conj
    ((Formula.ex (Formula.mem (Fin.last k) g.castSucc)).conj
      ((Formula.all (.all ((Formula.mem (Fin.last k).castSucc g.castSucc.castSucc).imp
        ((Formula.mem (Fin.last (k+1)) X.castSucc.castSucc).imp
          ((Source.SetLanguage.subset (Fin.last (k+1)) (Fin.last k).castSucc).imp
            (Formula.mem (Fin.last (k+1)) g.castSucc.castSucc)))))).conj
        (.all (.all ((Formula.mem (Fin.last k).castSucc g.castSucc.castSucc).imp
          ((Formula.mem (Fin.last (k+1)) g.castSucc.castSucc).imp
            (.ex ((Formula.mem (Fin.last (k+2)) g.castSucc.castSucc.castSucc).conj
              ((Source.SetLanguage.subset (Fin.last k).castSucc.castSucc (Fin.last (k+2))).conj
                (Source.SetLanguage.subset (Fin.last (k+1)).castSucc (Fin.last (k+2))))))))))))

theorem cohenFilter_semantics {k : Nat} (env : Fin k → M.Carrier .set) (X g : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (cohenFilter X g) ↔
      CohenFilter (env X) (env g) := by
  simp only [cohenFilter,CohenFilter,Formula.Realize,ForcingLabelPermutations.subset_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Actual local equality at the fixed ground diagram, with a Cohen witness
in the supplied filter and the actual Product/WithTop condition code. -/
def EqG {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W g r sigma tau : M.Carrier .set) : Prop :=
  ∃ d z, (Project.FirstOrderSemantics.reduct M).mem d g ∧ Code z d r ∧ Forces true R env W sigma tau z

def eqG {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W g r sigma tau : Fin m) : Formula m :=
  .ex (.ex ((Formula.mem (Fin.last m).castSucc g.castSucc.castSucc).conj
    ((ForcingSupportingRoot.code (Fin.last (m+1)) (Fin.last m).castSucc r.castSucc.castSucc).conj
      (ForcingAtomicRelations.forces true R (paramsUp (paramsUp rho)) W.castSucc.castSucc
        sigma.castSucc.castSucc tau.castSucc.castSucc (Fin.last (m+1))))))

theorem eqG_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (rho : Fin k → Fin m) (W g r sigma tau : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (eqG R rho W g r sigma tau) ↔
      EqG R (fun j => env (rho j)) (env W) (env g) (env r) (env sigma) (env tau) := by
  simp only [eqG,EqG,Formula.Realize,ForcingSupportingRoot.code_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem eqG_refl (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : CohenFilter (env (rho 3)) g) (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (sigma : M.Carrier .set) : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma sigma := by
  obtain ⟨d,hd⟩ := hg.2.1
  obtain ⟨z,hz⟩ := exists_code hM d r
  have hzW := code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hr hz
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨d,z,hd,hz,ForcingAtomicBasic.eq_refl hM hpre sigma z hzW⟩

theorem eqG_symm (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W g r sigma tau : M.Carrier .set}
    (h : EqG R env W g r sigma tau) : EqG R env W g r tau sigma := by
  obtain ⟨d,z,hd,hz,he⟩ := h
  exact ⟨d,z,hd,hz,ForcingAtomicBasic.eq_symm hM he⟩

theorem eqG_trans (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r sigma tau upsilon : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : CohenFilter (env (rho 3)) g) (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (ha : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau)
    (hb : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r tau upsilon) :
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma upsilon := by
  obtain ⟨d,z,hd,hz,he⟩ := ha
  obtain ⟨d',z',hd',hz',he'⟩ := hb
  obtain ⟨f,hf,hdf,hdf'⟩ := hg.2.2.2 d d' hd hd'
  obtain ⟨q,hq⟩ := exists_code hM f r
  have hqW := code_mem hp ((hp.2.2.1 f).mp (hg.1 f hf)) hr hq
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hle := ForcingDiagramPoset.le_refl hm hr
  have hqz := (orderFormula_semantics env (rho 0) mul q z).mpr ((code_le hq hz).mpr ⟨hdf,hle⟩)
  have hqz' := (orderFormula_semantics env (rho 0) mul q z').mpr ((code_le hq hz').mpr ⟨hdf',hle⟩)
  exact ⟨f,q,hf,hq,ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_mono hM hpre hqW hqz he) (ForcingAtomicBasic.eq_mono hM hpre hqW hqz' he')⟩

/-- Source quotient restriction's well-definedness: keep the same Cohen
witness and strengthen only the ground diagram. -/
theorem eqG_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r s sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : CohenFilter (env (rho 3)) g) (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (he : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau) :
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g s sigma tau := by
  obtain ⟨d,z,hd,hz,heq⟩ := he
  obtain ⟨q,hq⟩ := exists_code hM d s
  have hqW := code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hs hq
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨d,q,hd,hq,ForcingAtomicBasic.eq_mono hM hpre hqW
    ((orderFormula_semantics env (rho 0) mul q z).mpr ((code_le hq hz).mpr ⟨fun _ h => h,hsr⟩)) heq⟩

end PPAC.Migration.ForcingLocalAtomic
