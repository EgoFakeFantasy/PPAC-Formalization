/- Literal minimum for the pinned rawCost recursion. Reuse the accepted
comparison of all internal cuts; no additional real-field construction. -/
import PPAC.Migration.ConstructionCutArithmetic

namespace PPAC.Migration.ConstructionCutMinimum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (a b c : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p c ↔
    (Project.FirstOrderSemantics.reduct M).mem p a ∧ (Project.FirstOrderSemantics.reduct M).mem p b

def value {m : Nat} (a b c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound a.succ)) (.mem (.bound 0) (.bound b.succ))))

theorem value_freeClosed {m : Nat} (a b c : Fin m) : (value a b c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed]

theorem value_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (a b c : Fin m) : Project.Formula.satisfies env (value a b c) ↔
      Value (env.bound a) (env.bound b) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound]
  rfl

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {a b c d : M.Carrier .set}
    (hc : Value a b c) (hd : Value a b d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => (hc p).trans (hd p).symm)

theorem exists_minimum (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) : ∃ c, Cut hM w Q c ∧ Value a b c := by
  rcases cuts_total hM hw hQ ha hb with hab | hba
  · exact ⟨a,ha,fun p => ⟨fun hp => ⟨hp,hab p hp⟩,And.left⟩⟩
  · exact ⟨b,hb,fun p => ⟨fun hp => ⟨hba p hp,hp⟩,And.right⟩⟩

theorem value_cases (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value a b c) : c = a ∨ c = b := by
  rcases cuts_total hM hw hQ ha hb with hab | hba
  · exact Or.inl (value_unique hM hc (fun p => ⟨fun hp => ⟨hp,hab p hp⟩,And.left⟩))
  · exact Or.inr (value_unique hM hc (fun p => ⟨fun hp => ⟨hba p hp,hp⟩,And.right⟩))

theorem value_bounds {a b c : M.Carrier .set} (hc : Value a b c) : Subset c a ∧ Subset c b :=
  ⟨fun p hp => ((hc p).mp hp).1,fun p hp => ((hc p).mp hp).2⟩

theorem value_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value a b c)
    (han : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a)
    (hbn : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p b) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p c := by
  rcases value_cases hM hw hQ ha hb hc with rfl | rfl
  · exact han
  · exact hbn

def Total (R : M.Carrier .set) : Prop := ∀ a b,
  (Project.FirstOrderSemantics.reduct M).mem a R → (Project.FirstOrderSemantics.reduct M).mem b R →
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c R ∧ Value a b c ∧
      Subset c a ∧ Subset c b ∧ (c = a ∨ c = b) ∧
      ((∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) →
        (∃ p, (Project.FirstOrderSemantics.reduct M).mem p b) →
        ∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧
      ∀ d, Value a b d → d = c

theorem total (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hR : CutCarrier hM w Q R) : Total R := by
  intro a b ha hb
  have hA := (hR a).mp ha
  have hB := (hR b).mp hb
  obtain ⟨c,hc,hv⟩ := exists_minimum hM hw hQ hA hB
  exact ⟨c,(hR c).mpr hc,hv,(value_bounds hv).1,(value_bounds hv).2,
    value_cases hM hw hQ hA hB hv,value_nonempty hM hw hQ hA hB hv,
    fun d hd => value_unique hM hd hv⟩

end PPAC.Migration.ConstructionCutMinimum
