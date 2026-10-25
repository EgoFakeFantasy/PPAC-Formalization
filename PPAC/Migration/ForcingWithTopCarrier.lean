/- Internal presentation of the pinned ProductNames.Poset = WithTop Condition.
The empty set codes top; {p} codes the original condition p. All carriers,
empty sets and singletons are constructed inside arbitrary nativeZF models. -/
import PPAC.Migration.ForcingProductAction

namespace PPAC.Migration.ForcingWithTopCarrier
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Empty (z : M.Carrier .set) : Prop := ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x z

def empty {m : Nat} (z : Fin m) : Formula m := .all (.neg (.mem (Fin.last m) z.castSucc))

theorem empty_semantics {m : Nat} (env : Fin m → M.Carrier .set) (z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (empty z) ↔ Empty (env z) := by
  simp only [empty, Empty, Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc]

def Single (z p : M.Carrier .set) : Prop :=
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x z ↔ x = p

def single {m : Nat} (z p : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) z.castSucc).iff (.equal (Fin.last m) p.castSucc))

theorem single_semantics {m : Nat} (env : Fin m → M.Carrier .set) (z p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (single z p) ↔
      Single (env z) (env p) := by
  simp only [single, Single, Source.Formula.iff, Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1, (h x).2⟩, fun h x => ⟨(h x).mp, (h x).mpr⟩⟩

def Element (P z : M.Carrier .set) : Prop := Empty z ∨
  ∃ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ Single z p

def element {m : Nat} (P z : Fin m) : Formula m :=
  (empty z).disj (.ex ((Formula.mem (Fin.last m) P.castSucc).conj (single z.castSucc (Fin.last m))))

theorem element_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (element P z) ↔
      Element (env P) (env z) := by
  simp only [element, Element, Formula.Realize, empty_semantics (M := M), single_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]

def Carrier (P W : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z W ↔ Element P z

def carrier {m : Nat} (P W : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) W.castSucc).iff (element P.castSucc (Fin.last m)))

theorem carrier_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P W : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (carrier P W) ↔
      Carrier (env P) (env W) := by
  simp only [carrier, Carrier, Source.Formula.iff, Formula.Realize, element_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1, (h z).2⟩, fun h z => ⟨(h z).mp, (h z).mpr⟩⟩

theorem single_nonempty {z p : M.Carrier .set} (h : Single z p) : ¬ Empty z :=
  fun he => he p ((h p).mpr rfl)

theorem single_injective {z p q : M.Carrier .set} (hp : Single z p) (hq : Single z q) : p = q :=
  (hq p).mp ((hp p).mpr rfl)

theorem empty_unique (hM : FirstOrder.Theory.Models M nativeZF) {z t : M.Carrier .set}
    (hz : Empty z) (ht : Empty t) : z = t :=
  (ModelTransfer.extensionality hM).eq_of_same_members z t
    (fun x => ⟨fun hx => False.elim (hz x hx), fun hx => False.elim (ht x hx)⟩)

theorem single_unique (hM : FirstOrder.Theory.Models M nativeZF) {z t p : M.Carrier .set}
    (hz : Single z p) (ht : Single t p) : z = t :=
  (ModelTransfer.extensionality hM).eq_of_same_members z t (fun x => (hz x).trans (ht x).symm)

theorem exists_empty (hM : FirstOrder.Theory.Models M nativeZF) : ∃ e, Empty (M := M) e :=
  SetTheory.KP.exists_empty (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))

theorem exists_single (hM : FirstOrder.Theory.Models M nativeZF) (p : M.Carrier .set) :
    ∃ z, Single (M := M) z p :=
  SetTheory.KP.exists_singleton (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) p

theorem element_subset {P z : M.Carrier .set} (hz : Element P z) :
    ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x z →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x P := by
  intro x hx
  rcases hz with he | ⟨p, hp, hs⟩
  · exact False.elim (he x hx)
  · exact ((hs x).mp hx).symm ▸ hp

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (P : M.Carrier .set) :
    ∃ W, Carrier P W := by
  obtain ⟨power, hPower⟩ := SetTheory.ZF.exists_powerSet (ModelTransfer.project_models_iff.mp hM) P
  let params := Source.SetLanguage.args1 P
  let query := element (0 : Fin 1).castSucc (Fin.last 1)
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨W, hW⟩ := sep params power
  have hq : ∀ z, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases z params) query ↔ Element P z := by
    intro z
    exact element_semantics (M := M) (Fin.lastCases z params) (0 : Fin 1).castSucc (Fin.last 1)
  refine ⟨W, fun z => ?_⟩
  exact ⟨fun hz => (hq z).mp ((hW z).mp hz).2,
    fun hz => (hW z).mpr ⟨(hPower z).mpr (element_subset hz), (hq z).mpr hz⟩⟩

theorem exists_embedding (hM : FirstOrder.Theory.Models M nativeZF) {P W p : M.Carrier .set}
    (hW : Carrier P W) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    ∃ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z W ∧ Single z p := by
  obtain ⟨z, hz⟩ := exists_single hM p
  exact ⟨z, (hW z).mpr (Or.inr ⟨p, hp, hz⟩), hz⟩

def constructionSentence : Source.Sentence :=
  (Formula.ex (.ex ((carrier (0 : Fin 1).castSucc.castSucc (Fin.last 1).castSucc).conj
    ((empty (Fin.last 2)).conj (.mem (Fin.last 2) (Fin.last 1).castSucc))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨W, hW⟩ := exists_carrier hM (env 0)
  obtain ⟨e, he⟩ := exists_empty hM
  let v : Fin 3 → M.Carrier .set := Fin.lastCases e (Fin.lastCases W env)
  refine ⟨W, e, ?_, ?_, (hW e).mpr (Or.inl he)⟩
  · apply (carrier_semantics (M := M) v (0 : Fin 1).castSucc.castSucc (Fin.last 1).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hW
  · apply (empty_semantics (M := M) v (Fin.last 2)).mpr
    simpa only [v, Fin.lastCases_last] using he

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingWithTopCarrier
