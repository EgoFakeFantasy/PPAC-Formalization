/- Internal order-cover transport, reusing the completed L stage-bound route.
The existing Project.isSetCodedWellOrder quantifies over internal subsets.
Source syntax comes from the existing ProjectDecode compiler. The argument
uses no externally well-founded relation or external ordinal recursion.
The actual L stage construction is still a separate obligation. -/
import PPAC.Migration.KuratowskiZF
import YesMetaZFC.SetTheory.Ord.OrderType
import PPAC.Migration.ProjectDecode

namespace PPAC.Migration.InternalWellOrderChoice
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph : Source.Formula 3 := Source.SetLanguage.edge 0 1 2

theorem least_graph (hM : FirstOrder.Theory.Models M nativeZF) (r x y : M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Source.SetLanguage.args3 r x y)
      (DefinableMinimaChoice.least graph) ↔
    (Project.FirstOrderSemantics.reduct M).mem y x ∧ ∀ z,
      (Project.FirstOrderSemantics.reduct M).mem z x →
        ¬ (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) z y r := by
  simp only [DefinableMinimaChoice.least, Source.Formula.Realize,
    DefinableMinimaChoice.realize_rename]
  have he (z : M.Carrier .set) :
      (fun i => Fin.lastCases z (Source.SetLanguage.args3 r x y)
        (Source.SetLanguage.args3 0 3 2 i)) = Source.SetLanguage.args3 r z y := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k =>
      Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i <;> rfl
  simp only [he, graph, KuratowskiZF.source_edge]
  rfl

theorem unique_minimum (hM : FirstOrder.Theory.Models M nativeZF)
    {r a x : M.Carrier .set}
    (hwo : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r a)
    (hx : (Project.FirstOrderSemantics.reduct M).MemberSubset x a)
    (hne : ∃ y, (Project.FirstOrderSemantics.reduct M).mem y x) :
    ∃ y, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
        (Source.SetLanguage.args3 r x y) (DefinableMinimaChoice.least graph) ∧
      ∀ z, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
        (Source.SetLanguage.args3 r x z) (DefinableMinimaChoice.least graph) → z = y := by
  obtain ⟨y, hy, hleast⟩ := hwo.least x hx hne
  have hmin : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z x →
      ¬ (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) z y r := by
    intro z hz hzy
    rcases hleast z hz with heq | hyz
    · have hEq := (ModelTransfer.extensionality hM).eq_of_same_members y z heq
      subst z
      exact hwo.linear.2.1.1 y (hx y hy) hzy
    · exact hwo.linear.2.1.1 y (hx y hy)
        (hwo.linear.2.1.2 y (hx y hy) z (hx z hz) y (hx y hy) hyz hzy)
  refine ⟨y, (least_graph hM r x y).mpr ⟨hy, hmin⟩, ?_⟩
  intro z hz
  have hzm := (least_graph hM r x z).mp hz
  rcases hleast z hzm.1 with heq | hyz
  · exact ((ModelTransfer.extensionality hM).eq_of_same_members y z heq).symm
  · exact False.elim (hzm.2 y hy hyz)

/-- Actual existing order syntax on an internal bounding set. -/
def projectCover : Project.Sentence where
  formula := .forallE (.existsE (.existsE (.conj
    (Project.Formula.subset (.bound 2) (.bound 1))
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound 0) (.bound 1)))))
  freeClosed := by decide +kernel

def wellOrderCover : Source.Sentence :=
  ProjectDecode.reverse projectCover.formula projectCover.freeClosed

theorem cover_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence wellOrderCover).TrueIn M ↔
      ∀ a, ∃ b r, (Project.FirstOrderSemantics.reduct M).MemberSubset a b ∧
        (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
          (KuratowskiZF.interpretation hM) r b := by
  have hNorm := (Normalization.equivalent (T := nativeZF) (Γ := [])
    (Project.fo_sentence projectCover)).semantically_entails M hM
  have hRaw : (Translation.sentence wellOrderCover).TrueIn M ↔
      (Project.fo_sentence projectCover).TrueIn M := by
    simpa only [wellOrderCover, ProjectDecode.closed_fo, FirstOrder.Formula.TrueIn] using hNorm.symm
  refine hRaw.trans ?_
  rw [Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hM) projectCover,
    SetTheory.Structure.satisfiesSentence_iff]
  simp only [projectCover,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff]
  constructor
  · intro h a
    let ρ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0, fun _ => a⟩
    have ha := h (fun _ => a)
    change ∀ c, ∃ b r, Project.Formula.satisfies (((ρ.push c).push b).push r)
      (.conj (Project.Formula.subset (.bound 2) (.bound 1))
        (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound 0) (.bound 1))) at ha
    obtain ⟨b, r, hr⟩ := ha a
    have hs := (Project.Formula.satisfies_conj_iff _ _ _).mp hr
    exact ⟨b, r, (Project.Formula.satisfies_subset_iff _ _ _).mp hs.1,
      (Project.Formula.satisfies_isSetCodedWellOrder_iff
        (KuratowskiZF.interpretation hM) (((ρ.push a).push b).push r) (.bound 0) (.bound 1)).mp hs.2⟩
  · intro h free
    let ρ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0, free⟩
    change ∀ a, ∃ b r, Project.Formula.satisfies (((ρ.push a).push b).push r)
      (.conj (Project.Formula.subset (.bound 2) (.bound 1))
        (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound 0) (.bound 1)))
    intro a
    obtain ⟨b, r, hs, hr⟩ := h a
    refine ⟨b, r, (Project.Formula.satisfies_conj_iff _ _ _).mpr ⟨?_, ?_⟩⟩
    · exact (Project.Formula.satisfies_subset_iff _ _ _).mpr hs
    · exact (Project.Formula.satisfies_isSetCodedWellOrder_iff
        (KuratowskiZF.interpretation hM) (((ρ.push a).push b).push r) (.bound 0) (.bound 1)).mpr hr

theorem minimum_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hwo : (Translation.sentence wellOrderCover).TrueIn M) :
    (Translation.sentence (DefinableMinimaChoice.minimumPrinciple graph)).TrueIn M := by
  have hOrders := (cover_models hM).mp hwo
  apply (Translation.realizes_sentence M _).mpr
  apply (DefinableMinimaChoice.minimum_semantics _ graph).mpr
  intro a
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨u, hu⟩ := SetTheory.KP.exists_union hKP a
  obtain ⟨b, r, hSub, hr⟩ := hOrders u
  refine ⟨r, ?_⟩
  intro x hxa hne
  exact unique_minimum hM hr (fun y hy => hSub y ((hu y).mpr ⟨x, hxa, hy⟩)) hne

theorem minimum_kernel_certificate : FirstOrder.Derives nativeZF []
    (Translation.sentence (wellOrderCover.imp (DefinableMinimaChoice.minimumPrinciple graph))) :=
  ModelTransfer.derives (fun _ hM => minimum_models hM)

theorem kernel_certificate : FirstOrder.Derives nativeZF []
    (Translation.sentence (wellOrderCover.imp Source.SetLanguage.AC)) := by
  apply FirstOrder.Derives.imp_intro
  have hMin := FirstOrder.Derives.imp_elim minimum_kernel_certificate.context_weaken_cons
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.imp_elim
    (DefinableMinimaChoice.kernel_certificate graph).context_weaken_cons hMin

theorem source_certificate : Source.Derives (Source.SetLanguage.ZF.at 1)
    ((wellOrderCover.imp Source.SetLanguage.AC).rename Fin.elim0) :=
  ReverseZFReplay.source_sentence kernel_certificate

theorem relative_kernel_certificate (D : Source.Formula 1) :
    FirstOrder.Derives (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp
        ((Relativization.formula D wellOrderCover).imp (Relativization.formula D Source.SetLanguage.AC)))) :=
  Relativization.kernel_certificate D source_certificate

end PPAC.Migration.InternalWellOrderChoice
