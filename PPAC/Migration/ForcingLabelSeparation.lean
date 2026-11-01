/- Fixed ProductNames.mem_label_of_bit:263, mem_label:270,
not_mem_label_of_bit:292 and label_not_equal:304.
Direct consumer: AssignedGraphs.graphRelation_one:109 (also ChoiceFailure).
Reuse existing actual Cohen separation, Bit laws and check-name reflection.
No new forcing, choice, cardinal, condition or name construction. -/
import PPAC.Migration.ForcingLabelDensity
import PPAC.Migration.ForcingCheckReflection
import PPAC.Migration.ConstructionCohenSeparation

namespace PPAC.Migration.ForcingLabelSeparation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingProductFamily (Presentation)
open ForcingLabelNames (Label)
open ForcingCheckName (Checked)
open ForcingProductBits (Bit)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem mem_label_of_bit (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one c top j bit name alpha x nx p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hn : Label (env (rho 6)) K c top j bit name)
    (ha : (Project.FirstOrderSemantics.reduct M).mem alpha K)
    (hcx : PureKuratowski.PairMember M alpha x c) (hx : Checked top x nx)
    (hb : Bit (env (rho 6)) p j alpha bit) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nx name p := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ForcingAtomicBasic.mem_of_edge_eq hM hpre hb.1 (hpre.1 p hb.1)
    ((ForcingLabelNames.edge_label hM hn nx p).mpr ⟨alpha,ha,⟨x,hcx,hx⟩,hb⟩)
    (ForcingAtomicBasic.eq_refl hM hpre nx p hb.1)

theorem mem_label (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one c top j bit name nu p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hn : Label (env (rho 6)) K c top j bit name)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q p →
        ∃ r alpha x nx, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
          MapRel (orderFormula (rho 0) mul) env r q ∧ (Project.FirstOrderSemantics.reduct M).mem alpha K ∧
          PureKuratowski.PairMember M alpha x c ∧ Checked top x nx ∧ Bit (env (rho 6)) r j alpha bit ∧
          Forces true (orderFormula (rho 0) mul) env (env (rho 6)) nu nx r := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  constructor
  · intro h q hq hqp
    obtain ⟨r,nx,d,hr,hrq,_,he,hrd,heq⟩ := ((ForcingAtomicRelations.mem_iff hM _ _ _ _ _ _).mp h).2 q hq hqp
    obtain ⟨alpha,ha,⟨x,hcx,hx⟩,hb⟩ := (ForcingLabelNames.edge_label hM hn nx d).mp he
    exact ⟨r,alpha,x,nx,hr,hrq,ha,hcx,hx,
      ForcingProductBits.bit_mono hp hr ((orderFormula_semantics env (rho 0) mul r d).mp hrd) hb,heq⟩
  · intro h
    apply (ForcingAtomicRelations.mem_iff hM _ _ _ _ _ _).mpr
    refine ⟨hpW,?_⟩
    intro q hq hqp
    obtain ⟨r,alpha,x,nx,hr,hrq,ha,hcx,hx,hb,heq⟩ := h q hq hqp
    exact ⟨r,nx,r,hr,hrq,hr,(ForcingLabelNames.edge_label hM hn nx r).mpr ⟨alpha,ha,⟨x,hcx,hx⟩,hb⟩,hpre.1 r hr,heq⟩

theorem not_mem_label_of_bit (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one values c top j lo hi name alpha x nx p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hc : ForcingSupportSize.Injection K values c) (ht : ForcingWithTopCarrier.Empty top)
    (hne : lo ≠ hi) (hn : Label (env (rho 6)) K c top j hi name)
    (hcx : PureKuratowski.PairMember M alpha x c) (hx : Checked top x nx)
    (hb : Bit (env (rho 6)) p j alpha lo) :
    ¬ Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nx name p := by
  intro h
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  obtain ⟨r,beta,y,ny,hr,hrp,_,hcy,hy,hbit,heq⟩ :=
    (mem_label hM env rho mul hp hm hn hb.1).mp h p hb.1 (hpre.1 p hb.1)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q top :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht)
  have exy := (ForcingCheckReflection.eq_check_iff hM hpre ((hp.2.2.2.2.2 top).mpr (Or.inl ht)) hTop hr hx hy).mp heq
  have eab := hc.2 alpha beta x hcx (exy.symm ▸ hcy)
  subst beta
  exact hne (ForcingProductBits.bit_functional hM hp
    (ForcingProductBits.bit_mono hp hr ((orderFormula_semantics env (rho 0) mul r p).mp hrp) hb) hbit)

theorem label_not_equal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one values c top lo hi root j l left right p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hK : ¬ ForcingSupportSize.Small K w)
    (hc : ForcingSupportSize.Injection K values c) (ht : ForcingWithTopCarrier.Empty top)
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B)
    (hBits : lo ≠ hi) (hroot : ForcingSupportSize.Injection (env (rho 0)) I root)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j I) (hl : (Project.FirstOrderSemantics.reduct M).mem l I)
    (hjl : j ≠ l) (hLeft : Label (env (rho 6)) K c top j hi left) (hRight : Label (env (rho 6)) K c top l hi right) :
    ¬ Forces true (orderFormula (rho 0) mul) env (env (rho 6)) left right p := by
  intro hEq
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hpW := ForcingAtomicBasic.condition hM hEq
  obtain ⟨d,r,z,hd,hr,hz,hzp⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hroot hpW
  obtain ⟨d',alpha,hd',hdd,ha,hneg,hpos⟩ := ConstructionCohenSeparation.separate_labels hM hw hp.1 hp.2.1 hd hK hj hl hjl hlo hhi
  obtain ⟨z',hz'⟩ := ForcingSupportingRoot.exists_code hM d' r
  have hzW := ForcingSupportingRoot.code_mem hp hd hr hz
  have hzW' := ForcingSupportingRoot.code_mem hp hd' hr hz'
  have hzz := (ForcingSupportingRoot.code_le hz' hz).mpr ⟨hdd,ForcingDiagramPoset.le_refl hm hr⟩
  have hz'p := hpre.2 z' z p hzW' hzW hpW
    ((orderFormula_semantics env (rho 0) mul z' z).mpr hzz) ((orderFormula_semantics env (rho 0) mul z p).mpr hzp)
  have hEq' := ForcingAtomicBasic.eq_mono hM hpre hzW' hz'p hEq
  obtain ⟨x,hcx,_⟩ := hc.1.1.2 alpha ha
  obtain ⟨nx,hx⟩ := ForcingCheckName.exists_checked hM top x
  have hmRight := mem_label_of_bit hM env rho mul hp hm hRight ha hcx hx ((ForcingProductBits.bit_coe hzW' hz').mpr hpos)
  exact not_mem_label_of_bit hM env rho mul hp hm hc ht hBits hLeft hcx hx
    ((ForcingProductBits.bit_coe hzW' hz').mpr hneg)
    ((ForcingAtomicLaws.mem_congr_right hM hpre hEq').mpr hmRight)

/-- All internal conditions, including top, and arbitrary internal ground
coding injections are retained. The target set `values` only bounds the range
of the already set-coded injection; it is universally quantified. -/
def separationSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w one mul values c top lo hi root j l left right p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small K w)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection c K values))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (.mem (.bound lo) (.bound B))
    (.imp (.mem (.bound hi) (.bound B))
    (.imp (.neg (Project.Formula.extensionalEq (.bound lo) (.bound hi)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection root (rho 0) I))
    (.imp (.mem (.bound j) (.bound I))
    (.imp (.mem (.bound l) (.bound I))
    (.imp (.neg (Project.Formula.extensionalEq (.bound j) (.bound l)))
    (.imp (ProjectSyntax.encode id (ForcingLabelNames.label (rho 6) K c top j hi left))
    (.imp (ProjectSyntax.encode id (ForcingLabelNames.label (rho 6) K c top l hi right))
    (.neg (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) left right p))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.extensionalEq]

theorem separation_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w one mul values c top lo hi root j l left right p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (separationSentence rho I K B w one mul values c top lo hi root j l left right p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M)]
  exact label_not_equal hM env rho mul

theorem separation_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w one mul values c top lo hi root j l left right p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (separationSentence rho I K B w one mul values c top lo hi root j l left right p)) := by
  apply ModelTransfer.derives
  intro M hM
  exact separation_models rho I K B w one mul values c top lo hi root j l left right p hM

end PPAC.Migration.ForcingLabelSeparation
