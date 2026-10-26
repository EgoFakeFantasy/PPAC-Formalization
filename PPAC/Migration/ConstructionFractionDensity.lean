/- Dense ordered fraction input for the pinned Base.height/cost real
interpretation. The internal mediant (a+c)/(b+d) supplies the witness.
All arithmetic laws are consumed from the existing native ZF library. -/
import PPAC.Migration.ConstructionFractionOrder

namespace PPAC.Migration.ConstructionFractionDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

abbrev Add (hM : FirstOrder.Theory.Models M nativeZF) (a b s : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) s a b

def Lt (hM : FirstOrder.Theory.Models M nativeZF) (w q r : M.Carrier .set) : Prop :=
  Le hM w q r ∧ ¬ Le hM w r q

def lt {m : Nat} (w q r : Fin m) : Project.Formula 1 m :=
  .conj (le w q r) (.neg (le w r q))

theorem lt_freeClosed {m : Nat} (w q r : Fin m) : (lt w q r).FreeClosed := by
  simp -implicitDefEqProofs [lt,Definitional.Formula.FreeClosed,le_freeClosed]

theorem lt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q r : Fin m) :
    Project.Formula.satisfies env (lt w q r) ↔ Lt hM (env.bound w) (env.bound q) (env.bound r) := by
  simp only [lt,Lt,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,le_semantics hM]

theorem lt_irrefl {hM : FirstOrder.Theory.Models M nativeZF} {w q : M.Carrier .set} : ¬ Lt hM w q q :=
  fun h => h.2 h.1

theorem le_lt_trans (hM : FirstOrder.Theory.Models M nativeZF) {w p q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hpq : Le hM w p q) (hqr : Lt hM w q r) : Lt hM w p r :=
  ⟨le_trans hM hw hpq hqr.1,fun hrp => hqr.2 (le_trans hM hw hrp hpq)⟩

theorem lt_le_trans (hM : FirstOrder.Theory.Models M nativeZF) {w p q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hpq : Lt hM w p q) (hqr : Le hM w q r) : Lt hM w p r :=
  ⟨le_trans hM hw hpq.1 hqr,fun hrp => hpq.2 (le_trans hM hw hqr hrp)⟩

theorem le_iff_products (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b c d u v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a b) (hr : Coordinates w r c d)
    (hu : Mul hM a d u) (hv : Mul hM c b v) : Le hM w q r ↔ NatLe u v := by
  rw [le_iff_cross hM hq hr]
  constructor
  · rintro ⟨u',v',hu',hv',h⟩
    have eu := mul_unique hM hw hr.2.1 hu' hu
    have ev := mul_unique hM hw hq.2.1 hv' hv
    exact eu ▸ ev ▸ h
  · exact fun h => ⟨u,v,hu,hv,h⟩

theorem lt_iff_products (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b c d u v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a b) (hr : Coordinates w r c d)
    (hu : Mul hM a d u) (hv : Mul hM c b v) : Lt hM w q r ↔ (Project.FirstOrderSemantics.reduct M).mem u v := by
  change (Le hM w q r ∧ ¬ Le hM w r q) ↔ _
  rw [le_iff_products hM hw hq hr hu hv,le_iff_products hM hw hr hq hv hu]
  constructor
  · rintro ⟨he | hlt,hn⟩
    · exact (hn (Or.inl he.symm)).elim
    · exact hlt
  · intro hlt
    exact ⟨Or.inr hlt,fun h => nat_not_reverse hM hw (mul_range hM hw hq.1 hr.2.1 hu) h hlt⟩

theorem add_exists (hM : FirstOrder.Theory.Models M nativeZF) {w a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s w ∧ Add hM a b s := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨s,hs,_⟩ := ZF.ordinalAddition_existsUnique hZF (KuratowskiZF.interpretation hM) a
    (hw.members_areOrdinals hZF b hb)
  exact ⟨s,ZF.ordinalAddition_mem_omega hZF (KuratowskiZF.interpretation hM) hw ha hb hs,hs⟩

theorem add_comm (hM : FirstOrder.Theory.Models M nativeZF) {w a b s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hs : Add hM a b s) : Add hM b a s := by
  obtain ⟨t,_,ht⟩ := add_exists hM hw hb ha
  have he := SetTheory.Structure.natural_add_comm (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hw ha hb hs ht
  exact he.symm ▸ ht

theorem mul_add (hM : FirstOrder.Theory.Models M nativeZF) {w a b c bc ab ac p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c w)
    (hbc : Add hM b c bc) (hp : Mul hM a bc p) (hab : Mul hM a b ab) (hac : Mul hM a c ac) : Add hM ab ac p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨s,_,hs⟩ := add_exists hM hw (mul_range hM hw ha hb hab) (mul_range hM hw ha hc hac)
  have he := ZF.ordinalMultiplication_add hZF (KuratowskiZF.interpretation hM)
    (ord a ha) (ord b hb) (ord c hc) hbc hp hab hac hs
  exact he.symm ▸ hs

/-- Construct the mediant from internal sums, without selecting external values. -/
theorem dense (hM : FirstOrder.Theory.Models M nativeZF) {w q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hqr : Lt hM w q r) :
    ∃ s, Fraction w s ∧ Lt hM w q s ∧ Lt hM w s r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨a,b,c,d,hq,hr,ad,cb,had,hcb,_⟩ := hqr.1
  have hadcb := (lt_iff_products hM hw hq hr had hcb).mp hqr
  have hAd := mul_range hM hw hq.1 hr.2.1 had
  have hCb := mul_range hM hw hr.1 hq.2.1 hcb
  obtain ⟨ac,hAc,hac⟩ := add_exists hM hw hq.1 hr.1
  obtain ⟨bd,hBd,hbd⟩ := add_exists hM hw hq.2.1 hr.2.1
  have hbdn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z bd := by
    rcases ZF.ordinalAddition_left_eq_or_mem hZF I (ord d hr.2.1) hbd with he | hb
    · exact he ▸ hq.2.2.1
    · exact ⟨b,hb⟩
  obtain ⟨s,hs⟩ := KuratowskiZF.exists_code hM ac bd
  have hS : Coordinates w s ac bd := ⟨hAc,hBd,hbdn,hs⟩
  obtain ⟨ab,hAb,hab⟩ := mul_exists hM hw hq.1 hq.2.1
  obtain ⟨cd,hCd,hcd⟩ := mul_exists hM hw hr.1 hr.2.1
  obtain ⟨abd,_,habd⟩ := mul_exists hM hw hq.1 hBd
  obtain ⟨acb,_,hacb⟩ := mul_exists hM hw hAc hq.2.1
  obtain ⟨acd,_,hacd⟩ := mul_exists hM hw hAc hr.2.1
  obtain ⟨cbd,_,hcbd⟩ := mul_exists hM hw hr.1 hBd
  have hleft := mul_add hM hw hq.1 hq.2.1 hr.2.1 hbd habd hab had
  have hright := mul_add hM hw hq.2.1 hq.1 hr.1 hac (mul_comm hM hw hAc hq.2.1 hacb)
    (mul_comm hM hw hq.1 hq.2.1 hab) (mul_comm hM hw hr.1 hq.2.1 hcb)
  have hleft' := mul_add hM hw hr.2.1 hq.1 hr.1 hac (mul_comm hM hw hAc hr.2.1 hacd)
    (mul_comm hM hw hq.1 hr.2.1 had) (mul_comm hM hw hr.1 hr.2.1 hcd)
  have hright' := mul_add hM hw hr.1 hq.2.1 hr.2.1 hbd hcbd hcb hcd
  have hineq := ZF.ordinalAddition_isIncreasingOnOrdinals hZF I (ord ab hAb)
    ad cb (ord ad hAd) (ord cb hCb) hadcb abd acb hleft hright
  have hineq' := ZF.ordinalAddition_isIncreasingOnOrdinals hZF I (ord cd hCd)
    ad cb (ord ad hAd) (ord cb hCb) hadcb acd cbd
      (add_comm hM hw hAd hCd hleft') (add_comm hM hw hCb hCd hright')
  exact ⟨s,⟨ac,bd,hS⟩,(lt_iff_products hM hw hq hS habd hacb).mpr hineq,
    (lt_iff_products hM hw hS hr hacd hcbd).mpr hineq'⟩

def densitySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.forallE (.forallE (.imp (lt (2 : Fin 3) 1 0) (.existsE
      (.conj (fraction (3 : Fin 4) 0) (.conj (lt (3 : Fin 4) 2 0) (lt (3 : Fin 4) 0 1))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,lt_freeClosed,fraction_freeClosed]

theorem density_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence densitySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) densitySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,lt_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,fraction_semantics hM]
  exact fun q r hqr => dense hM hw hqr

theorem density_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence densitySentence) := ModelTransfer.derives (fun _ hM => density_models hM)

end PPAC.Migration.ConstructionFractionDensity
