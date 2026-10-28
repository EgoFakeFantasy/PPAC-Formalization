/- Pinned ProductNames.Bit/bit_coe/not_bit_top/bit_mono/bit_functional/bit_move.
Actual consumers: ProductNames.label, smul_label and mem_label, then
LocalQuotients.labelSet_subsetBound/localName_descent. Reuse existing internal
Cohen graphs, exact coordinate movement and WithTop coding. No new forcing,
recursion or support backend; values range over the actual internal carrier. -/
import PPAC.Migration.ForcingSupportOrbit

namespace PPAC.Migration.ForcingProductBits
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductFamily (Presentation)
open ForcingConditionGraphs (Permutation)
open ForcingSupportingRoot (Code code_mem)
open ConstructionCohenCompatibility (Entry)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact source Bit on the internally presented WithTop carrier.
Membership in W replaces the source's condition subtype; top has no code. -/
def Bit (W p j alpha b : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem p W ∧
    ∃ d s, Code p d s ∧ Entry d j alpha b

/-- Source formula for the existing nested Cohen coordinate entry. -/
def coordinateEntry {k : Nat} (d j alpha b : Fin k) : Formula k :=
  .ex ((PairSyntax.ordered (Fin.last k) j.castSucc alpha.castSucc).conj
    (Source.SetLanguage.edge d.castSucc (Fin.last k) b.castSucc))

theorem coordinateEntry_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (d j alpha b : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (coordinateEntry d j alpha b) ↔
      Entry (env d) (env j) (env alpha) (env b) := by
  simp only [coordinateEntry,Entry,Formula.Realize,KuratowskiZF.source_code,
    KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def bit {k : Nat} (W p j alpha b : Fin k) : Formula k :=
  (Formula.mem p W).conj (.ex (.ex
    ((ForcingSupportingRoot.code p.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).conj
      (coordinateEntry (Fin.last k).castSucc j.castSucc.castSucc
        alpha.castSucc.castSucc b.castSucc.castSucc))))

theorem bit_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (W p j alpha b : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (bit W p j alpha b) ↔
      Bit (env W) (env p) (env j) (env alpha) (env b) := by
  simp only [bit,Bit,Formula.Realize,ForcingSupportingRoot.code_semantics (M := M),
    coordinateEntry_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem bit_coe {W p d s j alpha b : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p W) (hc : Code p d s) :
    Bit W p j alpha b ↔ Entry d j alpha b := by
  constructor
  · rintro ⟨_,d',s',⟨z',hz',hs'⟩,hb⟩
    obtain ⟨z,hz,hs⟩ := hc
    have e := ForcingWithTopCarrier.single_injective hs' hs
    obtain ⟨rfl,_⟩ := PureKuratowski.code_injective (e ▸ hz') hz
    exact hb
  · intro hb
    exact ⟨hp,d,s,hc,hb⟩

theorem not_bit_top {W p j alpha b : M.Carrier .set}
    (hp : ForcingWithTopCarrier.Empty p) : ¬ Bit W p j alpha b := by
  rintro ⟨_,_,_,⟨_,_,hs⟩,_⟩
  exact ForcingWithTopCarrier.single_nonempty hs hp

theorem bit_mono {D I K B w C S X Y P W mul p q j alpha b : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hle : ForcingWithTopAction.Le D mul q p) (hb : Bit W p j alpha b) :
    Bit W q j alpha b := by
  obtain ⟨_,d,s,hcode,a,ha,z,hz,hzd⟩ := hb
  obtain ⟨c,t,_,_,hqcode⟩ := ForcingActiveIndependent.below_code hp hq hcode hle
  have hsub := ((ForcingSupportingRoot.code_le hqcode hcode).mp hle).1
  exact ⟨hq,c,t,hqcode,a,ha,z,hz,hsub z hzd⟩

theorem bit_functional (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W p j alpha b c : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W)
    (hb : Bit W p j alpha b) (hc : Bit W p j alpha c) : b = c := by
  obtain ⟨hpW,d,s,hcode,hb⟩ := hb
  obtain ⟨z,hz,hps⟩ := hcode
  have hzP := ForcingProductPoset.coe_mem hp.2.2.2.2.2 hpW hps
  obtain ⟨d',hd',s',_,hz'⟩ := (hp.2.2.2.2.1 z).mp hzP
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  exact ConstructionCohenCompatibility.entry_functional hM ((hp.2.2.1 d).mp hd').2.1
    hb ((bit_coe hpW ⟨z,hz,hps⟩).mp hc)

/-- Both directions of source bit_move, including the adjoined top.
The moved condition is read from the actual action, not assumed coordinate data. -/
theorem bit_move (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi A p q j j' alpha b : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hpi : Permutation I pi)
    (hA : ForcingProductFamily.Action D C S X Y P W pi A)
    (hpq : PureKuratowski.PairMember M p q A) (hjj : PureKuratowski.PairMember M j j' pi) :
    Bit W q j' alpha b ↔ Bit W p j alpha b := by
  have hperm := ForcingProductFamily.action_permutation hA
  have hpW := ForcingConditionGraphs.function_input hperm.1.1 hpq
  have hqW := hperm.1.2 p q hpq
  rcases (hp.2.2.2.2.2 p).mp hpW with he | ⟨z,hzP,hpz⟩
  · have hpFixed := ForcingProductFamily.top_fixed hp he hA
    have epq := ForcingConditionGraphs.function_unique hperm.1.1 hpFixed hpq
    subst q
    exact ⟨fun h => False.elim (not_bit_top he h),fun h => False.elim (not_bit_top he h)⟩
  · obtain ⟨d,hdX,s,hsY,hz⟩ := (hp.2.2.2.2.1 z).mp hzP
    have hd := (hp.2.2.1 d).mp hdX
    have hs := (hp.2.2.2.1 s).mp hsY
    have hcode : Code p d s := ⟨z,hz,hpz⟩
    let v : Fin 7 → M.Carrier .set :=
      Fin.cases D (Fin.cases C (Fin.cases S (Fin.cases X (Fin.cases Y (Fin.cases P (Fin.cases W Fin.elim0))))))
    have hpres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) := hp
    obtain ⟨d',s',_,hMoved,_,hqcode⟩ := ForcingSupportOrbit.moved_coordinates hM v hpres hpi
      ((ForcingProductFamily.mapRel_action v pi A).mpr hA) hd hs hcode hpq
    have hm := (ConstructionDescentPlacement.actual_moved_condition hMoved).2
    rw [bit_coe hqW hqcode,bit_coe hpW hcode,hm j' alpha b]
    constructor
    · rintro ⟨i,hij,hi⟩
      have e := hpi.2.1 i j j' hij hjj
      exact e ▸ hi
    · intro h
      exact ⟨j,hjj,h⟩

/-- All variables are object-quantified; this is literal Cohen membership. -/
def coeSentence : Source.Sentence :=
  ((Formula.mem (0 : Fin 7) 1).imp
    ((ForcingSupportingRoot.code 0 2 3).imp
      ((bit 1 0 4 5 6).iff (coordinateEntry 2 4 5 6)))).close

theorem coe_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence coeSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hc
  have h := bit_coe (j := env 4) (alpha := env 5) (b := env 6) hp ((ForcingSupportingRoot.code_semantics (M := M) env 0 2 3).mp hc)
  constructor
  · intro hb
    exact (coordinateEntry_semantics (M := M) env 2 4 5 6).mpr
      (h.mp ((bit_semantics (M := M) env 1 0 4 5 6).mp hb))
  · intro hb
    exact (bit_semantics (M := M) env 1 0 4 5 6).mpr
      (h.mpr ((coordinateEntry_semantics (M := M) env 2 4 5 6).mp hb))

theorem coe_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence coeSentence) :=
  ModelTransfer.derives (fun _ hM => coe_models hM)

def topSentence : Source.Sentence :=
  ((ForcingWithTopCarrier.empty (0 : Fin 5)).imp ((bit 1 0 2 3 4).neg)).close

theorem top_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence topSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hb
  exact not_bit_top ((ForcingWithTopCarrier.empty_semantics (M := M) env 0).mp hp)
    ((bit_semantics (M := M) env 1 0 2 3 4).mp hb)

theorem top_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence topSentence) :=
  ModelTransfer.derives (fun _ hM => top_models hM)

def monoSentence : Source.Sentence :=
  ((ForcingProductFamily.presentation (0 : Fin 17) 1 2 3 4 5 6 7 8 9 10).imp
    ((Formula.mem 13 10).imp
      ((ForcingWithTopAction.le 0 11 13 12).imp
        ((bit 10 12 14 15 16).imp (bit 10 13 14 15 16))))).close

theorem mono_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence monoSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hq hle hb
  exact (bit_semantics (M := M) env 10 13 14 15 16).mpr
    (bit_mono ((ForcingProductFamily.presentation_semantics (M := M) env 0 1 2 3 4 5 6 7 8 9 10).mp hp)
      hq ((ForcingWithTopAction.le_semantics (M := M) env 0 11 13 12).mp hle)
      ((bit_semantics (M := M) env 10 12 14 15 16).mp hb))

theorem mono_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence monoSentence) :=
  ModelTransfer.derives (fun _ hM => mono_models hM)

def functionalSentence : Source.Sentence :=
  ((ForcingProductFamily.presentation (0 : Fin 16) 1 2 3 4 5 6 7 8 9 10).imp
    ((bit 10 11 12 13 14).imp
      ((bit 10 11 12 13 15).imp (Formula.equal 14 15)))).close

theorem functional_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence functionalSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hb hc
  exact bit_functional hM
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 1 2 3 4 5 6 7 8 9 10).mp hp)
    ((bit_semantics (M := M) env 10 11 12 13 14).mp hb)
    ((bit_semantics (M := M) env 10 11 12 13 15).mp hc)

theorem functional_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence functionalSentence) :=
  ModelTransfer.derives (fun _ hM => functional_models hM)

/-- Exact movement of the actual condition and index; no assumed Bit covariance. -/
def moveSentence : Source.Sentence :=
  ((ForcingProductFamily.presentation (0 : Fin 19) 1 2 3 4 5 6 7 8 9 10).imp
    ((ForcingConditionGraphs.permutation 1 11).imp
      ((ForcingProductFamily.action 0 5 6 7 8 9 10 11 12).imp
        ((Source.SetLanguage.edge 12 13 14).imp
          ((Source.SetLanguage.edge 11 15 16).imp
            ((bit 10 14 16 17 18).iff (bit 10 13 15 17 18))))))).close

theorem move_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence moveSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hpi hA hpq hjj
  have h := bit_move (alpha := env 17) (b := env 18) hM
    ((ForcingProductFamily.presentation_semantics (M := M) env 0 1 2 3 4 5 6 7 8 9 10).mp hp)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env 1 11).mp hpi)
    ((ForcingProductFamily.action_semantics (M := M) env 0 5 6 7 8 9 10 11 12).mp hA)
    ((KuratowskiZF.source_edge (M := M) env 12 13 14).mp hpq)
    ((KuratowskiZF.source_edge (M := M) env 11 15 16).mp hjj)
  constructor
  · intro hb
    exact (bit_semantics (M := M) env 10 13 15 17 18).mpr
      (h.mp ((bit_semantics (M := M) env 10 14 16 17 18).mp hb))
  · intro hb
    exact (bit_semantics (M := M) env 10 14 16 17 18).mpr
      (h.mpr ((bit_semantics (M := M) env 10 13 15 17 18).mp hb))

theorem move_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence moveSentence) :=
  ModelTransfer.derives (fun _ hM => move_models hM)

end PPAC.Migration.ForcingProductBits
