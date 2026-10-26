/- Actual internal offset/scale/outsideBound graphs for source heightIntervals.
Use the existing native definable-function constructor and canonical interval
choices; no object choice function or host family of selected witnesses. -/
import PPAC.Migration.ConstructionProbeIntervalChoices

namespace PPAC.Migration.ConstructionProbeHeightIntervalGraphs
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionProbeIntervalChoices
open ConstructionProbeLetterIntervals (UniformMargins)
open ConstructionProbeLetterFloor (FloorLaws)
open ConstructionProbeCostBounds (CostBounds)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The three fixed fields of the source record; no witness extraction. -/
def project {α : Type v} (i : Fin 3) (offset delta bound : α) : α :=
  if i = 0 then offset else if i = 1 then delta else bound

def Selected (i : Fin 3) (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four D mul K E H C F s value : M.Carrier .set) : Prop := ∃ offset delta bound,
  Choice hM w Q four D mul K E H C F s offset delta bound ∧ value = project i offset delta bound

def Graph (i : Fin 3) (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four D mul S K E H C F G : M.Carrier .set) : Prop := ∀ s value,
  PureKuratowski.PairMember M s value G ↔ (Project.FirstOrderSemantics.reduct M).mem s S ∧
    Selected i hM w Q four D mul K E H C F s value

def Laws (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four D mul S A K E H C F O L B : M.Carrier .set) : Prop := ∀ s offset delta bound,
  PureKuratowski.PairMember M s offset O → PureKuratowski.PairMember M s delta L →
    PureKuratowski.PairMember M s bound B → Valid hM w Q four D mul S A K E H C F s offset delta bound

/-- The exact inside-cost field of HeightIntervals, with the actual difference
cut and its additive equation rather than only a one-sided bound. -/
def InsideBounds (hM : FirstOrder.Theory.Models M nativeZF) (w Q D mul S A H C F : M.Carrier .set) : Prop :=
  ∀ s floor x d hx cd, PureKuratowski.PairMember M s floor F →
    (Project.FirstOrderSemantics.reduct M).mem x D → (Project.FirstOrderSemantics.reduct M).mem d D →
    ConstructionProbeAlphabet.InCone S A x s → ConstructionProbeAlphabet.InCone S A d s →
    ¬ ConstructionBaseMonoid.Divides D mul d x → PureKuratowski.PairMember M x hx H →
    PureKuratowski.PairMember M d cd C → ∃ gap, Cut hM w Q gap ∧
      ConstructionCutDifference.Value hM w Q hx floor gap ∧ ConstructionCutAddition.SumCut hM w Q hx gap floor ∧ Subset cd gap

theorem inside_bounds (hM : FirstOrder.Theory.Models M nativeZF) {w Q R D mul S A K H C F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hCost : CostBounds hM w Q D mul S A K H C F) : InsideBounds hM w Q D mul S A H C F := by
  intro s floor x d hx cd hfs hxD hdD hxs hds hdx hxh hdc
  have hBound := ((hCost s floor hfs).1 x d hx cd hxD hdD hxs hds hdx hxh hdc).2
  obtain ⟨sum,_,hSum,hLe⟩ := hBound
  have hHX := (hR hx).mp (hH.2 x hx hxh)
  have hCD := (hR cd).mp (hC.2 d cd hdc)
  have hFloor := (hR floor).mp (hF.2 s floor hfs)
  have hHXFloor : Subset hx floor := fun p hp => hLe p ((ConstructionCutArithmetic.sum_contains hHX hCD hSum).1 p hp)
  obtain ⟨gap,hGap,hValue,hGapSum,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hHX hFloor hHXFloor
  have hCDGap := (ConstructionCutDifference.sum_le_iff hM hw hQ hCD hGap hHX
    (ConstructionCutArithmetic.sum_comm hM hw hSum) (ConstructionCutArithmetic.sum_comm hM hw hGapSum)).mp hLe
  exact ⟨gap,hGap,hValue,hGapSum,hCDGap⟩

def selected {m : Nat} (i : Fin 3) (w Q four D mul K E H C F s value : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (ConstructionProbeIntervalChoices.choice w.succ.succ.succ Q.succ.succ.succ four.succ.succ.succ
      D.succ.succ.succ mul.succ.succ.succ K.succ.succ.succ E.succ.succ.succ H.succ.succ.succ
      C.succ.succ.succ F.succ.succ.succ s.succ.succ.succ 2 1 0)
    (Project.Formula.extensionalEq (.bound value.succ.succ.succ) (.bound (project i (2 : Fin (m+3)) 1 0))))))

theorem selected_freeClosed {m : Nat} (i : Fin 3) (w Q four D mul K E H C F s value : Fin m) :
    (selected i w Q four D mul K E H C F s value).FreeClosed := by
  simp -implicitDefEqProofs [selected,Definitional.Formula.FreeClosed,ConstructionProbeIntervalChoices.choice_freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i : Fin 3)
    (w Q four D mul K E H C F s value : Fin m) :
    Project.Formula.satisfies env (selected i w Q four D mul K E H C F s value) ↔
      Selected i hM (env.bound w) (env.bound Q) (env.bound four) (env.bound D) (env.bound mul)
        (env.bound K) (env.bound E) (env.bound H) (env.bound C) (env.bound F) (env.bound s) (env.bound value) := by
  simp only [selected,Selected,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeIntervalChoices.choice_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp only [project,h0,h1,ite_true,ite_false] <;> rfl

theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four D mul S R K E H C F s value value' : M.Carrier .set} (i : Fin 3)
    (hK : MapsTo S D K) (hE : MapsTo S D E) (hH : MapsTo D R H) (hF : MapsTo S R F)
    (h : Selected i hM w Q four D mul K E H C F s value)
    (h' : Selected i hM w Q four D mul K E H C F s value') : value = value' := by
  obtain ⟨offset,delta,bound,hChoice,hValue⟩ := h
  obtain ⟨offset',delta',bound',hChoice',hValue'⟩ := h'
  obtain ⟨eu,ed,eb⟩ := choice_unique hM hK hE hH hF hChoice' hChoice
  subst offset'; subst delta'; subst bound'
  exact hValue.trans hValue'.symm

theorem selected_value (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four D mul S R K E H C F s value offset delta bound : M.Carrier .set} (i : Fin 3)
    (hK : MapsTo S D K) (hE : MapsTo S D E) (hH : MapsTo D R H) (hF : MapsTo S R F)
    (h : Selected i hM w Q four D mul K E H C F s value)
    (hChoice : Choice hM w Q four D mul K E H C F s offset delta bound) : value = project i offset delta bound :=
  selected_unique hM i hK hE hH hF h ⟨offset,delta,bound,hChoice,rfl⟩

/-- The native function constructor is applied to a unique definable relation,
not to an arbitrary family of existential witnesses. -/
theorem exists_coordinate_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four D mul S R K E H C F : M.Carrier .set} (i : Fin 3)
    (hR : CutCarrier hM w Q R) (hK : MapsTo S D K) (hE : MapsTo S D E) (hH : MapsTo D R H) (hF : MapsTo S R F)
    (hTotal : ∀ s, (Project.FirstOrderSemantics.reduct M).mem s S → ∃ offset delta bound,
      Choice hM w Q four D mul K E H C F s offset delta bound ∧
      Cut hM w Q offset ∧ Cut hM w Q delta ∧ Cut hM w Q bound) :
    ∃ G, MapsTo S R G ∧ Graph i hM w Q four D mul S K E H C F G := by
  let schema : Project.BinarySchema 10 := {
    body := selected i 2 3 4 5 6 7 8 9 10 11 1 0
    freeClosed := selected_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 10 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases four (Fin.cases D (Fin.cases mul
      (Fin.cases K (Fin.cases E (Fin.cases H (Fin.cases C (fun _ => F))))))))), free := fun _ => w }
  have he (s value : M.Carrier .set) : schema.denote env s value ↔ Selected i hM w Q four D mul K E H C F s value :=
    selected_semantics hM ((env.push s).push value) i 2 3 4 5 6 7 8 9 10 11 1 0
  obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := R) (by
      intro s hs
      obtain ⟨offset,delta,bound,hChoice,_,_,_⟩ := hTotal s hs
      exact ⟨project i offset delta bound,(he _ _).mpr ⟨offset,delta,bound,hChoice,rfl⟩⟩) (by
      intro s _ value value' hv hv'
      exact selected_unique hM i hK hE hH hF ((he _ _).mp hv) ((he _ _).mp hv')) (by
      intro s value hs hv
      obtain ⟨offset,delta,bound,hChoice,hu,hd,hb⟩ := hTotal s hs
      have eV := selected_value hM i hK hE hH hF ((he _ _).mp hv) hChoice
      apply (hR value).mpr
      rw [eV]
      by_cases h0 : i = 0
      · simpa [project,h0] using hu
      · by_cases h1 : i = 1
        · simpa [project,h0,h1] using hd
        · simpa [project,h0,h1] using hb)
  exact ⟨G,(ForcingSupportSize.native_mapsTo hM S R G).mpr hG,
    fun s value => (hGraph s value).trans (and_congr_right (fun _ => he s value))⟩

theorem exists_heightIntervals (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e d S A K E H C F one two three four : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hm : LeftCancelMonoid D mul e) (hConical : Conical D mul e)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (hK : MapsTo S D K) (hE : MapsTo S D E) (hExit : ConstructionProbeAlphabet.ExitGraph mul K d E)
    (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hFloor : FloorLaws D S A K H F) (hCost : CostBounds hM w Q D mul S A K H C F)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hDigits : ConstructionBaseWeights.Digits w one two three)
    (hFour : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hFourW : (Project.FirstOrderSemantics.reduct M).mem four w) :
    ∃ O L B, MapsTo S R O ∧ MapsTo S R L ∧ MapsTo S R B ∧
      Graph 0 hM w Q four D mul S K E H C F O ∧ Graph 1 hM w Q four D mul S K E H C F L ∧
      Graph 2 hM w Q four D mul S K E H C F B ∧ Laws hM w Q four D mul S A K E H C F O L B ∧
      InsideBounds hM w Q D mul S A H C F := by
  have hValid (s : M.Carrier .set) (hs : (Project.FirstOrderSemantics.reduct M).mem s S) :
      ∃ offset delta bound, Valid hM w Q four D mul S A K E H C F s offset delta bound :=
    exists_valid hM hw hQ hR hm hConical hd hne hK hE hExit hH hC hF hFloor hCost hUniform hDigits hFour hFourW hs
  have hTotal : ∀ s, (Project.FirstOrderSemantics.reduct M).mem s S → ∃ offset delta bound,
      Choice hM w Q four D mul K E H C F s offset delta bound ∧
      Cut hM w Q offset ∧ Cut hM w Q delta ∧ Cut hM w Q bound := by
    intro s hs
    obtain ⟨offset,delta,bound,hv⟩ := hValid s hs
    exact ⟨offset,delta,bound,valid_choice hv,valid_cuts hv⟩
  obtain ⟨O,hO,gO⟩ := exists_coordinate_graph hM 0 hR hK hE hH hF hTotal
  obtain ⟨L,hL,gL⟩ := exists_coordinate_graph hM 1 hR hK hE hH hF hTotal
  obtain ⟨B,hB,gB⟩ := exists_coordinate_graph hM 2 hR hK hE hH hF hTotal
  refine ⟨O,L,B,hO,hL,hB,gO,gL,gB,?_,inside_bounds hM hw hQ hR hH hC hF hCost⟩
  intro s offset delta bound ho hl hb
  obtain ⟨hs,hSelected⟩ := (gO s offset).mp ho
  obtain ⟨offset',delta',bound',hv⟩ := hValid s hs
  have hChoice := valid_choice hv
  have eu := selected_value hM 0 hK hE hH hF hSelected hChoice
  have ed := selected_value hM 1 hK hE hH hF ((gL s delta).mp hl).2 hChoice
  have eb := selected_value hM 2 hK hE hH hF ((gB s bound).mp hb).2 hChoice
  simp only [project,ite_true] at eu
  simp [project] at ed eb
  rw [eu,ed,eb]
  exact hv

end PPAC.Migration.ConstructionProbeHeightIntervalGraphs
