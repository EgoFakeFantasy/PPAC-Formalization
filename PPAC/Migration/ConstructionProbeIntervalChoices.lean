/- Canonical source interval choices: all source graph edges and the exact
missed-cost supremum are retained. This is the relation consumed by native
function construction, not a host choice of one witness per letter. -/
import PPAC.Migration.ConstructionProbeCostSupremum

namespace PPAC.Migration.ConstructionProbeIntervalChoices
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionProbeIntervals ConstructionProbeLetterIntervals
open ConstructionProbeCostSupremum (Cap)
open ConstructionProbeLetterFloor (FloorLaws)
open ConstructionProbeCostBounds (CostBounds)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Context (D mul K E H C F s floor t exit ht he c : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M s floor F ∧ PureKuratowski.PairMember M s t K ∧
    PureKuratowski.PairMember M s exit E ∧ PureKuratowski.PairMember M t ht H ∧
    PureKuratowski.PairMember M exit he H ∧ Cap D mul C t exit c

def Choice (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four D mul K E H C F s offset delta bound : M.Carrier .set) : Prop :=
  ∃ floor t exit ht he c, Context D mul K E H C F s floor t exit ht he c ∧
    Recipe hM w Q four floor ht he c offset delta bound

def Valid (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four D mul S A K E H C F s offset delta bound : M.Carrier .set) : Prop :=
  ∃ floor t exit ht he c, Context D mul K E H C F s floor t exit ht he c ∧
    Recipe hM w Q four floor ht he c offset delta bound ∧
    Interval hM w Q floor ht he c offset delta bound ∧ OutsideBound D mul S A C s exit bound

theorem valid_choice {hM : FirstOrder.Theory.Models M nativeZF}
    {w Q four D mul S A K E H C F s offset delta bound : M.Carrier .set}
    (h : Valid hM w Q four D mul S A K E H C F s offset delta bound) :
    Choice hM w Q four D mul K E H C F s offset delta bound := by
  obtain ⟨floor,t,exit,ht,he,c,hCtx,hRecipe,_,_⟩ := h
  exact ⟨floor,t,exit,ht,he,c,hCtx,hRecipe⟩

theorem valid_cuts {hM : FirstOrder.Theory.Models M nativeZF}
    {w Q four D mul S A K E H C F s offset delta bound : M.Carrier .set}
    (h : Valid hM w Q four D mul S A K E H C F s offset delta bound) :
    Cut hM w Q offset ∧ Cut hM w Q delta ∧ Cut hM w Q bound := by
  obtain ⟨_,_,_,_,_,_,_,_,hi,_⟩ := h
  exact ⟨hi.1,hi.2.1,hi.2.2.1⟩

theorem choice_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four D mul S R K E H C F s offset delta bound offset' delta' bound' : M.Carrier .set}
    (hK : MapsTo S D K) (hE : MapsTo S D E) (hH : MapsTo D R H) (hF : MapsTo S R F)
    (h : Choice hM w Q four D mul K E H C F s offset delta bound)
    (h' : Choice hM w Q four D mul K E H C F s offset' delta' bound') :
    offset = offset' ∧ delta = delta' ∧ bound = bound' := by
  obtain ⟨floor,t,exit,ht,he,c,hCtx,hRecipe⟩ := h
  obtain ⟨floor',t',exit',ht',he',c',hCtx',hRecipe'⟩ := h'
  obtain ⟨hfs,hkt,hexit,hht,hhe,hCap⟩ := hCtx
  obtain ⟨hfs',hkt',hexit',hht',hhe',hCap'⟩ := hCtx'
  have eF := ForcingConditionGraphs.function_unique hF.1 hfs' hfs
  subst floor'
  have eT := ForcingConditionGraphs.function_unique hK.1 hkt' hkt
  subst t'
  have eE := ForcingConditionGraphs.function_unique hE.1 hexit' hexit
  subst exit'
  have eHT := ForcingConditionGraphs.function_unique hH.1 hht' hht
  subst ht'
  have eHE := ForcingConditionGraphs.function_unique hH.1 hhe' hhe
  subst he'
  have eC := ConstructionProbeCostSupremum.cap_unique hM hCap' hCap
  subst c'
  exact recipe_unique hM hRecipe hRecipe'

/-- All data in the source recipe, including the old uniform cap, exist
canonically for each internal letter. No set of choice functions is assumed. -/
theorem exists_valid (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e d S A K E H C F one two three four s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hm : LeftCancelMonoid D mul e) (hConical : Conical D mul e)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (hK : MapsTo S D K) (hE : MapsTo S D E) (hExit : ConstructionProbeAlphabet.ExitGraph mul K d E)
    (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hFloor : FloorLaws D S A K H F) (hCost : CostBounds hM w Q D mul S A K H C F)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hDigits : ConstructionBaseWeights.Digits w one two three)
    (hFour : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hFourW : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) :
    ∃ offset delta bound, Valid hM w Q four D mul S A K E H C F s offset delta bound := by
  obtain ⟨floor,hfs,_⟩ := hF.1.2 s hs
  obtain ⟨t,hkt,_⟩ := hK.1.2 s hs
  obtain ⟨exit,hexit,_⟩ := hE.1.2 s hs
  obtain ⟨ht,hht,_⟩ := hH.1.2 t (hK.2 s t hkt)
  obtain ⟨he,hhe,_⟩ := hH.1.2 exit (hE.2 s exit hexit)
  obtain ⟨t',hkt',hProduct⟩ := (hExit s exit).mp hexit
  have eT := ForcingConditionGraphs.function_unique hK.1 hkt' hkt
  subst t'
  have hStrict := target_strict_exit hm hConical hd hne (hK.2 s t hkt) hProduct
  have hTargetCut := (hR ht).mp (hH.2 t ht hht)
  obtain ⟨c,tc,hc,hCap,hTC,hRoom,hMissed⟩ := ConstructionProbeCostSupremum.canonical_uniform hM hw hQ hR hC hTargetCut
    (hUniform t exit ht he hht hhe hStrict.1 hStrict.2)
  have hFloorCut := (hR floor).mp (hF.2 s floor hfs)
  have hExitCut := (hR he).mp (hH.2 exit he hhe)
  obtain ⟨offset,delta,bound,hRecipe,hInterval⟩ := exists_interval hM hw hQ hDigits hFour hFourW
    hFloorCut hTargetCut hExitCut hc ((hFloor s floor hfs).2.2 t ht hkt hht) hTC hRoom
  refine ⟨offset,delta,bound,floor,t,exit,ht,he,c,⟨hfs,hkt,hexit,hht,hhe,hCap⟩,hRecipe,hInterval,?_⟩
  intro x cx hx hcx hxe hNotCone
  by_cases hxt : Divides D mul x t
  · exact outside_target_bound hM hw hQ hFloorCut ((hR cx).mp (hC.2 x cx hcx)) hInterval
      ((hCost s floor hfs).2 t x ht cx hkt hx hxt hNotCone hht hcx).1
  · have hCopy := hInterval
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hCbound,_,_,_,_,_⟩ := hCopy
    exact fun p hp => hCbound p (hMissed x cx hx hcx hxe hxt p hp)

def context {m : Nat} (D mul K E H C F s floor t exit ht he c : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F s floor)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge K s t)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge E s exit))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge H t ht)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge H exit he)) (ConstructionProbeCostSupremum.cap D mul C t exit c))))))

theorem context_freeClosed {m : Nat} (D mul K E H C F s floor t exit ht he c : Fin m) : (context D mul K E H C F s floor t exit ht he c).FreeClosed := by
  simp -implicitDefEqProofs
  [context,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeCostSupremum.cap_freeClosed]

theorem context_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul K E H C F s floor t exit ht he c : Fin m) :
    Project.Formula.satisfies env (context D mul K E H C F s floor t exit ht he c) ↔
  Context (env.bound D) (env.bound mul) (env.bound K) (env.bound E) (env.bound H) (env.bound C) (env.bound
  F) (env.bound s) (env.bound floor) (env.bound t) (env.bound exit) (env.bound ht) (env.bound he)
  (env.bound c) := by
  simp only [context,Context,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeCostSupremum.cap_semantics
  hM]
  rfl

def choice {m : Nat} (w Q four D mul K E H C F s offset delta bound : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (context
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ s.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin
  (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (ConstructionProbeIntervalsSyntax.recipe
  w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ four.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6)) offset.succ.succ.succ.succ.succ.succ
  delta.succ.succ.succ.succ.succ.succ bound.succ.succ.succ.succ.succ.succ))))))))

theorem choice_freeClosed {m : Nat} (w Q four D mul K E H C F s offset delta bound : Fin m) : (choice w Q four D mul K E H C F s offset delta bound).FreeClosed := by
  simp -implicitDefEqProofs
  [choice,Definitional.Formula.FreeClosed,context_freeClosed,ConstructionProbeIntervalsSyntax.recipe_freeClosed]

theorem choice_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q four D mul K E H C F s offset delta bound : Fin m) :
    Project.Formula.satisfies env (choice w Q four D mul K E H C F s offset delta bound) ↔
  Choice hM (env.bound w) (env.bound Q) (env.bound four) (env.bound D) (env.bound mul) (env.bound K)
  (env.bound E) (env.bound H) (env.bound C) (env.bound F) (env.bound s) (env.bound offset) (env.bound
  delta) (env.bound bound) := by
  simp only
  [choice,Choice,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,context_semantics
  hM,ConstructionProbeIntervalsSyntax.recipe_semantics hM]
  rfl

def valid {m : Nat} (w Q four D mul S A K E H C F s offset delta bound : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (context
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ s.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin
  (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (.conj (ConstructionProbeIntervalsSyntax.recipe
  w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ four.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6)) offset.succ.succ.succ.succ.succ.succ
  delta.succ.succ.succ.succ.succ.succ bound.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionProbeIntervalsSyntax.interval w.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))
  offset.succ.succ.succ.succ.succ.succ delta.succ.succ.succ.succ.succ.succ
  bound.succ.succ.succ.succ.succ.succ) (ConstructionProbeIntervalsSyntax.outsideBound
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ s.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+6)) bound.succ.succ.succ.succ.succ.succ))))))))))

theorem valid_freeClosed {m : Nat} (w Q four D mul S A K E H C F s offset delta bound : Fin m) : (valid w Q four D mul S A K E H C F s offset delta bound).FreeClosed := by
  simp -implicitDefEqProofs
  [valid,Definitional.Formula.FreeClosed,context_freeClosed,ConstructionProbeIntervalsSyntax.recipe_freeClosed,ConstructionProbeIntervalsSyntax.interval_freeClosed,ConstructionProbeIntervalsSyntax.outsideBound_freeClosed]

theorem valid_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q four D mul S A K E H C F s offset delta bound : Fin m) :
    Project.Formula.satisfies env (valid w Q four D mul S A K E H C F s offset delta bound) ↔
  Valid hM (env.bound w) (env.bound Q) (env.bound four) (env.bound D) (env.bound mul) (env.bound S)
  (env.bound A) (env.bound K) (env.bound E) (env.bound H) (env.bound C) (env.bound F) (env.bound s)
  (env.bound offset) (env.bound delta) (env.bound bound) := by
  simp only
  [valid,Valid,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,context_semantics
  hM,ConstructionProbeIntervalsSyntax.recipe_semantics
  hM,ConstructionProbeIntervalsSyntax.interval_semantics
  hM,ConstructionProbeIntervalsSyntax.outsideBound_semantics hM]
  rfl

end PPAC.Migration.ConstructionProbeIntervalChoices
