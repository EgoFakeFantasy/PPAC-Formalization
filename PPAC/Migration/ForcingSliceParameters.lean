/- Pinned SliceAssembly.presentation_reverse_injection parameter v(i)
[actual Ypart(i), actual Spart(i)]. The EXISTING UniformMaximum.Inputs accepts
an internal definable functional relation directly. No redundant separate
FunctionOn graph, external choice function, or new parameter-family engine. -/
import PPAC.Migration.ForcingSliceGeometry

namespace PPAC.Migration.ForcingSliceParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem args3_map {a : Type v} {b : Type u} (g : a → b) (f X Y : a) :
    (fun j => g (args3 f X Y j)) = args3 (g f) (g X) (g Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- SAME nine constructor fields as the accepted Pieces existential, with
its three already constructed names exposed for the concrete consumer. -/
def PiecesWith {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) (i ci Bi Yi Si : M.Carrier .set) : Prop :=
  let e : Fin (k+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i env)
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr : Fin 7 → Fin (k+2) := fun j => b (rho j)
  HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Bi ∧
  Supported (fun j => env (rho j)) (env S) Bi ∧
  ForcingSliceSelection.Selected (orderFormula (rr 0) (b mul))
    (ForcingSliceGeometry.BPredicate rr (b G) (b F) (b mul) (b s) (b A) (b X) (Fin.last (k+1)))
    e (env (rho 6)) (env X) Bi ∧
  HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Yi ∧
  Supported (fun j => env (rho j)) (env S) Yi ∧
  ForcingSliceSelection.Selected (orderFormula (rr 0) (b mul))
    (ForcingSliceGeometry.YPredicate rr (b G) (b F) (b mul) (b top) (b O) (b f) (b s) (b A) (b X) (b Y) (Fin.last k).castSucc)
    e (env (rho 6)) (env Y) Yi ∧
  HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Si ∧
  Supported (fun j => env (rho j)) (env S) Si ∧
  ForcingSeparation.Separated (orderFormula (rr 0) (b mul)) (ForcingPairUnion.domain rr (b G) (b F))
    e (args3 (env f) Bi Yi) (env (rho 6)) Bi Si ForcingSliceGeometry.preimageFormula

def Spec {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) (i : M.Carrier .set) (v : Fin 2 → M.Carrier .set) : Prop :=
  ∃ ci, ForcingCheckName.Checked (env top) i ci ∧ ∃ Bi,
    PiecesWith env rho G F S mul top O f s A X Y i ci Bi (v 0) (v 1)

/-- Small quotation over ABSTRACT predicates. Keeping the large source
forcing formulas opaque during this binder proof avoids kernel expansion. -/
private def coreFormula {k : Nat} (H Fixed : Formula (k+1)) (C : Formula (k+2))
    (R QB QY : Formula (k+2+2)) (HF : Formula (k+2+1)) (f P X Y : Fin k) (phi : Formula 4) : Formula (k+1+2) :=
  let up : Fin k → Fin (k+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let i := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let Yi := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let Si := (Fin.last (k+2)).castSucc.castSucc
  let ci := (Fin.last (k+3)).castSucc
  let Bi := Fin.last (k+4)
  let base : Fin (k+2) → Fin (k+5) := Fin.lastCases ci (Fin.lastCases i up)
  .ex (.ex ((ReplacementPredicates.rel C up i ci).conj
    ((MinimalPredicates.pred H up Bi).conj ((MinimalPredicates.pred Fixed up Bi).conj
      ((ForcingSliceSelection.selected R QB base (up P) (up X) Bi).conj
        ((MinimalPredicates.pred H up Yi).conj ((MinimalPredicates.pred Fixed up Yi).conj
          ((ForcingSliceSelection.selected R QY base (up P) (up Y) Yi).conj
            ((MinimalPredicates.pred H up Si).conj ((MinimalPredicates.pred Fixed up Si).conj
              (ForcingSeparation.separated R HF base (args3 (up f) Bi Yi) (up P) Bi Si phi)))))))))))

private theorem parameter_two {k : Nat} (env : Fin k → M.Carrier .set)
    (Q : Formula (k+1+2)) (i : M.Carrier .set) (v : Fin 2 → M.Carrier .set) :
    ForcingUniformMaximum.ParameterSpec (M := M) env Q i v ↔
      Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
        (Fin.lastCases (v 1) (Fin.lastCases (v 0) (Fin.lastCases i env))) Q := by
  rfl

private theorem core_spec {k : Nat} (env : Fin k → M.Carrier .set)
    (H Fixed : Formula (k+1)) (C : Formula (k+2))
    (R QB QY : Formula (k+2+2)) (HF : Formula (k+2+1)) (f P X Y : Fin k) (phi : Formula 4)
    (i : M.Carrier .set) (v : Fin 2 → M.Carrier .set) :
    ForcingUniformMaximum.ParameterSpec (M := M) env (coreFormula H Fixed C R QB QY HF f P X Y phi) i v ↔
      ∃ ci, ForcingMapConditions.MapRel C env i ci ∧ ∃ Bi,
        ForcingClassEvaluation.Predicate H env Bi ∧ ForcingClassEvaluation.Predicate Fixed env Bi ∧
        ForcingSliceSelection.Selected R QB (Fin.lastCases ci (Fin.lastCases i env)) (env P) (env X) Bi ∧
        ForcingClassEvaluation.Predicate H env (v 0) ∧ ForcingClassEvaluation.Predicate Fixed env (v 0) ∧
        ForcingSliceSelection.Selected R QY (Fin.lastCases ci (Fin.lastCases i env)) (env P) (env Y) (v 0) ∧
        ForcingClassEvaluation.Predicate H env (v 1) ∧ ForcingClassEvaluation.Predicate Fixed env (v 1) ∧
        ForcingSeparation.Separated R HF (Fin.lastCases ci (Fin.lastCases i env)) (args3 (env f) Bi (v 0))
          (env P) Bi (v 1) phi := by
  refine (parameter_two env _ i v).trans ?_
  let up : Fin k → Fin (k+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let base : Fin (k+2) → Fin (k+5) := Fin.lastCases (Fin.last (k+3)).castSucc
    (Fin.lastCases (Fin.last k).castSucc.castSucc.castSucc.castSucc up)
  have hEnv (ci Bi : M.Carrier .set) :
      (fun j => Fin.lastCases Bi (Fin.lastCases ci (Fin.lastCases (v 1) (Fin.lastCases (v 0) (Fin.lastCases i env)))) (base j)) =
        Fin.lastCases ci (Fin.lastCases i env) := by
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp only [base,Fin.lastCases_last,Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · simp only [base,Fin.lastCases_last,Fin.lastCases_castSucc]
      · simp only [base,up,Fin.lastCases_castSucc]
  dsimp only [base,up] at hEnv
  simp only [coreFormula,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingSliceSelection.selected_semantics (M := M),
    ForcingSeparation.separated_semantics (M := M),args3_map,hEnv,Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · rintro ⟨ci,Bi,hCi,hParts⟩
    exact ⟨ci,hCi,Bi,hParts⟩
  · rintro ⟨ci,hCi,Bi,hParts⟩
    exact ⟨ci,Bi,hCi,hParts⟩

private def fixedPredicate {k : Nat} (rho : Fin 7 → Fin k) (S : Fin k) : Formula (k+1) :=
  ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc) S.castSucc (Fin.last k)

private theorem fixedPredicate_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (S : Fin k) (x : M.Carrier .set) :
    ForcingClassEvaluation.Predicate (fixedPredicate rho S) env x ↔ Supported (fun j => env (rho j)) (env S) x := by
  simp only [ForcingClassEvaluation.Predicate,fixedPredicate,ForcingEquivariantMix.fixedAll_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

private def checkPredicate {k : Nat} (top : Fin k) : Formula (k+2) :=
  ForcingCheckName.checkName top.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))

private theorem checkPredicate_semantics {k : Nat} (env : Fin k → M.Carrier .set) (top : Fin k)
    (i ci : M.Carrier .set) :
    ForcingMapConditions.MapRel (checkPredicate top) env i ci ↔ ForcingCheckName.Checked (env top) i ci := by
  simp only [ForcingMapConditions.MapRel,checkPredicate,ForcingCheckName.checkName_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Exactly the actual [Ypart_i,Spart_i] parameters required by the source. -/
def parameterFormula {k : Nat} (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y : Fin k) : Formula (k+1+2) :=
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr : Fin 7 → Fin (k+2) := fun j => b (rho j)
  coreFormula (ForcingPairUnion.domain rho G F) (fixedPredicate rho S) (checkPredicate top)
    (orderFormula (rr 0) (b mul))
    (ForcingSliceGeometry.BPredicate rr (b G) (b F) (b mul) (b s) (b A) (b X) (Fin.last (k+1)))
    (ForcingSliceGeometry.YPredicate rr (b G) (b F) (b mul) (b top) (b O) (b f) (b s) (b A) (b X) (b Y) (Fin.last k).castSucc)
    (ForcingPairUnion.domain rr (b G) (b F)) f (rho 6) X Y ForcingSliceGeometry.preimageFormula

set_option maxHeartbeats 30000 in
theorem parameter_spec_iff {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) (i : M.Carrier .set) (v : Fin 2 → M.Carrier .set) :
    ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v ↔
      Spec env rho G F S mul top O f s A X Y i v := by
  unfold parameterFormula
  refine (core_spec env _ _ _ _ _ _ _ _ _ _ _ _ i v).trans ?_
  simp only [Spec,PiecesWith,ForcingPairUnion.domain_semantics (M := M),fixedPredicate_semantics,checkPredicate_semantics]

theorem parameter_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j)))
    (hFixed : ∀ j, Supported (fun a => env (rho a)) (env S) (env (ForcingMapCalculus.five f s A X Y j)))
    (i : M.Carrier .set) :
    ∃ v, ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v := by
  obtain ⟨ci,hCi⟩ := ForcingCheckName.exists_checked hM (env top) i
  let e : Fin (k+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i env)
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr : Fin 7 → Fin (k+2) := fun j => b (rho j)
  have eu (a : Fin k) : e (b a) = env a := by simp only [e,b,Fin.lastCases_castSucc]
  have hFixed' (j : Fin 5) : Supported (fun a => e (rr a)) (e (b S))
      (e (ForcingMapCalculus.five (b f) (b s) (b A) (b X) (b Y) j)) := by
    have hm : (fun j => e (ForcingMapCalculus.five (b f) (b s) (b A) (b X) (b Y) j)) =
        (fun j => env (ForcingMapCalculus.five f s A X Y j)) := by
      funext j
      exact Fin.cases (eu f) (Fin.cases (eu s) (Fin.cases (eu A) (Fin.cases (eu X) (Fin.cases (eu Y) (fun t => Fin.elim0 t))))) j
    simpa only [rr,eu,congrFun hm j] using hFixed j
  obtain ⟨Bi,Yi,Si,hBi,hFixBi,hB,hYi,hFixYi,hYP,hSi,hFixSi,hSP⟩ := ForcingSliceGeometry.construct_pieces hM e rr
    (b I) (b K) (b B) (b w) (b G) (b F) (b S) (b mul) (b top) (b O) (b f) (b s) (b A) (b X) (b Y)
    (Fin.last k).castSucc (Fin.last (k+1))
    (by simpa only [rr,eu] using hPres) (by simpa only [eu] using hG) (by simpa only [eu] using hF)
    (by simpa only [eu] using hS) (by simpa only [eu] using hSF) (by simpa only [eu] using ht)
    (by simpa only [rr,eu,ForcingMapCalculus.five,Fin.cases_zero] using hNames 0)
    (by simpa only [rr,eu,ForcingMapCalculus.five,args3,args2,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ (Fin.succ 0))))
    (by simpa only [rr,eu,ForcingMapCalculus.five,args3,args2,args1,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) hFixed'
    (by simpa only [e,b,Fin.lastCases_last,Fin.lastCases_castSucc] using hCi)
  refine ⟨args2 Yi Si,(parameter_spec_iff env rho G F S mul top O f s A X Y i _).mpr ⟨ci,hCi,Bi,?_⟩⟩
  simpa only [PiecesWith,rr,eu,args2,args1,Fin.cases_zero,show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ]
    using And.intro hBi (And.intro hFixBi (And.intro hB (And.intro hYi (And.intro hFixYi
      (And.intro hYP (And.intro hSi (And.intro hFixSi hSP)))))))


/-- The accepted raw-edge extensionality proof, verbatim, now consuming the
existing Separated equation needed for source parameter functionality. -/
private theorem separated_unique (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin n → M.Carrier .set} {P X name name' : M.Carrier .set} {phi : Formula (n+1)}
    (hn : ForcingNames.IsName P name) (hn' : ForcingNames.IsName P name')
    (hc : ForcingSeparation.Separated R H env v P X name phi)
    (hc' : ForcingSeparation.Separated R H env v P X name' phi) : name = name' := by
  have hsub {a b : M.Carrier .set} (ha : ForcingNames.IsName P a)
      (he : ∀ child p, PureKuratowski.PairMember M child p a → PureKuratowski.PairMember M child p b) :
      ForcingPowerName.Subset a b := by
    intro z hz
    obtain ⟨child,p,hcode,_,_⟩ := ForcingNames.edges ha z hz
    obtain ⟨z',hcode',hz'⟩ := he child p ⟨z,hcode,hz⟩
    exact (KuratowskiZF.code_unique hM hcode hcode').symm ▸ hz'
  exact (ModelTransfer.extensionality hM).eq_of_same_members name name' (fun z =>
    ⟨hsub hn (fun child p he => (hc' child p).mpr ((hc child p).mp he)) z,
      hsub hn' (fun child p he => (hc child p).mpr ((hc' child p).mp he)) z⟩)

theorem parameter_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y : Fin k)
    {i : M.Carrier .set} {v v' : Fin 2 → M.Carrier .set}
    (h : ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v)
    (h' : ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v') : v = v' := by
  obtain ⟨ci,hCi,Bi,hBi,_hFixBi,hB,hYi,_hFixYi,hYP,hSi,_hFixSi,hSP⟩ :=
    (parameter_spec_iff env rho G F S mul top O f s A X Y i v).mp h
  obtain ⟨ci',hCi',Bi',hBi',_hFixBi',hB',hYi',_hFixYi',hYP',hSi',_hFixSi',hSP'⟩ :=
    (parameter_spec_iff env rho G F S mul top O f s A X Y i v').mp h'
  have hc := ForcingCheckName.unique hM hCi hCi'
  subst ci'
  have hb := ForcingSliceSelection.unique hM (ForcingHS.isName hBi) (ForcingHS.isName hBi') hB hB'
  subst Bi'
  have hy := ForcingSliceSelection.unique hM (ForcingHS.isName hYi) (ForcingHS.isName hYi') hYP hYP'
  rw [← hy] at hSP'
  have hs := separated_unique hM (ForcingHS.isName hSi) (ForcingHS.isName hSi') hSP hSP'
  funext j
  exact Fin.cases hy (Fin.cases hs (fun t => Fin.elim0 t)) j

theorem parameter_fixed {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) {i : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (h : ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v) :
    ∀ j, Supported (fun a => env (rho a)) (env S) (v j) := by
  obtain ⟨ci,_hCi,Bi,_hBi,_hFixBi,_hB,_hYi,hFixYi,_hYP,_hSi,hFixSi,_hSP⟩ :=
    (parameter_spec_iff env rho G F S mul top O f s A X Y i v).mp h
  intro j
  exact Fin.cases hFixYi (Fin.cases hFixSi (fun t => Fin.elim0 t)) j

theorem parameter_hs {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) {i : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (h : ForcingUniformMaximum.ParameterSpec (M := M) env (parameterFormula rho G F S mul top O f s A X Y) i v) :
    ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (v j) := by
  obtain ⟨ci,_hCi,Bi,_hBi,_hFixBi,_hB,hYi,_hFixYi,_hYP,hSi,_hFixSi,_hSP⟩ :=
    (parameter_spec_iff env rho G F S mul top O f s A X Y i v).mp h
  intro j
  exact Fin.cases hYi (Fin.cases hSi (fun t => Fin.elim0 t)) j


private theorem parameter_pair {k : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+1+2))
    (i x y : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds Q env i x y ↔
      ForcingUniformMaximum.ParameterSpec (M := M) env Q i (args2 x y) := by
  simpa only [ForcingRelationGraphForcing.Holds,args2,args1,show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_zero,Fin.cases_succ]
    using (parameter_two env Q i (args2 x y)).symm

private def hasParameters {k : Nat} (Q : Formula (k+3)) (i : Fin k) : Formula k :=
  .ex (.ex (ForcingRelationGraphSupport.relation Q (fun j => j.castSucc.castSucc)
    i.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))))

private theorem hasParameters_semantics {k : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+3)) (i : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (hasParameters Q i) ↔
      ∃ x y, ForcingRelationGraphForcing.Holds Q env (env i) x y := by
  simp only [hasParameters,Formula.Realize,ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Full object contract for the EXISTING UniformMaximum parameter input:
internal totality, literal uniqueness, HS and SAME-support fixedness. The
source injection-existence input remains the actual slice_candidate task. -/
def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i a b a' b' : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F s),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho S (ForcingMapCalculus.five f s A X Y)),
      .mem (.bound i) (.bound O)].foldr Definitional.Formula.imp
      (.conj (ProjectSyntax.encode id (hasParameters (parameterFormula rho G F S mul top O f s A X Y) i))
        (.imp (ProjectSyntax.encode id (ForcingRelationGraphSupport.relation (parameterFormula rho G F S mul top O f s A X Y) id i a b))
          (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F a))
            (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F b))
              (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S a))
                (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S b))
                  (.imp (ProjectSyntax.encode id (ForcingRelationGraphSupport.relation (parameterFormula rho G F S mul top O f s A X Y) id i a' b'))
                    (ProjectSyntax.encode id ((Formula.equal a a').conj (Formula.equal b b')))))))))))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i a b a' b' : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S mul top O f s A X Y i a b a' b')).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingHS.hs_semantics,ForcingSupportingRoot.tupleSupported_semantics,
    ForcingRelationGraphSupport.relation_semantics,ForcingEquivariantMix.fixedAll_semantics,
    hasParameters_semantics,id_eq]
  intro hPres hG hF hS hSF ht hf hs hA hX hY hFixed _hi
  have hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j)) := by
    intro j
    exact Fin.cases hf (Fin.cases hs (Fin.cases hA (Fin.cases hX (Fin.cases hY (fun t => Fin.elim0 t))))) j
  constructor
  · obtain ⟨v,hv⟩ := parameter_exists hM env rho I K B w G F S mul top O f s A X Y
      hPres hG hF hS hSF ht hNames hFixed (env i)
    exact ⟨v 0,v 1,(parameter_two env _ (env i) v).mp hv⟩
  · intro hAB
    have hv := (parameter_pair env _ (env i) (env a) (env b)).mp hAB
    have hvHS := parameter_hs env rho G F S mul top O f s A X Y hv
    have hvFixed := parameter_fixed env rho G F S mul top O f s A X Y hv
    refine ⟨hvHS 0,hvHS (Fin.succ 0),hvFixed 0,hvFixed (Fin.succ 0),?_⟩
    intro hAB'
    have hv' := (parameter_pair env _ (env i) (env a') (env b')).mp hAB'
    have he := parameter_unique hM env rho G F S mul top O f s A X Y hv hv'
    exact ⟨congrFun he 0,congrFun he (Fin.succ 0)⟩

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i a b a' b' : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F S mul top O f s A X Y i a b a' b')) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S mul top O f s A X Y i a b a' b' hM)

end PPAC.Migration.ForcingSliceParameters
