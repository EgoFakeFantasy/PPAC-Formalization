/- Pinned OrdinalCodes.FixedName.collect, selectedRankFixed,
selectedRank_fixed and selectionType_fixed. Consumes the SAME actual
internal rank graph and the existing collected HS/fixed producers. -/
import PPAC.Migration.ForcingOrdinalRanks
import PPAC.Migration.ForcingCollectedHS

namespace PPAC.Migration.ForcingOrdinalFixed
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingCollectedName (Collected)
open ForcingStabilizer (Action)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Fixed (v : Fin 7 → M.Carrier .set) (G F H name : M.Carrier .set) : Prop :=
  ForcingHS.HS actionFormula v G (v 6) F name ∧ ∀ g,
    (Project.FirstOrderSemantics.reduct M).mem g H → ∀ a,
    MapRel actionFormula v g a → Action (v 6) a name name

def fixed {m : Nat} (ra : Fin 7 → Fin m) (G F H name : Fin m) : Formula m :=
  (ForcingHS.hs actionFormula ra G (ra 6) F name).conj (.all
    ((Formula.mem (Fin.last m) H.castSucc).imp (.all
      ((rel actionFormula (paramsUp (paramsUp ra)) (Fin.last m).castSucc (Fin.last (m+1))).imp
        (ForcingStabilizer.action (ra 6).castSucc.castSucc (Fin.last (m+1))
          name.castSucc.castSucc name.castSucc.castSucc)))))

theorem fixed_semantics {m : Nat} (env : Fin m → M.Carrier .set) (ra : Fin 7 → Fin m)
    (G F H name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fixed ra G F H name) ↔
      Fixed (fun i => env (ra i)) (env G) (env F) (env H) (env name) := by
  simp only [fixed,Fixed,Formula.Realize,ForcingHS.hs_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingStabilizer.action_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def FixedAt (v : Fin 7 → M.Carrier .set) (G F H history i : M.Carrier .set) : Prop :=
  ∀ name, PureKuratowski.PairMember M i name history → Fixed v G F H name

def fixedAt {m : Nat} (ra : Fin 7 → Fin m) (G F H history i : Fin m) : Formula m :=
  .all ((Source.SetLanguage.edge history.castSucc i.castSucc (Fin.last m)).imp
    (fixed (paramsUp ra) G.castSucc F.castSucc H.castSucc (Fin.last m)))

theorem fixedAt_semantics {m : Nat} (env : Fin m → M.Carrier .set) (ra : Fin 7 → Fin m)
    (G F H history i : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fixedAt ra G F H history i) ↔
      FixedAt (fun j => env (ra j)) (env G) (env F) (env H) (env history) (env i) := by
  simp only [fixedAt,FixedAt,Formula.Realize,KuratowskiZF.source_edge,fixed_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def FixedFamily (v : Fin 7 → M.Carrier .set) (G F H J history : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → FixedAt v G F H history i

def fixedFamily {m : Nat} (ra : Fin 7 → Fin m) (G F H J history : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) J.castSucc).imp
    (fixedAt (paramsUp ra) G.castSucc F.castSucc H.castSucc history.castSucc (Fin.last m)))

theorem fixedFamily_semantics {m : Nat} (env : Fin m → M.Carrier .set) (ra : Fin 7 → Fin m)
    (G F H J history : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fixedFamily ra G F H J history) ↔
      FixedFamily (fun j => env (ra j)) (env G) (env F) (env H) (env J) (env history) := by
  simp only [fixedFamily,FixedFamily,Formula.Realize,fixedAt_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Source hR: the index stays literally fixed; only its condition moves. -/
def Invariant {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (H X : M.Carrier .set) : Prop :=
  ∀ g a i p q, (Project.FirstOrderSemantics.reduct M).mem g H →
    MapRel actionFormula v g a → (Project.FirstOrderSemantics.reduct M).mem i X →
    (Project.FirstOrderSemantics.reduct M).mem p (v 6) → PureKuratowski.PairMember M p q a →
    MapRel R env i p → MapRel R env i q

def invariant {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m)
    (ra : Fin 7 → Fin m) (H X : Fin m) : Formula m :=
  let r5 := paramsUp (paramsUp (paramsUp (paramsUp (paramsUp rho))))
  let a5 := paramsUp (paramsUp (paramsUp (paramsUp (paramsUp ra))))
  let g := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let a := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let i := (Fin.last (m+2)).castSucc.castSucc
  let p := (Fin.last (m+3)).castSucc
  let q := Fin.last (m+4)
  .all (.all (.all (.all (.all ((Formula.mem g H.castSucc.castSucc.castSucc.castSucc.castSucc).imp
    ((rel actionFormula a5 g a).imp ((Formula.mem i X.castSucc.castSucc.castSucc.castSucc.castSucc).imp
      ((Formula.mem p (a5 6)).imp ((Source.SetLanguage.edge a p q).imp
        ((rel R r5 i p).imp (rel R r5 i q)))))))))))

theorem invariant_semantics {n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m) (H X : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (invariant R rho ra H X) ↔
      Invariant R (fun j => env (rho j)) (fun j => env (ra j)) (env H) (env X) := by
  simp only [invariant,Invariant,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    KuratowskiZF.source_edge,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Exact use of FixedName.collect: same index, same child, moved condition. -/
theorem collected_fixed (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H J history name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H)
    (hHF : (Project.FirstOrderSemantics.reduct M).mem H F)
    (hFamily : FixedFamily v G F H J history) (hInvariant : Invariant R env v H J)
    (hn : Collected R env J history (v 6) name) : Fixed v G F H name := by
  have hHS : ForcingCollectedHS.FamilyHS v G (v 6) F J history :=
    fun i child hi hic => (hFamily i hi child hic).1
  have hPerm := (ForcingCollectedHS.indexed_permutes_iff hM R env v H J history).mp (by
    intro g hg a hga i child p hi hic hp hR
    have ha := ForcingProductFamily.action_permutation ((mapRel_action v g a).mp hga)
    obtain ⟨q,hpq,_⟩ := ha.1.1.2 p hp
    exact ⟨i,child,q,hi,hic,hInvariant g a i p q hg hga hi hp hpq hR,
      (hFamily i hi child hic).2 g hg a hga,hpq⟩)
  exact ⟨ForcingCollectedHS.collect_HS hM R env v hp hG hF hH hHF hHS hPerm hn,
    fun g hg a hga => ForcingCollectedHS.fixed hM R env v hp hG hH hHS hPerm hn hg hga⟩

/-- The accepted rank equation IS the existing collect on the internal predecessor set. -/
theorem rank_collected (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set}
    {X order P history a value J : M.Carrier .set}
    (hRanks : ForcingOrdinalRanks.Ranks R env X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (hav : PureKuratowski.PairMember M a value history)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsPredecessorSet
      (KuratowskiZF.interpretation hM) J order X a) : Collected R env J history P value := by
  intro z
  rw [hRanks.2 a value ha hav z]
  constructor
  · rintro ⟨child,p,⟨hp,b,hb,hba,hbc,hR⟩,hc⟩
    exact ⟨child,p,⟨hp,b,(hJ b).mpr ⟨hb,hba⟩,hbc,hR⟩,hc⟩
  · rintro ⟨child,p,⟨hp,b,hb,hbc,hR⟩,hc⟩
    exact ⟨child,p,⟨hp,b,((hJ b).mp hb).1,((hJ b).mp hb).2,hbc,hR⟩,hc⟩

theorem ranks_fixed (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H X order history : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H)
    (hHF : (Project.FirstOrderSemantics.reduct M).mem H F)
    (hInvariant : Invariant R env v H X)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : ForcingOrdinalRanks.Ranks R env X order (v 6) history) :
    FixedFamily v G F H X history := by
  let inputs : Fin 11 → M.Carrier .set := Fin.lastCases history (Fin.lastCases H (Fin.lastCases F (Fin.lastCases G v)))
  let query : Formula 12 := (fixedAt (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc) 7 8 9 10 11).imp .bot
  have hq : ∀ a, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases a inputs) query ↔ ¬ FixedAt v G F H history a := by
    intro a
    simp only [query,Formula.Realize,fixedAt_semantics (M := M),inputs,Fin.lastCases_castSucc]
    rfl
  have hsep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨bad,hBad⟩ := hsep inputs X
  apply hOrder.induction (ModelTransfer.extensionality hM) (FixedAt v G F H history)
    ⟨bad,fun a => (hBad a).trans (and_congr Iff.rfl (hq a))⟩
  intro a ha ih value hav
  obtain ⟨J,hJ⟩ := ZF.exists_wellOrderPredecessorSet (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) order X a
  apply collected_fixed hM R env v hp hG hF hH hHF
    (fun b hb => ih b ((hJ b).mp hb).1 ((hJ b).mp hb).2)
    (fun g act i p q hg hga hi hp hpq hR => hInvariant g act i p q hg hga ((hJ i).mp hi).1 hp hpq hR)
    (rank_collected hM hRanks ha hav hJ)

/-- Joint source construction: all ranks and the total type share H literally. -/
theorem exists_fixed_ranks (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H X order : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H)
    (hHF : (Project.FirstOrderSemantics.reduct M).mem H F)
    (hInvariant : Invariant R env v H X)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X) :
    ∃ history selection, ForcingOrdinalRanks.Ranks R env X order (v 6) history ∧
      Collected R env X history (v 6) selection ∧ FixedFamily v G F H X history ∧ Fixed v G F H selection := by
  obtain ⟨history,selection,hr,hs,_,_⟩ := ForcingOrdinalRanks.ranks_and_type_exists hM R env (v 6) hOrder
  have hf := ranks_fixed hM R env v hp hG hF hH hHF hInvariant hOrder hr
  exact ⟨history,selection,hr,hs,hf,collected_fixed hM R env v hp hG hF hH hHF hf hInvariant hs⟩

def context {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X : Fin m) : Formula m :=
  (ForcingProductFamily.presentation (ra 0) I K B w (ra 1) (ra 2) (ra 3) (ra 4) (ra 5) (ra 6)).conj
    ((ForcingLabelPermutations.carrier I G).conj ((ForcingNormalFilter.normal I G F).conj
      ((ForcingConjugationGraph.subgroup I G H).conj ((Formula.mem H F).conj (invariant R rho ra H X)))))

theorem context_semantics {n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m) (I K B w G F H X : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (context R rho ra I K B w G F H X) ↔
      Presentation (env (ra 0)) (env I) (env K) (env B) (env w) (env (ra 1)) (env (ra 2))
        (env (ra 3)) (env (ra 4)) (env (ra 5)) (env (ra 6)) ∧
      ForcingLabelPermutations.Carrier (env I) (env G) ∧ ForcingNormalFilter.Normal (env I) (env G) (env F) ∧
      ForcingConjugationGraph.Subgroup (env I) (env G) (env H) ∧
      (Project.FirstOrderSemantics.reduct M).mem (env H) (env F) ∧
      Invariant R (fun j => env (rho j)) (fun j => env (ra j)) (env H) (env X) := by
  simp only [context,Formula.Realize,ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),invariant_semantics (M := M)]

/-- Original pure-membership statement; all source action/filter premises remain explicit. -/
def constructionSentence {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (ProjectSyntax.encode id (context R rho ra I K B w G F H X)) (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (.existsE (.existsE (.conj
      (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks R (fun j => (rho j).succ.succ)
        X.succ.succ order.succ.succ (ra 6).succ.succ 1)) (.conj
      (ProjectSyntax.encode id (ForcingCollectedName.collected R (fun j => (rho j).succ.succ)
        X.succ.succ 1 (ra 6).succ.succ 0)) (.conj
      (ProjectSyntax.encode id (fixedFamily (fun j => (ra j).succ.succ)
        G.succ.succ F.succ.succ H.succ.succ X.succ.succ 1))
      (ProjectSyntax.encode id (fixed (fun j => (ra j).succ.succ)
        G.succ.succ F.succ.succ H.succ.succ 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem construction_models {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence R rho ra I K B w G F H X order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),context_semantics (M := M),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    fixedFamily_semantics (M := M),fixed_semantics (M := M)]
  rintro ⟨hp,hG,hF,hH,hHF,hInvariant⟩ hOrder
  exact exists_fixed_ranks hM R (fun j => bound (rho j)) (fun j => bound (ra j))
    hp hG hF hH hHF hInvariant hOrder

theorem construction_kernel_certificate {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence R rho ra I K B w G F H X order)) :=
  ModelTransfer.derives (fun _ hM => construction_models R rho ra I K B w G F H X order hM)

end PPAC.Migration.ForcingOrdinalFixed
