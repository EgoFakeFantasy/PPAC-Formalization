/- Fixed UniformImages.nonwellorderable_image_bijection:243-276.
Consume the SAME existing ConcreteSystem Core/Outcome, actual image quotient,
and the literal source HS composition/inverse graph constructors. -/
import PPAC.Migration.ForcingMapCalculus
import PPAC.Migration.ForcingConcreteSystem

namespace PPAC.Migration.ForcingNonwellorderableImage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingPairUnion (domain domain_semantics)
open ForcingConcreteSystem (forcingRho)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private abbrev MapForce {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (f X Y p : M.Carrier .set) (phi : Formula 3) : Prop :=
  Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 f X Y) (env (rho 6)) p phi

private def CompLaws {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (f g X Y Z J p : M.Carrier .set) : Prop :=
  (MapForce env rho G F mul f X Y p (Source.SetLanguage.mapsTo 0 1 2) →
    MapForce env rho G F mul g Y Z p (Source.SetLanguage.mapsTo 0 1 2) →
    MapForce env rho G F mul J X Z p (Source.SetLanguage.mapsTo 0 1 2)) ∧
  (MapForce env rho G F mul f X Y p (Source.SetLanguage.surjection 0 1 2) →
    MapForce env rho G F mul g Y Z p (Source.SetLanguage.surjection 0 1 2) →
    MapForce env rho G F mul J X Z p (Source.SetLanguage.surjection 0 1 2)) ∧
  (MapForce env rho G F mul f X Y p (Source.SetLanguage.injection 0 1 2) →
    MapForce env rho G F mul g Y Z p (Source.SetLanguage.injection 0 1 2) →
    MapForce env rho G F mul J X Z p (Source.SetLanguage.injection 0 1 2))

/-- Only parameter slots change. The underlying forcing relation is the SAME. -/
theorem force_reindex {k n l : Nat} (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ j, other (base j) = env j)
    (rho : Fin 7 → Fin k) (G F mul : Fin k) (phi : Formula l)
    (v : Fin l → M.Carrier .set) (p : M.Carrier .set) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p phi ↔
    Force (orderFormula (base (rho 0)) (base mul)) (domain (fun j => base (rho j)) (base G) (base F))
      other v (env (rho 6)) p phi := by
  apply ForcingSeparation.force_congr ?_ ?_ phi v _ p
  · intro x y
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  · intro x
    simp only [domain_semantics,he]

theorem pre_reindex {k n : Nat} (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ j, other (base j) = env j)
    (rho : Fin 7 → Fin k) (mul : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    ForcingAtomicBasic.PreorderOn (orderFormula (base (rho 0)) (base mul)) other (other (base (rho 6))) := by
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (base (rho 0)) (base mul)) other x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  rw [he]
  constructor
  · intro p hp
    exact (hR p p).mp (hpre.1 p hp)
  · intro p q r hp hq hr hpq hqr
    exact (hR p r).mp (hpre.2 p q r hp hq hr ((hR p q).mpr hpq) ((hR q r).mpr hqr))

section Operations
variable {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
variable (I K two w G F mul top : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
variable (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w)
  (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
variable (hG : ForcingLabelPermutations.Carrier (env I) (env G))
variable (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
variable (ht : ForcingWithTopCarrier.Empty (env top))
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
include hM hp hG hF ht hpre

/-- Instantiate the already proved literal composition constructor at arbitrary
internal HS names and return its laws to the original environment. -/
theorem compose {f g X Y Z : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) f)
    (hg : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) g)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X)
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Y)
    (hZ : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Z) :
    ∃ J, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) → CompLaws env rho G F mul f g X Y Z J p := by
  let up5 : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
  let ra5 : Fin 7 → Fin (k+5) := fun j => up5 (rho j)
  let extra : Fin (k+5) → M.Carrier .set := Fin.cases Z (Fin.cases Y (Fin.cases X (Fin.cases g (Fin.cases f env))))
  have he5 (j : Fin k) : extra (up5 j) = env j := rfl
  have hNames (j : Fin 5) : HS actionFormula (fun j => extra (ra5 j)) (extra (up5 G)) (extra (ra5 6)) (extra (up5 F))
      (extra (ForcingMapCalculus.five (4 : Fin (k+5)) 3 2 1 0 j)) :=
    Fin.cases hf (Fin.cases hg (Fin.cases hX (Fin.cases hY (Fin.cases hZ (fun i => Fin.elim0 i))))) j
  obtain ⟨S,J,_,_,_,hGraph,hJHS,_⟩ := ForcingMapCalculus.actual_reuse hM extra ra5 (up5 I) (up5 K)
    (up5 two) (up5 w) (up5 G) (up5 F) (up5 mul) (up5 top)
    (ForcingMapCalculus.five 4 3 2 1 0) ForcingMapCalculus.compositionFormula 2 4 hp hG hF ht hNames
  let up : Fin k → Fin (k+6) := fun j => (up5 j).succ
  let ra : Fin 7 → Fin (k+6) := fun j => up (rho j)
  let other : Fin (k+6) → M.Carrier .set := Fin.cases S extra
  have he (j : Fin k) : other (up j) = env j := rfl
  have hfVal : other (5 : Fin (k+6)) = f := rfl
  have hgVal : other (4 : Fin (k+6)) = g := rfl
  have hXVal : other (3 : Fin (k+6)) = X := rfl
  have hYVal : other (2 : Fin (k+6)) = Y := rfl
  have hZVal : other (1 : Fin (k+6)) = Z := rfl
  have hn : (fun j : Fin 5 => (ForcingMapCalculus.five (4 : Fin (k+5)) 3 2 1 0 j).succ) =
      ForcingMapCalculus.five (5 : Fin (k+6)) 4 3 2 1 := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
  have hd : ForcingMapCalculus.five (4 : Fin (k+5)) 3 2 1 0 (2 : Fin 5) = 2 := rfl
  have hc : ForcingMapCalculus.five (4 : Fin (k+5)) 3 2 1 0 (4 : Fin 5) = 0 := rfl
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) (up mul))
      (ForcingMapCalculus.compositionRelation ra (up G) (up F) (up mul) 5 4 3 2 1)
      other (ra 6) (up top) 3 1 J := by
    have hs2 : (2 : Fin (k+5)).succ = (3 : Fin (k+6)) := by
      apply Fin.ext
      change 2 % (k+5) + 1 = 3 % (k+6)
      rw [Nat.mod_eq_of_lt (by omega : 2 < k+5), Nat.mod_eq_of_lt (by omega : 3 < k+6)]
    have hs0 : (0 : Fin (k+5)).succ = (1 : Fin (k+6)) := by
      apply Fin.ext
      change 0 % (k+5) + 1 = 1 % (k+6)
      rw [Nat.mod_eq_of_lt (by omega : 0 < k+5), Nat.mod_eq_of_lt (by omega : 1 < k+6)]
    simpa only [ForcingMapCalculus.compositionRelation,hn,hd,hc,hs2,hs0] using hGraph
  have hpre' := pre_reindex env other up he rho mul hpre
  have hX' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 3) := by
    simpa only [ra,he,hXVal] using hX
  have hZ' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 1) := by
    simpa only [ra,he,hZVal] using hZ
  refine ⟨J,?_,?_⟩
  · simpa only [ra5,he5] using hJHS
  · intro p hpW
    have hOp : CompLaws other ra (up G) (up F) (up mul) f g X Y Z J p := by
      simpa only [CompLaws,MapForce,hfVal,hgVal,hXVal,hYVal,hZVal] using
        (ForcingMapCalculus.composition_graph_functions other ra (up G) (up F) (up mul) (up top)
          5 4 3 2 1 hM hp hG hF ht hpre' hX' hZ' hGraph' hpW)
    have cast (phi : Formula 3) (v : Fin 3 → M.Carrier .set) := force_reindex env other up he rho G F mul phi v p
    refine ⟨?_,?_,?_⟩
    · intro hf hg
      exact (cast _ _).mpr (hOp.1 ((cast _ _).mp hf) ((cast _ _).mp hg))
    · intro hf hg
      exact (cast _ _).mpr (hOp.2.1 ((cast _ _).mp hf) ((cast _ _).mp hg))
    · intro hf hg
      exact (cast _ _).mpr (hOp.2.2 ((cast _ _).mp hf) ((cast _ _).mp hg))

/-- Literal inverse graph, instantiated at actual internal names. -/
theorem inverse {f X Y : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) f)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X)
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Y) :
    ∃ J, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        MapForce env rho G F mul f X Y p (Source.SetLanguage.surjection 0 1 2) →
        MapForce env rho G F mul f X Y p (Source.SetLanguage.injection 0 1 2) →
        MapForce env rho G F mul J Y X p (Source.SetLanguage.surjection 0 1 2) ∧
        MapForce env rho G F mul J Y X p (Source.SetLanguage.injection 0 1 2) := by
  let up3 : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  let ra3 : Fin 7 → Fin (k+3) := fun j => up3 (rho j)
  let extra : Fin (k+3) → M.Carrier .set := Fin.cases Y (Fin.cases X (Fin.cases f env))
  have he3 (j : Fin k) : extra (up3 j) = env j := rfl
  have hNames (j : Fin 3) : HS actionFormula (fun j => extra (ra3 j)) (extra (up3 G)) (extra (ra3 6)) (extra (up3 F))
      (extra (args3 (2 : Fin (k+3)) 1 0 j)) :=
    Fin.cases hf (Fin.cases hX (Fin.cases hY (fun i => Fin.elim0 i))) j
  obtain ⟨S,J,_,_,_,hGraph,hJHS,_⟩ := ForcingMapCalculus.actual_reuse hM extra ra3 (up3 I) (up3 K)
    (up3 two) (up3 w) (up3 G) (up3 F) (up3 mul) (up3 top)
    (args3 2 1 0) ForcingMapCalculus.inverseFormula 2 1 hp hG hF ht hNames
  let up : Fin k → Fin (k+4) := fun j => (up3 j).succ
  let ra : Fin 7 → Fin (k+4) := fun j => up (rho j)
  let other : Fin (k+4) → M.Carrier .set := Fin.cases S extra
  have he (j : Fin k) : other (up j) = env j := rfl
  have hfVal : other (3 : Fin (k+4)) = f := rfl
  have hXVal : other (2 : Fin (k+4)) = X := rfl
  have hYVal : other (1 : Fin (k+4)) = Y := rfl
  have hn : (fun j : Fin 3 => (args3 (2 : Fin (k+3)) 1 0 j).succ) = args3 (3 : Fin (k+4)) 2 1 := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j
  have hd : args3 (2 : Fin (k+3)) 1 0 (2 : Fin 3) = 0 := rfl
  have hc : args3 (2 : Fin (k+3)) 1 0 (1 : Fin 3) = 1 := rfl
  have hs0 : (0 : Fin (k+3)).succ = (1 : Fin (k+4)) := by
    apply Fin.ext
    change 0 % (k+3) + 1 = 1 % (k+4)
    rw [Nat.mod_eq_of_lt (by omega : 0 < k+3),Nat.mod_eq_of_lt (by omega : 1 < k+4)]
  have hs1 : (1 : Fin (k+3)).succ = (2 : Fin (k+4)) := by
    apply Fin.ext
    change 1 % (k+3) + 1 = 2 % (k+4)
    rw [Nat.mod_eq_of_lt (by omega : 1 < k+3),Nat.mod_eq_of_lt (by omega : 2 < k+4)]
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) (up mul))
      (ForcingMapCalculus.inverseRelation ra (up G) (up F) (up mul) 3 2 1)
      other (ra 6) (up top) 1 2 J := by
    simpa only [ForcingMapCalculus.inverseRelation,hn,hd,hc,hs0,hs1] using hGraph
  have hpre' := pre_reindex env other up he rho mul hpre
  have hX' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 2) := by
    simpa only [ra,he,hXVal] using hX
  have hY' : HS actionFormula (fun j => other (ra j)) (other (up G)) (other (ra 6)) (other (up F)) (other 1) := by
    simpa only [ra,he,hYVal] using hY
  refine ⟨J,?_,?_⟩
  · simpa only [ra3,he3] using hJHS
  · intro p hpW hf hi
    have cast (phi : Formula 3) (v : Fin 3 → M.Carrier .set) := force_reindex env other up he rho G F mul phi v p
    have hf' := (cast _ _).mp hf
    have hi' := (cast _ _).mp hi
    have hOp := ForcingMapCalculus.inverse_graph_functions other ra (up G) (up F) (up mul) (up top)
      3 2 1 hM hp hG hF ht hpre' hX' hY' hGraph' hpW hf' hi'
    exact ⟨(cast _ _).mpr hOp.1,(cast _ _).mpr hOp.2⟩

end Operations
private theorem args3_map {n : Nat} (v : Fin n → M.Carrier .set) (a b c : Fin n) :
    (fun j => v (args3 a b c j)) = args3 (v a) (v b) (v c) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

/-- Obtain the SAME raw image quotient and its bijection from the previously
closed native sentence. No quotient or inverse graph is an input. -/
private theorem image_data {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K two w mu G F mul c top bit A : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env A))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {h B : M.Carrier .set}
    (hh : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) h)
    (hB : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) B) :
    ∃ E Q J,
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) E ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Q ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      (∀ p, ForcingQuotientName.Quotient (Fin.cases p (Fin.cases Q (Fin.cases E env)))
        (fun j => (rho j).succ.succ.succ) G.succ.succ.succ F.succ.succ.succ mul.succ.succ.succ
        I.succ.succ.succ K.succ.succ.succ c.succ.succ.succ top.succ.succ.succ bit.succ.succ.succ
        A.succ.succ.succ 2 Q) ∧
      (∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        MapForce env rho G F mul h (env A) B p (Source.SetLanguage.surjection 0 1 2) →
        MapForce env rho G F mul J B Q p (Source.SetLanguage.surjection 0 1 2) ∧
        MapForce env rho G F mul J B Q p (Source.SetLanguage.injection 0 1 2)) := by
  let up2 : Fin k → Fin (k+2) := fun j => j.succ.succ
  let ra2 : Fin 7 → Fin (k+2) := fun j => up2 (rho j)
  let base : Fin (k+2) → M.Carrier .set := Fin.cases B (Fin.cases h env)
  have he2 (j : Fin k) : base (up2 j) = env j := rfl
  let nativeEnv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) (k+2) :=
    {bound := base,free := fun _ => env top}
  have hpre2 := pre_reindex env base up2 he2 rho mul hpre
  have hRes := ForcingImageQuotient.result_from_inputs ra2 (up2 I) (up2 K) (up2 two) (up2 w) (up2 mu)
    (up2 G) (up2 F) (up2 mul) (up2 c) (up2 top) (up2 bit) (up2 A) 1 0 hM nativeEnv
    hw hMu hp hG hF hc ht hLabels hpre2 hh hB
  simp only [ForcingImageQuotient.result,List.foldr,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConjugationGraph.subgroup_semantics,ForcingTupleStabilizer.tupleFixed_semantics,
    ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,ForcingSupportedNames.supported_semantics,
    ForcingQuotientName.quotient_semantics,ForcingImageQuotient.membershipLaw_semantics hM,
    ForcingImageQuotient.functionLaws_semantics hM,args3_map,id_eq] at hRes
  obtain ⟨S,E,Q,J,_,_,_,_,hEHS,_,hQraw,hQHS,_,_,hJHS,_,_,hFunctions⟩ := hRes
  let other : Fin (k+5) → M.Carrier .set := Fin.cases Q (Fin.cases E (Fin.cases S base))
  let up5 : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
  let ra5 : Fin 7 → Fin (k+5) := fun j => up5 (rho j)
  have he5 (j : Fin k) : other (up5 j) = env j := rfl
  have hQVal : other (0 : Fin (k+5)) = Q := rfl
  have hBVal : other (3 : Fin (k+5)) = B := rfl
  have hhVal : other (4 : Fin (k+5)) = h := rfl
  have hRaw : ForcingQuotientName.Quotient other ra5 (up5 G) (up5 F) (up5 mul) (up5 I)
      (up5 K) (up5 c) (up5 top) (up5 bit) (up5 A) 1 Q := hQraw
  refine ⟨E,Q,J,?_,?_,?_,?_,?_⟩
  · exact hEHS
  · exact hQHS
  · exact hJHS
  · intro p
    let both : Fin (k+6) → M.Carrier .set := Fin.cases p other
    have hBoth := (ForcingNonwellorderableQuotient.quotient_transport other both Fin.succ (fun _ => rfl)
      ra5 (up5 G) (up5 F) (up5 mul) (up5 I) (up5 K) (up5 c) (up5 top) (up5 bit) (up5 A) 1 Q).mpr hRaw
    let small : Fin (k+3) → M.Carrier .set := Fin.cases p (Fin.cases Q (Fin.cases E env))
    let embed : Fin (k+3) → Fin (k+6) := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun j => (up5 j).succ)))
    have he (j : Fin (k+3)) : both (embed j) = small j := by
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => rfl))) j
    exact (ForcingNonwellorderableQuotient.quotient_transport small both embed he
      (fun j => (rho j).succ.succ.succ) G.succ.succ.succ F.succ.succ.succ mul.succ.succ.succ
      I.succ.succ.succ K.succ.succ.succ c.succ.succ.succ top.succ.succ.succ bit.succ.succ.succ A.succ.succ.succ 2 Q).mp hBoth
  · intro p hpW hSurj
    have cast (phi : Formula 3) (v : Fin 3 → M.Carrier .set) := force_reindex env other up5 he5 rho G F mul phi v p
    have hf := hFunctions p hpW ((cast _ _).mp hSurj)
    exact ⟨(cast _ _).mpr hf.2.1,(cast _ _).mpr hf.2.2⟩

/-- The exact source image-bijection conclusion on the existing concrete frame. -/
def ImageOutcome (env : Fin 40 → M.Carrier .set) : Prop :=
  ∀ h B p,
    HS actionFormula (fun j => env (forcingRho j)) (env 34) (env 33) (env 35) h →
    HS actionFormula (fun j => env (forcingRho j)) (env 34) (env 33) (env 35) B →
    (Project.FirstOrderSemantics.reduct M).mem p (env 33) →
    MapForce env forcingRho 34 35 18 h (env 37) B p (Source.SetLanguage.surjection 0 1 2) →
    Force (orderFormula (forcingRho 0) 18) (domain forcingRho 34 35) env (args1 B) (env 33) p
      (ForcingCheckOrdinal.wellorderable 0).neg →
    ∃ q, (Project.FirstOrderSemantics.reduct M).mem q (env 33) ∧
      MapRel (orderFormula (forcingRho 0) 18) env q p ∧
      ∃ graph, HS actionFormula (fun j => env (forcingRho j)) (env 34) (env 33) (env 35) graph ∧
        MapForce env forcingRho 34 35 18 graph (env 37) B q
          ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))

/-- UniformImages:243-276, on the SAME Core and the already completed quotient
Outcome. All image, inverse and composition names are actually constructed. -/
theorem on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (env : Fin 40 → M.Carrier .set) (hCore : ForcingConcreteSystem.Core hM env)
    (hOutcome : ForcingConcreteSystem.Outcome env) : ImageOutcome env := by
  obtain ⟨_,hm,_,hp,hG,hF,hw,hMu,_,_,_,_,hc,ht,hLabels,_⟩ := hCore
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM (env 39) (env 13)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (forcingRho j))
    hp hG hNormal hF hw hSmall hc ht hLabels).1
  have hpre := ForcingProductPoset.preorder env (forcingRho 0) 18 (forcingRho 6)
    hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  intro h B p hh hB hpW hSurj hNoB
  obtain ⟨E,Q,J,hE,hQ,hJ,hRaw,hImage⟩ := image_data env forcingRho 27 14 3 39 13 34 35 18 36 1 2 37
    hM hw hMu hp hG hF hc ht hLabels hpre hh hB
  have hJp := hImage p hpW hSurj
  have hNoQ : Force (orderFormula (forcingRho 0) 18) (domain forcingRho 34 35) env
      (args1 Q) (env 33) p (ForcingCheckOrdinal.wellorderable 0).neg := by
    apply (ForcingFormula.force_neg hM hpre hpW (args1 Q) (ForcingCheckOrdinal.wellorderable 0)).mpr
    intro q hq hqp hQwo
    obtain ⟨r,hr,hrq,eta,heta,hOrd,hInj⟩ :=
      (ForcingCheckOrdinal.forces_wellorderable hM hpre hq (args1 Q) 0).mp hQwo q hq (hpre.1 q hq)
    obtain ⟨s,hs,hsr,K,hK,hKi⟩ := hInj r hr (hpre.1 r hr)
    have hEta := (domain_semantics env forcingRho 34 35 eta).mp heta
    have hKHS := (domain_semantics env forcingRho 34 35 K).mp hK
    obtain ⟨C,hC,hComp⟩ := compose env forcingRho 27 14 3 39 34 35 18 1 hM
      hp hG hNormal ht hpre hJ hKHS hB hQ hEta
    have hsp := hpre.2 s q p hs hq hpW (hpre.2 s r q hs hr hq hsr hrq) hqp
    have hBi : MapForce env forcingRho 34 35 18 C B eta s (Source.SetLanguage.injection 0 1 2) :=
      (hComp s hs).2.2 (ForcingFormula.mono hM hpre _ _ hpW hs hsp hJp.2) hKi
    have hBwo : Force (orderFormula (forcingRho 0) 18) (domain forcingRho 34 35) env
        (args1 B) (env 33) s (ForcingCheckOrdinal.wellorderable 0) := by
      apply (ForcingCheckOrdinal.forces_wellorderable hM hpre hs (args1 B) 0).mpr
      intro t htW hts
      have htr := hpre.2 t s r htW hs hr hts hsr
      refine ⟨t,htW,hpre.1 t htW,eta,heta,ForcingFormula.mono hM hpre _ _ hr htW htr hOrd,?_⟩
      intro a ha hat
      exact ⟨a,ha,hpre.1 a ha,C,(domain_semantics env forcingRho 34 35 C).mpr hC,
        ForcingFormula.mono hM hpre _ _ hs ha (hpre.2 a t s ha htW hs hat hts) hBi⟩
    exact (ForcingFormula.force_neg hM hpre hpW (args1 B) (ForcingCheckOrdinal.wellorderable 0)).mp hNoB s hs hsp hBwo
  let other : Fin 43 → M.Carrier .set := Fin.cases p (Fin.cases Q (Fin.cases E env))
  let up : Fin 40 → Fin 43 := fun j => j.succ.succ.succ
  have he (j : Fin 40) : other (up j) = env j := rfl
  have hNoQ' := (force_reindex env other up he forcingRho 34 35 18 _ (args1 Q) p).mp hNoQ
  obtain ⟨q,hq,hqp,f,hf,hfBij⟩ := hOutcome E Q p hE (hRaw p) hpW hNoQ'
  have hqp' : MapRel (orderFormula (forcingRho 0) 18) env q p := by
    change MapRel (orderFormula (up (forcingRho 0)) (up 18)) other q p at hqp
    simpa only [ForcingProductSymmetry.orderFormula_semantics,he] using hqp
  have hfBij' := (force_reindex env other up he forcingRho 34 35 18 _ (args3 f (env 37) Q) q).mpr hfBij
  have hfLaws := (ForcingFormula.force_conj _ _ _ _ _ _ _ _).mp hfBij'
  have hSurjq := ForcingFormula.mono hM hpre _ _ hpW hq hqp' hSurj
  have hJq := hImage q hq hSurjq
  obtain ⟨K,hK,hInverse⟩ := inverse env forcingRho 27 14 3 39 34 35 18 1 hM hp hG hNormal ht hpre hJ hB hQ
  have hKq := hInverse q hq hJq.1 hJq.2
  obtain ⟨C,hC,hComp⟩ := compose env forcingRho 27 14 3 39 34 35 18 1 hM hp hG hNormal ht hpre hf hK hA hQ hB
  exact ⟨q,hq,hqp',C,hC,(ForcingFormula.force_conj _ _ _ _ _ _ _ _).mpr
    ⟨(hComp q hq).2.1 hfLaws.1 hKq.1,(hComp q hq).2.2 hfLaws.2 hKq.2⟩⟩

/-- Native object sentence for all actual HS image names and conditions. -/
def imageOutcomeFormula : Project.Formula 1 40 :=
  let R := orderFormula (forcingRho 0) 18
  let H := domain forcingRho 34 35
  let up3 : Fin 40 → Fin 43 := fun j => j.succ.succ.succ
  let up4 : Fin 40 → Fin 44 := fun j => j.succ.succ.succ.succ
  let up5 : Fin 40 → Fin 45 := fun j => j.succ.succ.succ.succ.succ
  let out : Project.Formula 1 43 :=
    .existsE (.conj (.mem (.bound 0) (.bound (up4 33)))
      (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel R up4 0 1))
        (.existsE (.conj
          (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up5 (forcingRho j))
            (up5 34) (up5 33) (up5 35) 0))
          (ProjectSyntax.encode id (ForcingFormula.formula R H up5 (args3 0 (up5 37) 3) (up5 33) 1
            ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))))))))
  .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up3 (forcingRho j))
      (up3 34) (up3 33) (up3 35) 2))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up3 (forcingRho j))
      (up3 34) (up3 33) (up3 35) 1))
    (.imp (.mem (.bound 0) (.bound (up3 33)))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H up3 (args3 2 (up3 37) 1) (up3 33) 0
      (Source.SetLanguage.surjection 0 1 2)))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H up3 (args1 1) (up3 33) 0
      (ForcingCheckOrdinal.wellorderable 0).neg)) out)))))))

theorem imageOutcomeFormula_freeClosed : imageOutcomeFormula.FreeClosed := by
  simp -implicitDefEqProofs [imageOutcomeFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

private theorem args1_map {n : Nat} (v : Fin n → M.Carrier .set) (a : Fin n) :
    (fun j => v (args1 a j)) = args1 (v a) := by
  funext j
  exact Fin.cases rfl (fun i => Fin.elim0 i) j

theorem imageOutcomeFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env imageOutcomeFormula ↔ ImageOutcome env.bound := by
  simp only [imageOutcomeFormula,ImageOutcome,MapForce,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics,
    ForcingFormula.formula_semantics,ForcingMapConditions.rel_semantics,args3_map,args1_map,id_eq]
  rfl

def sentence : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj ForcingConcreteSystem.coreFormula (.conj ForcingConcreteSystem.outcomeFormula imageOutcomeFormula))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ForcingConcreteSystem.coreFormula_freeClosed,ForcingConcreteSystem.outcomeFormula_freeClosed,imageOutcomeFormula_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) sentence.formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩ := ForcingConcreteSystem.construct hM hOrder hChoice hw
  have hImages := on_core hM _ hCore hOutcome
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingConcreteSystem.coreFormula_semantics hM,ForcingConcreteSystem.outcomeFormula_semantics hM,imageOutcomeFormula_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome,hImages⟩

theorem kernel_certificate :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sentence)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence)).mp
      (models hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ForcingNonwellorderableImage
