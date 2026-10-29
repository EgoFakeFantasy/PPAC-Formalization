/- Exact source raw-set rank, reusing ObjectRankCover and the completed
source cumulative hierarchy. No new rank construction or external WF.
Consumer: AtomicForcing.Child.rank_lt -> PersistentCodes.ordF_eq_check_le. -/
import PPAC.Migration.ObjectRankCover
import PPAC.Migration.ForcingNameInduction

namespace PPAC.Migration.ForcingRawRank
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The existing source ordinal formula, including internal well-foundedness. -/
def Ordinal (a : M.Carrier .set) : Prop :=
  Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (args1 a) (OrdinalSyntax.ordinal 0)

/-- The existing cumulative hierarchy formula, not a newly supplied hierarchy. -/
def Layer (a V : M.Carrier .set) : Prop :=
  Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (args2 a V) (HierarchyLayerSyntax.layer 0 1)

/-- Exactly the existing least ordinal whose actual layer contains the set. -/
def Rank (x a : M.Carrier .set) : Prop :=
  Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (args2 x a) (LayerRankSyntax.rank 0 1)

theorem env_args2 {m : Nat} (env : Fin m → M.Carrier .set) (x y : Fin m) :
    (fun i => env (args2 x y i)) = args2 (env x) (env y) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun z => Fin.elim0 z) j

theorem ordinal_semantics {m : Nat} (env : Fin m → M.Carrier .set) (a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (OrdinalSyntax.ordinal a) ↔ Ordinal (env a) := by
  have h := DefinableMinimaChoice.realize_rename (Project.FirstOrderSemantics.reduct M).mem
    (OrdinalSyntax.ordinal (0 : Fin 1)) (args1 a) env
  have he : (fun i => env (args1 a i)) = args1 (env a) := by
    funext i
    exact Fin.cases rfl (fun z => Fin.elim0 z) i
  rw [OrdinalSyntax.ordinal_rename,he] at h
  simpa [Ordinal,args1] using h

theorem layer_semantics {m : Nat} (env : Fin m → M.Carrier .set) (a V : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (HierarchyLayerSyntax.layer a V) ↔ Layer (env a) (env V) := by
  have h := DefinableMinimaChoice.realize_rename (Project.FirstOrderSemantics.reduct M).mem
    (HierarchyLayerSyntax.layer (0 : Fin 2) 1) (args2 a V) env
  rw [HierarchyLayerSyntax.layer_rename,env_args2] at h
  have h0 : args2 a V (0 : Fin 2) = a := Fin.cases_zero
  have h1 : args2 a V (1 : Fin 2) = V := (Fin.cases_succ (0 : Fin 1)).trans Fin.cases_zero
  simpa only [h0,h1,Layer] using h

theorem rank_semantics {m : Nat} (env : Fin m → M.Carrier .set) (x a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (LayerRankSyntax.rank x a) ↔ Rank (env x) (env a) := by
  have h := DefinableMinimaChoice.realize_rename (Project.FirstOrderSemantics.reduct M).mem
    (LayerRankSyntax.rank (0 : Fin 2) 1) (args2 x a) env
  rw [LayerRankSyntax.rank_rename,env_args2] at h
  have h0 : args2 x a (0 : Fin 2) = x := Fin.cases_zero
  have h1 : args2 x a (1 : Fin 2) = a := (Fin.cases_succ (0 : Fin 1)).trans Fin.cases_zero
  simpa only [h0,h1,Rank] using h

theorem contains_semantics {m : Nat} (env : Fin m → M.Carrier .set) (x a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (LayerCoverSyntax.contains x a) ↔
      ∃ V, Layer (env a) V ∧ ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (env x) →
        (Project.FirstOrderSemantics.reduct M).mem z V := by
  simp only [LayerCoverSyntax.contains,Formula.Realize,layer_semantics (M := M),
    RestrictionSyntax.subset,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem rank_spec {x a : M.Carrier .set} : Rank x a ↔
    (Ordinal a ∧ ∃ V, Layer a V ∧ ∀ z, (Project.FirstOrderSemantics.reduct M).mem z x →
      (Project.FirstOrderSemantics.reduct M).mem z V) ∧
    ∀ b, (Ordinal b ∧ ∃ W, Layer b W ∧ ∀ z, (Project.FirstOrderSemantics.reduct M).mem z x →
      (Project.FirstOrderSemantics.reduct M).mem z W) → a = b ∨ (Project.FirstOrderSemantics.reduct M).mem a b := by
  simp only [Rank,LayerRankSyntax.rank,OrdinalLeastSyntax.least,OrdinalLeastSyntax.property,
    MinimalPredicates.pred,DefinableMinimaChoice.realize_rename,LayerCoverSyntax.containsMatrix,
    Formula.Realize,ordinal_semantics (M := M),contains_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl


theorem closed_truth (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat} (phi : Formula n)
    (h : FirstOrder.Derives nativeZF [] (Translation.sentence phi.close))
    (env : Fin n → M.Carrier .set) : Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env phi :=
  (GodelDefOutput.close_semantics _ _).mp ((Translation.realizes_sentence M _).mp (h.semantically_entails M hM)) env

theorem exists_rank (hM : FirstOrder.Theory.Models M nativeZF) (x : M.Carrier .set) : ∃ a, Rank x a := by
  have h := closed_truth hM (LayerRankSyntax.fiber (0 : Fin 1)) ObjectRankCover.native_rank (args1 x)
  obtain ⟨a,ha,_⟩ := h
  exact ⟨a,(rank_semantics (M := M) _ _ _).mp ha⟩

theorem unique_rank (hM : FirstOrder.Theory.Models M nativeZF) {x a b : M.Carrier .set}
    (ha : Rank x a) (hb : Rank x b) : a = b := by
  have h := closed_truth hM ((LayerRankSyntax.rank (0 : Fin 3) 1).imp
    ((LayerRankSyntax.rank 0 2).imp (.equal 1 2))) ObjectRankCover.native_equality (Source.SetLanguage.args3 x a b)
  simp only [Formula.Realize,rank_semantics (M := M)] at h
  exact h ha hb

theorem ordinal_member (hM : FirstOrder.Theory.Models M nativeZF) {a b : M.Carrier .set}
    (ha : Ordinal a) (hb : (Project.FirstOrderSemantics.reduct M).mem b a) : Ordinal b := by
  have h := closed_truth hM ((OrdinalSyntax.ordinal (0 : Fin 2)).imp
    ((Formula.mem 1 0).imp (OrdinalSyntax.ordinal 1))) ObjectOrdinalBasic.native_member (args2 a b)
  simp only [Formula.Realize,ordinal_semantics (M := M)] at h
  exact h ha hb

theorem ordinal_transitive {a : M.Carrier .set} (ha : Ordinal a) :
    ∀ b, (Project.FirstOrderSemantics.reduct M).mem b a → ∀ c,
      (Project.FirstOrderSemantics.reduct M).mem c b → (Project.FirstOrderSemantics.reduct M).mem c a := by
  have h := ha.1
  simp only [OrdinalSyntax.transitiveSet,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc] at h
  intro b hb c hc
  exact h b c hb hc


theorem layer_membership (hM : FirstOrder.Theory.Models M nativeZF) {a V : M.Carrier .set}
    (ha : Ordinal a) (hV : Layer a V) (x : M.Carrier .set) :
    (Project.FirstOrderSemantics.reduct M).mem x V ↔ ∃ b W,
      (Project.FirstOrderSemantics.reduct M).mem b a ∧ Layer b W ∧
        ∀ z, (Project.FirstOrderSemantics.reduct M).mem z x → (Project.FirstOrderSemantics.reduct M).mem z W := by
  have h := closed_truth hM ((OrdinalSyntax.ordinal (0 : Fin 2)).imp
    ((HierarchyLayerSyntax.layer 0 1).imp (HierarchyMemberSyntax.membership 0 1)))
    ObjectHierarchyAlgebra.native_membership (args2 a V)
  have h' := h ((ordinal_semantics (M := M) _ _).mpr ha) ((layer_semantics (M := M) _ _ _).mpr hV) x
  simp only [HierarchyMemberSyntax.layerMember,HierarchyMemberSyntax.layerData,Formula.Realize,
    layer_semantics (M := M),RestrictionSyntax.subset,Formula.Realize,
    Fin.lastCases_last,Fin.lastCases_castSucc,args2,Fin.cases_zero] at h'
  exact ⟨h'.1,h'.2⟩

theorem member_rank_lt (hM : FirstOrder.Theory.Models M nativeZF) {x y a b : M.Carrier .set}
    (hx : Rank x a) (hy : Rank y b) (hyx : (Project.FirstOrderSemantics.reduct M).mem y x) :
    (Project.FirstOrderSemantics.reduct M).mem b a := by
  obtain ⟨⟨ha,V,hV,hxV⟩,_⟩ := rank_spec.mp hx
  obtain ⟨c,W,hca,hW,hyW⟩ := (layer_membership hM ha hV y).mp (hxV y hyx)
  rcases (rank_spec.mp hy).2 c ⟨ordinal_member hM ha hca,W,hW,hyW⟩ with he | he
  · exact he.symm ▸ hca
  · exact ordinal_transitive ha c hca b he

/-- Exactly the source three Kuratowski links, with existing unique internal ranks. -/
theorem child_rank_lt (hM : FirstOrder.Theory.Models M nativeZF) {x y a b c : M.Carrier .set}
    (hx : Rank x a) (hy : Rank y b) (hchild : PureKuratowski.PairMember M y c x) :
    (Project.FirstOrderSemantics.reduct M).mem b a := by
  obtain ⟨single,edge,hySingle,hSingleEdge,hEdge⟩ := ForcingNameInduction.child_descent ⟨c,hchild⟩
  obtain ⟨r,hr⟩ := exists_rank hM single
  obtain ⟨s,hs⟩ := exists_rank hM edge
  have hbr := member_rank_lt hM hr hy hySingle
  have hrs := member_rank_lt hM hs hr hSingleEdge
  have hsa := member_rank_lt hM hx hs hEdge
  have hba := ordinal_transitive (rank_spec.mp hx).1.1 s hsa r hrs
  exact ordinal_transitive (rank_spec.mp hx).1.1 r hba b hbr

def descentSentence : Source.Sentence := ((LayerRankSyntax.rank (0 : Fin 5) 2).imp
  ((LayerRankSyntax.rank 1 3).imp ((Source.SetLanguage.edge 0 1 4).imp (.mem 3 2)))).close

theorem descent_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence descentSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hx hy hc
  exact child_rank_lt hM ((rank_semantics (M := M) env 0 2).mp hx)
    ((rank_semantics (M := M) env 1 3).mp hy) ((KuratowskiZF.source_edge env 0 1 4).mp hc)

theorem descent_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence descentSentence) :=
  ModelTransfer.derives (fun _ hM => descent_models hM)

end PPAC.Migration.ForcingRawRank
