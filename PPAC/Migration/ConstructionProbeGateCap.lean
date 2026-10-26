/- Pinned ProbeMargins.OldMinimum/gateCap. Use the existing old-gate
profile, native definable functions and exact actual old cost, never the
cost of an arbitrary larger old multiple. All quantifiers are internal. -/
import PPAC.Migration.ConstructionPersistentProfiles
import PPAC.Migration.ConstructionCutProduct

namespace PPAC.Migration.ConstructionProbeGateCap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBaseMonoid (Divides)
open ConstructionRealCuts (Subset)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The element divisibility order, distinct from the diagram order. -/
theorem divides_antisymm {D mul e x y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hxy : Divides D mul x y) (hyx : Divides D mul y x) : x = y := by
  obtain ⟨a,ha,hxa⟩ := hxy
  obtain ⟨b,hb,hyb⟩ := hyx
  obtain ⟨ab,hab,hp⟩ := (hm.2.1 a ha).1 b hb
  have hxprod := (hm.2.2 x a b y ab x hx ha hb hxa hp).mp hyb
  have he := (hm.2.1 x hx).2.2 ab e x hab hm.1.1 hxprod ((hm.1.2 x hx x).2.mpr rfl)
  have hae := (hc a b ha hb (he ▸ hp)).1
  subst a
  exact ((hm.1.2 x hx y).2.mp hxa).symm

def OldMinimum (D N mul G O q g : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem g D ∧ ∀ y fy, PureKuratowski.PairMember M y fy O →
    (Divides N G q fy ↔ Divides D mul g y)

theorem minimum_unique {D N mul e G O q g k : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hO : MapsTo D N O)
    (hg : OldMinimum D N mul G O q g) (hk : OldMinimum D N mul G O q k) : g = k := by
  obtain ⟨og,hog,_⟩ := hO.1.2 g hg.1
  obtain ⟨ok,hok,_⟩ := hO.1.2 k hk.1
  have hgg : Divides D mul g g := ⟨e,hm.1.1,(hm.1.2 g hg.1 g).2.mpr rfl⟩
  have hkk : Divides D mul k k := ⟨e,hm.1.1,(hm.1.2 k hk.1 k).2.mpr rfl⟩
  exact divides_antisymm hm hc hg.1 ((hg.2 k ok hok).mp ((hk.2 k ok hok).mpr hkk))
    ((hk.2 g og hog).mp ((hg.2 g og hog).mpr hgg))

/-- Forget only the extra intersection field of the already proved source
gate; its exact old-multiple profile supplies OldMinimum. -/
theorem minimum_of_oldGate {D N mul G O q g fg : M.Carrier .set}
    (hO : MapsTo D N O) (hg : ConstructionPersistentProfiles.OldGate D N mul G O q g fg) :
    OldMinimum D N mul G O q g :=
  ⟨ForcingConditionGraphs.function_input hO.1 hg.1,hg.2.2.1⟩

def Value (D N mul G O C unit q c : M.Carrier .set) : Prop :=
  (∃ g, OldMinimum D N mul G O q g ∧ PureKuratowski.PairMember M g c C) ∨
    (¬ (∃ g, OldMinimum D N mul G O q g) ∧ c = unit)

theorem value_total {D N mul G O C unit R : M.Carrier .set}
    (hC : MapsTo D R C) (hu : (Project.FirstOrderSemantics.reduct M).mem unit R) (q : M.Carrier .set) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c R ∧ Value D N mul G O C unit q c := by
  classical
  by_cases hg : ∃ g, OldMinimum D N mul G O q g
  · obtain ⟨g,hg⟩ := hg
    obtain ⟨c,hc,_⟩ := hC.1.2 g hg.1
    exact ⟨c,hC.2 g c hc,Or.inl ⟨g,hg,hc⟩⟩
  · exact ⟨unit,hu,Or.inr ⟨hg,rfl⟩⟩

theorem value_unique {D N mul e G O C unit R q c d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hO : MapsTo D N O) (hC : MapsTo D R C)
    (hv : Value D N mul G O C unit q c) (hw : Value D N mul G O C unit q d) : c = d := by
  rcases hv with ⟨g,hg,hgc⟩ | ⟨hn,he⟩
  · rcases hw with ⟨k,hk,hkd⟩ | ⟨hn,_⟩
    · have he := minimum_unique hm hc hO hg hk
      subst k
      exact ForcingConditionGraphs.function_unique hC.1 hgc hkd
    · exact (hn ⟨g,hg⟩).elim
  · rcases hw with ⟨g,hg,_⟩ | ⟨_,he'⟩
    · exact (hn ⟨g,hg⟩).elim
    · exact he.trans he'.symm

theorem value_range {D N mul G O C unit R q c : M.Carrier .set}
    (hC : MapsTo D R C) (hu : (Project.FirstOrderSemantics.reduct M).mem unit R)
    (hv : Value D N mul G O C unit q c) : (Project.FirstOrderSemantics.reduct M).mem c R := by
  rcases hv with ⟨g,_,hgc⟩ | ⟨_,rfl⟩
  · exact hC.2 g c hgc
  · exact hu

def Graph (D N mul G O C unit Cap : M.Carrier .set) : Prop := ∀ q c,
  PureKuratowski.PairMember M q c Cap ↔
    (Project.FirstOrderSemantics.reduct M).mem q N ∧ Value D N mul G O C unit q c

/-- Non-strict cost upper bound: later costs may equal the unit cut. -/
def Bounds (unit C : M.Carrier .set) : Prop := ∀ q c, PureKuratowski.PairMember M q c C →
  (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c unit

theorem cap_bounds {D N mul G O C unit Cap : M.Carrier .set}
    (hg : Graph D N mul G O C unit Cap) (hC : Bounds unit C)
    (hu : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit) : Bounds unit Cap := by
  intro q c hqc
  rcases ((hg q c).mp hqc).2 with ⟨g,_,hgc⟩ | ⟨_,rfl⟩
  · exact hC g c hgc
  · exact ⟨hu,fun _ h => h⟩

theorem cap_eq {D N mul G O C unit Cap q g c : M.Carrier .set}
    (hg : Graph D N mul G O C unit Cap) (hq : (Project.FirstOrderSemantics.reduct M).mem q N)
    (hmin : OldMinimum D N mul G O q g) (hcost : PureKuratowski.PairMember M g c C) :
    PureKuratowski.PairMember M q c Cap := (hg q c).mpr ⟨hq,Or.inl ⟨g,hmin,hcost⟩⟩

theorem cap_default {D N mul G O C unit Cap q : M.Carrier .set}
    (hg : Graph D N mul G O C unit Cap) (hq : (Project.FirstOrderSemantics.reduct M).mem q N)
    (hn : ¬ ∃ g, OldMinimum D N mul G O q g) : PureKuratowski.PairMember M q unit Cap :=
  (hg q unit).mpr ⟨hq,Or.inr ⟨hn,rfl⟩⟩

def oldMinimum {m : Nat} (D N mul G O q g : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound g) (.bound D)) (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
O.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.iff (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
N.succ.succ G.succ.succ q.succ.succ (0 : Fin (m+2)))) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
D.succ.succ mul.succ.succ g.succ.succ (1 : Fin (m+2)))))))))

theorem oldMinimum_freeClosed {m : Nat} (D N mul G O q g : Fin m) : (oldMinimum D N mul G O q g).FreeClosed := by
  simp -implicitDefEqProofs [oldMinimum,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem oldMinimum_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul G O q g : Fin m) :
    Project.Formula.satisfies env (oldMinimum D N mul G O q g) ↔ OldMinimum (env.bound D) (env.bound N) (env.bound mul) (env.bound G) (env.bound O) (env.bound q) (env.bound g) := by
  simp only
    [oldMinimum,OldMinimum,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def value {m : Nat} (D N mul G O C unit q c : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (oldMinimum D.succ N.succ mul.succ G.succ O.succ q.succ (0 : Fin (m+1)))
(ProjectSyntax.encode id (Source.SetLanguage.edge C.succ (0 : Fin (m+1)) c.succ)))) (.conj (.neg (.existsE
(oldMinimum D.succ N.succ mul.succ G.succ O.succ q.succ (0 : Fin (m+1))))) (Project.Formula.extensionalEq
(.bound c) (.bound unit))))

theorem value_freeClosed {m : Nat} (D N mul G O C unit q c : Fin m) : (value D N mul G O C unit q c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,oldMinimum_freeClosed,ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul G O C unit q c : Fin m) :
    Project.Formula.satisfies env (value D N mul G O C unit q c) ↔ Value (env.bound D) (env.bound N) (env.bound mul) (env.bound G) (env.bound O) (env.bound C) (env.bound unit) (env.bound q) (env.bound c) := by
  simp only
    [value,Value,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,oldMinimum_semantics
    hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality
    hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality
    hM),Project.Term.eval_bound]
  rfl

def graph {m : Nat} (D N mul G O C unit Cap : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Cap.succ.succ (1 : Fin (m+2)) (0 :
Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound N.succ.succ)) (value D.succ.succ N.succ.succ
mul.succ.succ G.succ.succ O.succ.succ C.succ.succ unit.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (D N mul G O C unit Cap : Fin m) : (graph D N mul G O C unit Cap).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,value_freeClosed,ProjectSyntax.freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul G O C unit Cap : Fin m) :
    Project.Formula.satisfies env (graph D N mul G O C unit Cap) ↔ Graph (env.bound D) (env.bound N) (env.bound mul) (env.bound G) (env.bound O) (env.bound C) (env.bound unit) (env.bound Cap) := by
  simp only
    [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

def bounds {m : Nat} (unit C : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ (1 : Fin (m+2)) (0 : Fin
(m+2)))) (.conj (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3))))) (Project.Formula.subset
(.bound (0 : Fin (m+2))) (.bound unit.succ.succ))))))

theorem bounds_freeClosed {m : Nat} (unit C : Fin m) : (bounds unit C).FreeClosed := by
  simp -implicitDefEqProofs [bounds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem bounds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (unit C : Fin m) :
    Project.Formula.satisfies env (bounds unit C) ↔ Bounds (env.bound unit) (env.bound C) := by
  simp only
    [bounds,Bounds,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {D N mul e G O C unit R : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hO : MapsTo D N O) (hC : MapsTo D R C)
    (hu : (Project.FirstOrderSemantics.reduct M).mem unit R) :
    ∃ Cap, MapsTo N R Cap ∧ Graph D N mul G O C unit Cap := by
  let schema : Project.BinarySchema 7 := {
    body := value 2 3 4 5 6 7 8 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases N (Fin.cases mul (Fin.cases G (Fin.cases O (Fin.cases C (fun _ => unit))))))
    free := fun _ => D }
  have he (q c : M.Carrier .set) : schema.denote env q c ↔ Value D N mul G O C unit q c :=
    value_semantics hM ((env.push q).push c) 2 3 4 5 6 7 8 1 0
  obtain ⟨Cap,hCap,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := N) (target := R) (by
      intro q _
      obtain ⟨c,_,hv⟩ := value_total hC hu q
      exact ⟨c,(he q c).mpr hv⟩) (by
      intro q _ c d hc' hd
      exact value_unique hm hc hO hC ((he q c).mp hc') ((he q d).mp hd)) (by
      intro q c _ hv
      exact value_range hC hu ((he q c).mp hv))
  exact ⟨Cap,(ForcingSupportSize.native_mapsTo hM N R Cap).mpr hCap,
    fun q c => (hg q c).trans (and_congr_right (fun _ => he q c))⟩

theorem graph_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D N mul G O C unit R Cap K : M.Carrier .set}
    (hCap : MapsTo N R Cap) (hK : MapsTo N R K)
    (hg : Graph D N mul G O C unit Cap) (hk : Graph D N mul G O C unit K) : Cap = K :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM N R Cap).mp hCap).1.1
    ((ForcingSupportSize.native_mapsTo hM N R K).mp hK).1.1
    (fun q c => (hg q c).trans (hk q c).symm)

theorem exists_cap (hM : FirstOrder.Theory.Models M nativeZF)
    {D N mul e G O C unit R : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hO : MapsTo D N O) (hC : MapsTo D R C)
    (hu : (Project.FirstOrderSemantics.reduct M).mem unit R)
    (hun : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit) (hB : Bounds unit C) :
    ∃ Cap, MapsTo N R Cap ∧ Graph D N mul G O C unit Cap ∧ Bounds unit Cap ∧
      (∀ q g c, (Project.FirstOrderSemantics.reduct M).mem q N → OldMinimum D N mul G O q g →
        PureKuratowski.PairMember M g c C → PureKuratowski.PairMember M q c Cap) ∧
      (∀ q, (Project.FirstOrderSemantics.reduct M).mem q N →
        ¬ (∃ g, OldMinimum D N mul G O q g) → PureKuratowski.PairMember M q unit Cap) ∧
      ∀ K, MapsTo N R K → Graph D N mul G O C unit K → K = Cap := by
  obtain ⟨Cap,hCap,hg⟩ := exists_graph hM hm hc hO hC hu
  exact ⟨Cap,hCap,hg,cap_bounds hg hB hun,
    fun _ _ _ hq hmin hcost => cap_eq hg hq hmin hcost,
    fun _ hq hn => cap_default hg hq hn,
    fun _ hK hk => graph_unique hM hK hCap hk hg⟩

end PPAC.Migration.ConstructionProbeGateCap
