/- Internal rounded lower cuts of the accepted fraction preorder.
Representation adapter for pinned DiagramOrder.HeightCost and MonoidBase.missedSup.
Only the nonnegative order/completeness interface is claimed here; field arithmetic
and the source margin are separate obligations. Reuses native Separation/PowerSet/Union. -/
import PPAC.Migration.ConstructionFractionDensity

namespace PPAC.Migration.ConstructionRealCuts
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

abbrev Subset (a b : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p a → (Project.FirstOrderSemantics.reduct M).mem p b

/-- Empty cuts are allowed (zero); the whole fraction carrier is excluded. -/
def Cut (hM : FirstOrder.Theory.Models M nativeZF) (w Q c : M.Carrier .set) : Prop :=
  Subset c Q ∧
  (∀ p q, (Project.FirstOrderSemantics.reduct M).mem q c → Le hM w p q →
    (Project.FirstOrderSemantics.reduct M).mem p c) ∧
  (∀ p, (Project.FirstOrderSemantics.reduct M).mem p c → ∃ q,
    (Project.FirstOrderSemantics.reduct M).mem q c ∧ Lt hM w p q) ∧
  (∃ q, (Project.FirstOrderSemantics.reduct M).mem q Q ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem q c)

def cut {m : Nat} (w Q c : Fin m) : Project.Formula 1 m :=
  .conj (Project.Formula.subset (.bound c) (.bound Q))
    (.conj (.forallE (.forallE (.imp (.mem (.bound 0) (.bound c.succ.succ))
      (.imp (le w.succ.succ 1 0) (.mem (.bound 1) (.bound c.succ.succ))))))
      (.conj (.forallE (.imp (.mem (.bound 0) (.bound c.succ)) (.existsE
        (.conj (.mem (.bound 0) (.bound c.succ.succ)) (lt w.succ.succ 1 0)))))
        (.existsE (.conj (.mem (.bound 0) (.bound Q.succ)) (.neg (.mem (.bound 0) (.bound c.succ)))))))

theorem cut_freeClosed {m : Nat} (w Q c : Fin m) : (cut w Q c).FreeClosed := by
  simp -implicitDefEqProofs [cut,Definitional.Formula.FreeClosed,le_freeClosed,lt_freeClosed]

theorem cut_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q c : Fin m) :
    Project.Formula.satisfies env (cut w Q c) ↔ Cut hM (env.bound w) (env.bound Q) (env.bound c) := by
  simp only [cut,Cut,Subset,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,le_semantics hM,lt_semantics hM,
    Project.Term.eval_bound]
  rfl

def Principal (hM : FirstOrder.Theory.Models M nativeZF) (w Q q c : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p c ↔
    (Project.FirstOrderSemantics.reduct M).mem p Q ∧ Lt hM w p q

def principal {m : Nat} (w Q q c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound Q.succ)) (lt w.succ 0 q.succ)))

theorem principal_freeClosed {m : Nat} (w Q q c : Fin m) : (principal w Q q c).FreeClosed := by
  simp -implicitDefEqProofs [principal,Definitional.Formula.FreeClosed,lt_freeClosed]

theorem principal_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q q c : Fin m) :
    Project.Formula.satisfies env (principal w Q q c) ↔
      Principal hM (env.bound w) (env.bound Q) (env.bound q) (env.bound c) := by
  simp only [principal,Principal,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,lt_semantics hM,Project.Term.eval_bound]
  rfl

theorem exists_principal (hM : FirstOrder.Theory.Models M nativeZF) (w Q q : M.Carrier .set) :
    ∃ c, Principal hM w Q q c := by
  let schema : Project.UnarySchema 2 := { body := lt 1 0 2, freeClosed := lt_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases w (fun _ => q), free := fun _ => w }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  refine ⟨c,fun p => ?_⟩
  exact (hc p).trans (and_congr_right (fun _ => lt_semantics hM (env.push p) 1 0 2))

theorem principal_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q q c d : M.Carrier .set}
    (hc : Principal hM w Q q c) (hd : Principal hM w Q q d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => (hc p).trans (hd p).symm)

theorem principal_cut (hM : FirstOrder.Theory.Models M nativeZF) {w Q q c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q Q) (hc : Principal hM w Q q c) : Cut hM w Q c := by
  refine ⟨fun p hp => ((hc p).mp hp).1,?_,?_,q,hq,?_⟩
  · intro p r hr hpr
    have hprCopy := hpr
    obtain ⟨a,b,d,e,hp,_,_⟩ := hprCopy
    exact (hc p).mpr ⟨(hQ p).mpr ⟨a,b,hp⟩,le_lt_trans hM hw hpr ((hc r).mp hr).2⟩
  · intro p hp
    obtain ⟨r,hr,hpr,hrq⟩ := dense hM hw ((hc p).mp hp).2
    exact ⟨r,(hc r).mpr ⟨(hQ r).mpr hr,hrq⟩,hpr⟩
  · exact fun h => lt_irrefl ((hc q).mp h).2

/-- Principal cuts compare by the original numerical preorder, not code equality. -/
theorem principal_subset_iff (hM : FirstOrder.Theory.Models M nativeZF) {w Q q r c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q Q) (hr : (Project.FirstOrderSemantics.reduct M).mem r Q)
    (hc : Principal hM w Q q c) (hd : Principal hM w Q r d) : Subset c d ↔ Le hM w q r := by
  constructor
  · intro hsub
    classical
    by_cases hqr : Le hM w q r
    · exact hqr
    · have hrq := (le_total hM hw ((hQ q).mp hq) ((hQ r).mp hr)).resolve_left hqr
      have hrc := (hc r).mpr ⟨hr,hrq,hqr⟩
      exact (lt_irrefl ((hd r).mp (hsub r hrc)).2).elim
  · intro hqr p hp
    obtain ⟨hpQ,hpq⟩ := (hc p).mp hp
    exact (hd p).mpr ⟨hpQ,lt_le_trans hM hw hpq hqr⟩

theorem principal_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {w Q q r c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q Q) (hr : (Project.FirstOrderSemantics.reduct M).mem r Q)
    (hc : Principal hM w Q q c) (hd : Principal hM w Q r d) : c = d ↔ Le hM w q r ∧ Le hM w r q := by
  constructor
  · intro he
    exact ⟨(principal_subset_iff hM hw hQ hq hr hc hd).mp (fun _ h => he ▸ h),
      (principal_subset_iff hM hw hQ hr hq hd hc).mp (fun _ h => he.symm ▸ h)⟩
  · rintro ⟨hqr,hrq⟩
    exact (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p =>
      ⟨(principal_subset_iff hM hw hQ hq hr hc hd).mpr hqr p,
        (principal_subset_iff hM hw hQ hr hq hd hc).mpr hrq p⟩)

def CutCarrier (hM : FirstOrder.Theory.Models M nativeZF) (w Q R : M.Carrier .set) : Prop :=
  ∀ c, (Project.FirstOrderSemantics.reduct M).mem c R ↔ Cut hM w Q c

def cutCarrier {m : Nat} (w Q R : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound R.succ)) (cut w.succ Q.succ 0))

theorem cutCarrier_freeClosed {m : Nat} (w Q R : Fin m) : (cutCarrier w Q R).FreeClosed := by
  simp -implicitDefEqProofs [cutCarrier,Definitional.Formula.FreeClosed,cut_freeClosed]

theorem cutCarrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R : Fin m) :
    Project.Formula.satisfies env (cutCarrier w Q R) ↔ CutCarrier hM (env.bound w) (env.bound Q) (env.bound R) := by
  simp only [cutCarrier,CutCarrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,cut_semantics hM,Project.Term.eval_bound]
  rfl

theorem exists_cutCarrier (hM : FirstOrder.Theory.Models M nativeZF) (w Q : M.Carrier .set) :
    ∃ R, CutCarrier hM w Q R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨power,hpower⟩ := ZF.exists_powerSet hZF Q
  let schema : Project.UnarySchema 2 := { body := cut 1 2 0, freeClosed := cut_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases w (fun _ => Q), free := fun _ => w }
  obtain ⟨R,hR⟩ := ZF.separation_exists_d hZF schema env power
  have he : ∀ c, Project.Formula.satisfies (env.push c) schema.body ↔ Cut hM w Q c :=
    fun c => cut_semantics hM (env.push c) 1 2 0
  exact ⟨R,fun c => ⟨fun h => (he c).mp ((hR c).mp h).2,
    fun h => (hR c).mpr ⟨(hpower c).mpr h.1,(he c).mpr h⟩⟩⟩

theorem cuts_total (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hc : Cut hM w Q c) (hd : Cut hM w Q d) : Subset c d ∨ Subset d c := by
  classical
  by_cases h : Subset c d
  · exact Or.inl h
  · right
    obtain ⟨p,hp⟩ := Classical.not_forall.mp h
    have hpc : (Project.FirstOrderSemantics.reduct M).mem p c := Classical.byContradiction (fun hn => hp (fun h => (hn h).elim))
    have hpd : ¬ (Project.FirstOrderSemantics.reduct M).mem p d := fun hd => hp (fun _ => hd)
    intro q hqd
    rcases le_total hM hw ((hQ q).mp (hd.1 q hqd)) ((hQ p).mp (hc.1 p hpc)) with hqp | hpq
    · exact hc.2.1 q p hpc hqp
    · exact (hpd (hd.2.1 p q hqd hpq)).elim

/-- An internal union gives the least upper bound of every internally bounded
set of cuts. No enumeration, external standardness or choice function occurs. -/
theorem bounded_union (hM : FirstOrder.Theory.Models M nativeZF) {w Q R family upper : M.Carrier .set}
    (hR : CutCarrier hM w Q R) (hf : Subset family R) (hu : Cut hM w Q upper)
    (hbound : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → Subset c upper) :
    ∃ s, Cut hM w Q s ∧
      (∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → Subset c s) ∧
      (∀ t, (∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → Subset c t) → Subset s t) := by
  obtain ⟨s,hs⟩ := KP.exists_union (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) family
  have hc : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → Cut hM w Q c :=
    fun c hc => (hR c).mp (hf c hc)
  refine ⟨s,⟨?_,?_,?_,?_⟩,?_,?_⟩
  · intro p hp
    obtain ⟨c,hcf,hpc⟩ := (hs p).mp hp
    exact (hc c hcf).1 p hpc
  · intro p q hqs hpq
    obtain ⟨c,hcf,hqc⟩ := (hs q).mp hqs
    exact (hs p).mpr ⟨c,hcf,(hc c hcf).2.1 p q hqc hpq⟩
  · intro p hp
    obtain ⟨c,hcf,hpc⟩ := (hs p).mp hp
    obtain ⟨q,hqc,hpq⟩ := (hc c hcf).2.2.1 p hpc
    exact ⟨q,(hs q).mpr ⟨c,hcf,hqc⟩,hpq⟩
  · obtain ⟨q,hq,hnq⟩ := hu.2.2.2
    refine ⟨q,hq,fun hqs => ?_⟩
    obtain ⟨c,hcf,hqc⟩ := (hs q).mp hqs
    exact hnq (hbound c hcf q hqc)
  · exact fun c hcf p hpc => (hs p).mpr ⟨c,hcf,hpc⟩
  · intro t ht p hp
    obtain ⟨c,hcf,hpc⟩ := (hs p).mp hp
    exact ht c hcf p hpc

def UpperBound (family upper : M.Carrier .set) : Prop :=
  ∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → Subset c upper

def upperBound {m : Nat} (family upper : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound family.succ))
    (Project.Formula.subset (.bound 0) (.bound upper.succ)))

theorem upperBound_freeClosed {m : Nat} (family upper : Fin m) : (upperBound family upper).FreeClosed := by
  simp -implicitDefEqProofs [upperBound,Definitional.Formula.FreeClosed]

theorem upperBound_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (family upper : Fin m) : Project.Formula.satisfies env (upperBound family upper) ↔
      UpperBound (env.bound family) (env.bound upper) := by
  simp only [upperBound,UpperBound,Subset,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

def supremum {m : Nat} (family s : Fin m) : Project.Formula 1 m :=
  .conj (upperBound family s) (.forallE (.imp (upperBound family.succ 0)
    (Project.Formula.subset (.bound s.succ) (.bound 0))))

theorem supremum_freeClosed {m : Nat} (family s : Fin m) : (supremum family s).FreeClosed := by
  simp -implicitDefEqProofs [supremum,Definitional.Formula.FreeClosed,upperBound_freeClosed]

theorem supremum_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (family s : Fin m) : Project.Formula.satisfies env (supremum family s) ↔
      UpperBound (env.bound family) (env.bound s) ∧
        ∀ t, UpperBound (env.bound family) t → Subset (env.bound s) t := by
  simp only [supremum,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,upperBound_semantics,
    Project.Term.eval_bound,Subset]
  rfl

def boundedComplete {m : Nat} (R : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (Project.Formula.subset (.bound 1) (.bound R.succ.succ))
    (.imp (.mem (.bound 0) (.bound R.succ.succ)) (.imp (upperBound (1 : Fin (m+2)) 0)
      (.existsE (.conj (.mem (.bound 0) (.bound R.succ.succ.succ)) (supremum (2 : Fin (m+3)) 0)))))))

theorem boundedComplete_freeClosed {m : Nat} (R : Fin m) : (boundedComplete R).FreeClosed := by
  simp -implicitDefEqProofs [boundedComplete,Definitional.Formula.FreeClosed,upperBound_freeClosed,supremum_freeClosed]

theorem boundedComplete_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (R : Fin m) : Project.Formula.satisfies env (boundedComplete R) ↔
      ∀ family upper, Subset family (env.bound R) → (Project.FirstOrderSemantics.reduct M).mem upper (env.bound R) →
        UpperBound family upper → ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (env.bound R) ∧
          UpperBound family s ∧ ∀ t, UpperBound family t → Subset s t := by
  simp only [boundedComplete,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    upperBound_semantics,supremum_semantics,Project.Term.eval_bound,Subset]
  rfl

def embedding {m : Nat} (w Q R : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound Q.succ)) (.existsE
    (.conj (.mem (.bound 0) (.bound R.succ.succ)) (principal w.succ.succ Q.succ.succ 1 0))))

theorem embedding_freeClosed {m : Nat} (w Q R : Fin m) : (embedding w Q R).FreeClosed := by
  simp -implicitDefEqProofs [embedding,Definitional.Formula.FreeClosed,principal_freeClosed]

theorem embedding_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R : Fin m) :
    Project.Formula.satisfies env (embedding w Q R) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env.bound Q) →
        ∃ c, (Project.FirstOrderSemantics.reduct M).mem c (env.bound R) ∧
          Principal hM (env.bound w) (env.bound Q) q c := by
  simp only [embedding,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,principal_semantics hM,Project.Term.eval_bound]
  rfl

def linearOrder {m : Nat} (R : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound R.succ.succ))
    (.imp (.mem (.bound 0) (.bound R.succ.succ))
      (.conj (.disj (Project.Formula.subset (.bound 1) (.bound 0)) (Project.Formula.subset (.bound 0) (.bound 1)))
        (.imp (Project.Formula.subset (.bound 1) (.bound 0))
          (.imp (Project.Formula.subset (.bound 0) (.bound 1)) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))

theorem linearOrder_freeClosed {m : Nat} (R : Fin m) : (linearOrder R).FreeClosed := by
  simp -implicitDefEqProofs [linearOrder,Definitional.Formula.FreeClosed]

theorem linearOrder_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Fin m) :
    Project.Formula.satisfies env (linearOrder R) ↔
      ∀ c d, (Project.FirstOrderSemantics.reduct M).mem c (env.bound R) →
        (Project.FirstOrderSemantics.reduct M).mem d (env.bound R) →
        (Subset c d ∨ Subset d c) ∧ (Subset c d → Subset d c → c = d) := by
  simp only [linearOrder,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,Subset]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.conj (carrier (2 : Fin 3) 1) (.conj (cutCarrier (2 : Fin 3) 1 0)
      (.conj (embedding (2 : Fin 3) 1 0) (.conj (linearOrder (0 : Fin 3)) (boundedComplete (0 : Fin 3)))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed,
    cutCarrier_freeClosed,embedding_freeClosed,linearOrder_freeClosed,boundedComplete_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    carrier_semantics hM,cutCarrier_semantics hM,embedding_semantics hM,linearOrder_semantics hM,boundedComplete_semantics]
  obtain ⟨Q,hQ⟩ := exists_carrier hM (bound 0)
  obtain ⟨R,hR⟩ := exists_cutCarrier hM (bound 0) Q
  refine ⟨Q,R,hQ,hR,?_,?_,?_⟩
  · intro q hq
    obtain ⟨c,hc⟩ := exists_principal hM (bound 0) Q q
    exact ⟨c,(hR c).mpr (principal_cut hM hw hQ hq hc),hc⟩
  · intro c d hc hd
    exact ⟨cuts_total hM hw hQ ((hR c).mp hc) ((hR d).mp hd),fun hcd hdc =>
      (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => ⟨hcd p,hdc p⟩)⟩
  · intro family upper hf hu hb
    obtain ⟨s,hs,hup,hleast⟩ := bounded_union hM hR hf ((hR upper).mp hu) hb
    exact ⟨s,(hR s).mpr hs,hup,hleast⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

/-- Both order reflection and equality of equivalent fraction representations. -/
def comparisonSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (carrier (0 : Fin 6) 1) (.imp (.mem (.bound 2) (.bound 1)) (.imp (.mem (.bound 3) (.bound 1))
      (.imp (principal (0 : Fin 6) 1 2 4) (.imp (principal (0 : Fin 6) 1 3 5)
        (.conj (.iff (Project.Formula.subset (.bound 4) (.bound 5)) (le (0 : Fin 6) 2 3))
          (.iff (Project.Formula.extensionalEq (.bound 4) (.bound 5))
            (.conj (le (0 : Fin 6) 2 3) (le (0 : Fin 6) 3 2))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed,principal_freeClosed,le_freeClosed]

theorem comparison_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence comparisonSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) comparisonSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    carrier_semantics hM,principal_semantics hM,le_semantics hM,Project.Term.eval_bound]
  exact fun hw hQ hq hr hc hd => ⟨principal_subset_iff hM hw hQ hq hr hc hd,principal_eq_iff hM hw hQ hq hr hc hd⟩

theorem comparison_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence comparisonSentence) := ModelTransfer.derives (fun _ hM => comparison_models hM)

end PPAC.Migration.ConstructionRealCuts
