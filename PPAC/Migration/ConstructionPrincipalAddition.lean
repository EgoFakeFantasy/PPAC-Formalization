/- Rational principal-cut addition used by the source Base.margin arithmetic.
The operation is independent of fraction codes. This is not yet addition of
arbitrary cuts, nor a complete ordered real field. -/
import PPAC.Migration.ConstructionFractionAddition
import PPAC.Migration.ConstructionCutWeights

namespace PPAC.Migration.ConstructionPrincipalAddition
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionAddition ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Represented (hM : FirstOrder.Theory.Models M nativeZF) (w Q c : M.Carrier .set) : Prop :=
  ∃ q, (Project.FirstOrderSemantics.reduct M).mem q Q ∧ Principal hM w Q q c

def PrincipalAdd (hM : FirstOrder.Theory.Models M nativeZF) (w Q c d e : M.Carrier .set) : Prop :=
  ∃ q r s, (Project.FirstOrderSemantics.reduct M).mem q Q ∧ (Project.FirstOrderSemantics.reduct M).mem r Q ∧
    Principal hM w Q q c ∧ Principal hM w Q r d ∧ Sum hM w q r s ∧ Principal hM w Q s e

theorem output_represented (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d e : M.Carrier .set}
    (hQ : Carrier w Q) (he : PrincipalAdd hM w Q c d e) : Represented hM w Q e := by
  obtain ⟨q,r,s,_,_,_,_,hs,he⟩ := he
  obtain ⟨a,b,c,d,n,den,_,_,hc,_⟩ := hs
  exact ⟨s,(hQ s).mpr ⟨n,den,hc⟩,he⟩

theorem add_exists (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hc : Represented hM w Q c) (hd : Represented hM w Q d) : ∃ e, PrincipalAdd hM w Q c d e := by
  obtain ⟨q,hq,hc⟩ := hc
  obtain ⟨r,hr,hd⟩ := hd
  obtain ⟨s,hs⟩ := sum_exists hM hw ((hQ q).mp hq) ((hQ r).mp hr)
  obtain ⟨e,he⟩ := exists_principal hM w Q s
  exact ⟨e,q,r,s,hq,hr,hc,hd,hs,he⟩

theorem add_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d e e' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (he : PrincipalAdd hM w Q c d e) (he' : PrincipalAdd hM w Q c d e') : e = e' := by
  obtain ⟨q,r,s,hq,hr,hc,hd,hs,he⟩ := he
  obtain ⟨q',r',s',hq',hr',hc',hd',hs',he'⟩ := he'
  have hqq := (principal_eq_iff hM hw hQ hq hq' hc hc').mp rfl
  have hrr := (principal_eq_iff hM hw hQ hr hr' hd hd').mp rfl
  exact principal_sum_independent hM hw hQ hs hs' hqq hrr he he'

theorem add_comm (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (he : PrincipalAdd hM w Q c d e) : PrincipalAdd hM w Q d c e := by
  obtain ⟨q,r,s,hq,hr,hc,hd,hs,he⟩ := he
  exact ⟨r,q,s,hr,hq,hd,hc,sum_comm hM hw hs,he⟩

/-- Cancellation holds for the actual cut objects, not merely chosen codes. -/
theorem add_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w Q c c' d e e' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (he : PrincipalAdd hM w Q c d e) (he' : PrincipalAdd hM w Q c' d e') : Subset e e' ↔ Subset c c' := by
  obtain ⟨q,r,s,hq,hr,hc,hd,hs,he⟩ := he
  obtain ⟨q',r',s',hq',hr',hc',hd',hs',he'⟩ := he'
  have hrr := (principal_eq_iff hM hw hQ hr hr' hd hd').mp rfl
  obtain ⟨mid,hm⟩ := sum_exists hM hw ((hQ q').mp hq') ((hQ r).mp hr)
  obtain ⟨t,ht⟩ := exists_principal hM w Q mid
  have hrefl := le_refl hM hw ((hQ q').mp hq')
  have het : t = e' := principal_sum_independent hM hw hQ hm hs' ⟨hrefl,hrefl⟩ hrr ht he'
  have hmCopy := hm
  have hsCopy := hs
  obtain ⟨a,b,c0,d0,n,den,_,_,hsc,_⟩ := hsCopy
  obtain ⟨a',b',c0',d0',n',den',_,_,hmc,_⟩ := hmCopy
  rw [← het]
  exact (principal_subset_iff hM hw hQ ((hQ s).mpr ⟨n,den,hsc⟩) ((hQ mid).mpr ⟨n',den',hmc⟩) he ht).trans
    ((sum_right_le_iff hM hw hs hm).trans (principal_subset_iff hM hw hQ hq hq' hc hc').symm)

def represented {m : Nat} (w Q c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound Q.succ)) (principal w.succ Q.succ 0 c.succ))

theorem represented_freeClosed {m : Nat} (w Q c : Fin m) : (represented w Q c).FreeClosed := by
  simp -implicitDefEqProofs [represented,Definitional.Formula.FreeClosed,principal_freeClosed]

theorem represented_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q c : Fin m) :
    Project.Formula.satisfies env (represented w Q c) ↔ Represented hM (env.bound w) (env.bound Q) (env.bound c) := by
  simp only [represented,Represented,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,principal_semantics hM,Project.Term.eval_bound]
  rfl

def principalAdd {m : Nat} (w Q c d e : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound Q.succ.succ.succ))
    (.conj (.mem (.bound 1) (.bound Q.succ.succ.succ))
      (.conj (principal w.succ.succ.succ Q.succ.succ.succ 2 c.succ.succ.succ)
        (.conj (principal w.succ.succ.succ Q.succ.succ.succ 1 d.succ.succ.succ)
          (.conj (sum w.succ.succ.succ 2 1 0) (principal w.succ.succ.succ Q.succ.succ.succ 0 e.succ.succ.succ))))))))

theorem principalAdd_freeClosed {m : Nat} (w Q c d e : Fin m) : (principalAdd w Q c d e).FreeClosed := by
  simp -implicitDefEqProofs [principalAdd,Definitional.Formula.FreeClosed,principal_freeClosed,sum_freeClosed]

theorem principalAdd_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q c d e : Fin m) :
    Project.Formula.satisfies env (principalAdd w Q c d e) ↔
      PrincipalAdd hM (env.bound w) (env.bound Q) (env.bound c) (env.bound d) (env.bound e) := by
  simp only [principalAdd,PrincipalAdd,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,principal_semantics hM,sum_semantics hM,Project.Term.eval_bound]
  rfl

def totalUnique {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (represented w.succ.succ Q.succ.succ 1) (.imp (represented w.succ.succ Q.succ.succ 0)
    (.existsE (.conj (principalAdd w.succ.succ.succ Q.succ.succ.succ 2 1 0)
      (.conj (represented w.succ.succ.succ Q.succ.succ.succ 0) (.forallE (.imp
        (principalAdd w.succ.succ.succ.succ Q.succ.succ.succ.succ 3 2 0)
        (Project.Formula.extensionalEq (.bound 0) (.bound 1))))))))))

theorem totalUnique_freeClosed {m : Nat} (w Q : Fin m) : (totalUnique w Q).FreeClosed := by
  simp -implicitDefEqProofs [totalUnique,Definitional.Formula.FreeClosed,represented_freeClosed,principalAdd_freeClosed]

theorem totalUnique_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (totalUnique w Q) ↔ ∀ c d,
      Represented hM (env.bound w) (env.bound Q) c → Represented hM (env.bound w) (env.bound Q) d →
        ∃ e, PrincipalAdd hM (env.bound w) (env.bound Q) c d e ∧ Represented hM (env.bound w) (env.bound Q) e ∧
          ∀ t, PrincipalAdd hM (env.bound w) (env.bound Q) c d t → t = e := by
  simp only [totalUnique,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    represented_semantics hM,principalAdd_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def commutative {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (principalAdd w.succ.succ.succ Q.succ.succ.succ 2 1 0)
    (principalAdd w.succ.succ.succ Q.succ.succ.succ 1 2 0))))

theorem commutative_freeClosed {m : Nat} (w Q : Fin m) : (commutative w Q).FreeClosed := by
  simp -implicitDefEqProofs [commutative,Definitional.Formula.FreeClosed,principalAdd_freeClosed]

theorem commutative_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (commutative w Q) ↔ ∀ c d e,
      PrincipalAdd hM (env.bound w) (env.bound Q) c d e → PrincipalAdd hM (env.bound w) (env.bound Q) d c e := by
  simp only [commutative,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,principalAdd_semantics hM]
  rfl

def orderReflection {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (principalAdd w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 4 2 1)
    (.imp (principalAdd w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 3 2 0)
      (.iff (Project.Formula.subset (.bound 1) (.bound 0)) (Project.Formula.subset (.bound 4) (.bound 3)))))))))

theorem orderReflection_freeClosed {m : Nat} (w Q : Fin m) : (orderReflection w Q).FreeClosed := by
  simp -implicitDefEqProofs [orderReflection,Definitional.Formula.FreeClosed,principalAdd_freeClosed]

theorem orderReflection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (orderReflection w Q) ↔ ∀ c c' d e e',
      PrincipalAdd hM (env.bound w) (env.bound Q) c d e → PrincipalAdd hM (env.bound w) (env.bound Q) c' d e' →
        (Subset e e' ↔ Subset c c') := by
  simp only [orderReflection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_subset_iff,principalAdd_semantics hM,
    Project.Term.eval_bound,ConstructionRealCuts.Subset]
  rfl

def additionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 2 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (carrier (0 : Fin 2) 1) (.conj (totalUnique (0 : Fin 2) 1)
      (.conj (commutative (0 : Fin 2) 1) (orderReflection (0 : Fin 2) 1)))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed,
    totalUnique_freeClosed,commutative_freeClosed,orderReflection_freeClosed]

theorem addition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence additionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) additionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_conj_iff,carrier_semantics hM,totalUnique_semantics hM,commutative_semantics hM,orderReflection_semantics hM]
  intro hw hQ
  refine ⟨?_,fun _ _ _ he => add_comm hM hw he,fun _ _ _ _ _ he he' => add_le_iff hM hw hQ he he'⟩
  intro c d hc hd
  obtain ⟨e,he⟩ := add_exists hM hw hQ hc hd
  exact ⟨e,he,output_represented hM hQ he,fun _ ht => add_unique hM hw hQ ht he⟩

theorem addition_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence additionSentence) := ModelTransfer.derives (fun _ hM => addition_models hM)

/-- The actual source weight values are in the rational principal-cut domain. -/
theorem source_weights_represented (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q height cost : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : ConstructionBaseWeights.Digits w one two three)
    (hQ : Carrier w Q) (hh : ConstructionCutWeights.Graph hM true w one two one Q height)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost) :
    (∀ n c, PureKuratowski.PairMember M n c height → Represented hM w Q c) ∧
    (∀ n c, PureKuratowski.PairMember M n c cost → Represented hM w Q c) := by
  have hon : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := by
    obtain ⟨zero,_,hs⟩ := hd.2.2.2.1
    exact ⟨zero,hs.predecessor_mem⟩
  have hthn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z three := ⟨two,hd.2.2.2.2.2.predecessor_mem⟩
  constructor
  · intro n c hnc
    obtain ⟨hn,q,hq,hprincipal⟩ := (hh n c).mp hnc
    exact ⟨q,proper_in_carrier hQ (ConstructionBaseWeights.weight_proper hM hw hd.2.2.2.1 hd.2.1
      hd.2.2.2.2.1.predecessor_mem hd.1 hon hn hq),hprincipal⟩
  · intro n c hnc
    obtain ⟨hn,q,hq,hprincipal⟩ := (hc n c).mp hnc
    exact ⟨q,proper_in_carrier hQ (ConstructionBaseWeights.weight_proper hM hw hd.2.2.2.1 hd.2.1
      hd.2.2.2.2.1.predecessor_mem hd.2.2.1 hthn hn hq),hprincipal⟩

theorem source_weight_addition (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q height cost n m a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : ConstructionBaseWeights.Digits w one two three)
    (hQ : Carrier w Q) (hh : ConstructionCutWeights.Graph hM true w one two one Q height)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (ha : PureKuratowski.PairMember M n a height) (hb : PureKuratowski.PairMember M m b cost) :
    ∃ e, PrincipalAdd hM w Q a b e ∧ ∀ t, PrincipalAdd hM w Q a b t → t = e := by
  have hr := source_weights_represented hM hw hd hQ hh hc
  obtain ⟨e,he⟩ := add_exists hM hw hQ (hr.1 n a ha) (hr.2 m b hb)
  exact ⟨e,he,fun _ ht => add_unique hM hw hQ ht he⟩

def weightAdditionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (ConstructionBaseWeights.digits (0 : Fin 11) 1 2 3) (.imp (carrier (0 : Fin 11) 4)
      (.imp (ConstructionCutWeights.graph true (0 : Fin 11) 1 2 1 4 5)
        (.imp (ConstructionCutWeights.graph false (0 : Fin 11) 1 2 3 4 6)
          (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 11) 7 9))
            (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (6 : Fin 11) 8 10))
              (.existsE (.conj (principalAdd (1 : Fin 12) 5 10 11 0)
                (.forallE (.imp (principalAdd (2 : Fin 13) 6 11 12 0)
                  (Project.Formula.extensionalEq (.bound 0) (.bound 1)))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBaseWeights.digits_freeClosed,
    carrier_freeClosed,ConstructionCutWeights.graph_freeClosed,ProjectSyntax.freeClosed,principalAdd_freeClosed]

theorem weightAddition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence weightAdditionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) weightAdditionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionBaseWeights.digits_semantics,carrier_semantics hM,ConstructionCutWeights.graph_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,principalAdd_semantics hM,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact fun hw hd hQ hh hc ha hb => source_weight_addition hM hw hd hQ hh hc ha hb

theorem weightAddition_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence weightAdditionSentence) := ModelTransfer.derives (fun _ hM => weightAddition_models hM)

end PPAC.Migration.ConstructionPrincipalAddition
