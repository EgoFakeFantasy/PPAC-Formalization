/- Pinned ForcingQuotient.principalFilter/eqG_principal and
PersistentCodes.principalFilter_move. Consumers: actual Works and
same_iff_represents_eq. Uses the existing Cohen carrier, atomic relations,
condition coding, Separation and permutation/image interfaces. -/
import PPAC.Migration.ForcingLocalTransport
import PPAC.Migration.GodelDefRecursion

namespace PPAC.Migration.ForcingPrincipalFilter
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingPowerName (Subset)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingSupportingRoot (Code code_mem exists_code code_le)
open ForcingLocalAtomic (CohenFilter EqG)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Principal (X d g : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q g ↔
    (Project.FirstOrderSemantics.reduct M).mem q X ∧ Subset q d

def principal {m : Nat} (X d g : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound g.succ))
    (.conj (.mem (.bound 0) (.bound X.succ)) (Project.Formula.subset (.bound 0) (.bound d.succ))))

theorem principal_freeClosed {m : Nat} (X d g : Fin m) : (principal X d g).FreeClosed := by
  simp [principal,Definitional.Formula.FreeClosed]

theorem principal_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (X d g : Fin m) :
    Project.Formula.satisfies env (principal X d g) ↔ Principal (env.bound X) (env.bound d) (env.bound g) := by
  simp only [principal,Principal,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

theorem exists_principal (hM : FirstOrder.Theory.Models M nativeZF) (X d : M.Carrier .set) :
    ∃ g, Principal X d g := by
  let schema : Project.UnarySchema 1 := {
    body := Project.Formula.subset (.bound 0) (.bound 1)
    freeClosed := by simp }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {bound := fun _ => d,free := fun _ => d}
  obtain ⟨g,hg⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env X
  refine ⟨g,fun q => ?_⟩
  refine (hg q).trans (and_congr_right fun _ => ?_)
  simp only [schema,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

theorem principal_unique (hM : FirstOrder.Theory.Models M nativeZF) {X d g h : M.Carrier .set}
    (hg : Principal X d g) (hh : Principal X d h) : g = h :=
  (ModelTransfer.extensionality hM).eq_of_same_members g h (fun q => (hg q).trans (hh q).symm)

theorem principal_filter {X d g : M.Carrier .set}
    (hd : (Project.FirstOrderSemantics.reduct M).mem d X) (hg : Principal X d g) : CohenFilter X g := by
  have hdg := (hg d).mpr ⟨hd,fun _ h => h⟩
  refine ⟨fun q hq => ((hg q).mp hq).1,⟨d,hdg⟩,?_,?_⟩
  · intro q r hq hr hrq
    exact (hg r).mpr ⟨hr,fun z hz => ((hg q).mp hq).2 z (hrq z hz)⟩
  · intro q r hq hr
    exact ⟨d,hdg,((hg q).mp hq).2,((hg r).mp hr).2⟩

def EqF {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W d r sigma tau : M.Carrier .set) : Prop :=
  ∃ z, Code z d r ∧ Forces true R env W sigma tau z

def eqF {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W d r sigma tau : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 d.succ r.succ))
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun i => (base i).succ) W.succ sigma.succ tau.succ 0)))

theorem eqF_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W d r sigma tau : Fin m) : (eqF R base W d r sigma tau).FreeClosed := by
  simp [eqF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem eqF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (R : Formula (k+2)) (base : Fin k → Fin m) (W d r sigma tau : Fin m) :
    Project.Formula.satisfies env (eqF R base W d r sigma tau) ↔
      EqF R (fun j => env.bound (base j)) (env.bound W) (env.bound d) (env.bound r) (env.bound sigma) (env.bound tau) := by
  simp only [eqF,EqF,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M)]
  rfl

theorem eqG_principal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e d g r sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hg : Principal (env (rho 3)) d g) :
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau ↔
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau := by
  constructor
  · rintro ⟨q,z,hq,hz,he⟩
    obtain ⟨t,ht⟩ := exists_code hM d r
    have htW := code_mem hp ((hp.2.2.1 d).mp hd) hr ht
    have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
    exact ⟨t,ht,ForcingAtomicBasic.eq_mono hM hpre htW
      ((orderFormula_semantics env (rho 0) mul t z).mpr ((code_le ht hz).mpr
        ⟨((hg q).mp hq).2,ForcingDiagramPoset.le_refl hm hr⟩)) he⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨d,z,(hg d).mpr ⟨hd,fun _ h => h⟩,hz,he⟩

theorem principal_move {X ac d d' g g' : M.Carrier .set}
    (hac : ForcingConditionGraphs.Permutation X ac) (ho : ForcingCohenOrderAction.OrderPreserving ac)
    (hdd : PureKuratowski.PairMember M d d' ac)
    (hg : Principal X d g) (hg' : Principal X d' g') : ForcingStabilizerTransport.Image ac g g' := by
  intro q'
  constructor
  · intro hq'
    obtain ⟨q,hq,hqq⟩ := hac.2.2 q' ((hg' q').mp hq').1
    exact ⟨q,(hg q).mpr ⟨hq,(ho d q d' q' hdd hqq).mp ((hg' q').mp hq').2⟩,hqq⟩
  · rintro ⟨q,hq,hqq⟩
    exact (hg' q').mpr ⟨hac.1.2 q q' hqq,(ho d q d' q' hdd hqq).mpr ((hg q).mp hq).2⟩


theorem eqF_refl (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e d r : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r) (sigma : M.Carrier .set) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma sigma := by
  obtain ⟨g,hg⟩ := exists_principal hM (env (rho 3)) d
  exact (eqG_principal hM env rho mul hm hp hd hr hg).mp
    (ForcingLocalAtomic.eqG_refl hM env rho mul hm hp (principal_filter hd hg) hr sigma)

theorem eqF_symm (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W d r sigma tau : M.Carrier .set}
    (h : EqF R env W d r sigma tau) : EqF R env W d r tau sigma := by
  obtain ⟨z,hz,he⟩ := h
  exact ⟨z,hz,ForcingAtomicBasic.eq_symm hM he⟩

theorem eqF_trans (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e d r sigma tau upsilon : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (ha : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau)
    (hb : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r tau upsilon) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma upsilon := by
  obtain ⟨g,hg⟩ := exists_principal hM (env (rho 3)) d
  exact (eqG_principal hM env rho mul hm hp hd hr hg).mp
    (ForcingLocalAtomic.eqG_trans hM env rho mul hm hp (principal_filter hd hg) hr
      ((eqG_principal hM env rho mul hm hp hd hr hg).mpr ha)
      ((eqG_principal hM env rho mul hm hp hd hr hg).mpr hb))

theorem eqF_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one d e r sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r) (hde : Subset d e)
    (h : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) e r sigma tau := by
  obtain ⟨z,hz,hf⟩ := h
  obtain ⟨t,ht⟩ := exists_code hM e r
  exact ⟨t,ht,ForcingAtomicBasic.eq_mono hM
    (ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2)
    (code_mem hp ((hp.2.2.1 e).mp he) hr ht)
    ((orderFormula_semantics env (rho 0) mul t z).mpr ((code_le ht hz).mpr ⟨hde,ForcingDiagramPoset.le_refl hm hr⟩)) hf⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul e d : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
        (.imp (.mem (.bound d) (.bound (rho 3)))
          (.existsE (.conj (principal (rho 3).succ d.succ 0)
            (.conj (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3).succ 0))
              (.forallE (.forallE (.forallE
                (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection 2 (rho 0).succ.succ.succ.succ I.succ.succ.succ.succ))
                  (.iff (ProjectSyntax.encode id (ForcingLocalAtomic.eqG (orderFormula (rho 0) mul)
                    (fun j => j.succ.succ.succ.succ) (rho 6).succ.succ.succ.succ 3 2 1 0))
                    (eqF (orderFormula (rho 0) mul) (fun j => j.succ.succ.succ.succ)
                      (rho 6).succ.succ.succ.succ d.succ.succ.succ.succ 2 1 0))))))))))))
  freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,principal_freeClosed,eqF_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul e d : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w mul e d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingLocalAtomic.eqG_semantics (M := M),principal_semantics,eqF_semantics hM]
  intro hm hp hd
  obtain ⟨g,hg⟩ := exists_principal hM (env (rho 3)) (env d)
  exact ⟨g,hg,principal_filter hd hg,fun r sigma tau hr => eqG_principal hM env rho mul hm hp hd hr hg⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul e d : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w mul e d)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mul e d hM)

def moveSentence {m : Nat} (X ac d d' g g' : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation X ac))
      (.imp (ProjectSyntax.encode id (ForcingCohenOrderAction.orderPreserving ac))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d d'))
          (.imp (principal X d g) (.imp (principal X d' g')
            (ProjectSyntax.encode id (ForcingStabilizerTransport.image ac g g')))))))
  freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,principal_freeClosed]

theorem move_models {m : Nat} (X ac d d' g g' : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (moveSentence X ac d d' g g')).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingCohenOrderAction.orderPreserving_semantics (M := M),
    KuratowskiZF.source_edge,ForcingStabilizerTransport.image_semantics (M := M),principal_semantics]
  exact principal_move

theorem move_kernel_certificate {m : Nat} (X ac d d' g g' : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (moveSentence X ac d d' g g')) :=
  ModelTransfer.derives (fun _ hM => move_models X ac d d' g g' hM)

end PPAC.Migration.ForcingPrincipalFilter
