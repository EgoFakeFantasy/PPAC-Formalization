/- Pinned ForcingTruth.forceFormula_rename/raise/instantiate and forcing_sound.
All 19 original rules are replayed. The output is a nativeZF derivation for each
fixed finite premise list and source proof. This is not yet a theorem about
arbitrary internal/nonstandard proof codes or about the target ZF/PP axioms. -/
import PPAC.Migration.ForcingFormula
import PPAC.Migration.DefinableMinimaChoice
import PPAC.Migration.SourceDerivation

namespace PPAC.Migration.ForcingSound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingFormula (Force formula)
open ForcingAtomicBasic (PreorderOn)
open ForcingClassEvaluation (Predicate)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem rename (hM : FirstOrder.Theory.Models M nativeZF) {k n m : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula n) (r : Fin n → Fin m)
    (v : Fin m → M.Carrier .set) (p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Force R H params v P p (phi.rename r) ↔ Force R H params (fun i => v (r i)) P p phi := by
  induction phi generalizing m p with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | conj a b ia ib => exact and_congr (ia r v p hp) (ib r v p hp)
  | imp a b ia ib =>
    simp only [Source.Formula.rename,ForcingFormula.force_imp hM hpre hp]
    constructor
    · intro h q hq hqp ha
      exact (ib r v q hq).mp (h q hq hqp ((ia r v q hq).mpr ha))
    · intro h q hq hqp ha
      exact (ib r v q hq).mpr (h q hq hqp ((ia r v q hq).mp ha))
  | disj a b ia ib =>
    simp only [Source.Formula.rename,ForcingFormula.force_disj]
    constructor
    · intro h q hq hqp
      obtain ⟨s,hs,hsq,ha | hb⟩ := h q hq hqp
      · exact ⟨s,hs,hsq,Or.inl ((ia r v s hs).mp ha)⟩
      · exact ⟨s,hs,hsq,Or.inr ((ib r v s hs).mp hb)⟩
    · intro h q hq hqp
      obtain ⟨s,hs,hsq,ha | hb⟩ := h q hq hqp
      · exact ⟨s,hs,hsq,Or.inl ((ia r v s hs).mpr ha)⟩
      · exact ⟨s,hs,hsq,Or.inr ((ib r v s hs).mpr hb)⟩
  | all a ia =>
    simp only [Source.Formula.rename,ForcingFormula.force_all hM hpre hp]
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    simpa only [DefinableMinimaChoice.lift_assignment] using
      ia (Formula.liftRen r) (Fin.lastCases x v) p hp
  | ex a ia =>
    have hi : ∀ x s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P →
        (Force R H params (Fin.lastCases x v) P s (a.rename (Formula.liftRen r)) ↔
          Force R H params (Fin.lastCases x (fun i => v (r i))) P s a) := by
      intro x s hs
      simpa only [DefinableMinimaChoice.lift_assignment] using
        ia (Formula.liftRen r) (Fin.lastCases x v) s hs
    constructor
    · intro h q hq hqp
      obtain ⟨s,hs,hsq,x,hx,ha⟩ := h q hq hqp
      exact ⟨s,hs,hsq,x,hx,(hi x s hs).mp ha⟩
    · intro h q hq hqp
      obtain ⟨s,hs,hsq,x,hx,ha⟩ := h q hq hqp
      exact ⟨s,hs,hsq,x,hx,(hi x s hs).mpr ha⟩

theorem raise (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula n) (v : Fin n → M.Carrier .set)
    (x p : M.Carrier .set) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Force R H params (Fin.lastCases x v) P p phi.raise ↔ Force R H params v P p phi := by
  simpa only [Source.Formula.raise,Fin.lastCases_castSucc] using rename hM (H := H) hpre phi Fin.castSucc (Fin.lastCases x v) p hp

theorem instantiate (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula (n+1)) (t : Fin n) (v : Fin n → M.Carrier .set)
    (p : M.Carrier .set) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Force R H params v P p (phi.instantiate t) ↔ Force R H params (Fin.lastCases (v t) v) P p phi := by
  have he : (fun i => v (Fin.lastCases t id i)) = Fin.lastCases (v t) v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  simpa only [Source.Formula.instantiate,he] using rename hM (H := H) hpre phi (Fin.lastCases t id) v p hp

/-- The original 19-rule induction, with explicit internal condition/domain guards. -/
theorem sound (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) {n : Nat} {Gamma : Source.Context n} {phi : Formula n}
    (d : Source.Derives Gamma phi) (v : Fin n → M.Carrier .set) (p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hv : ∀ i, Predicate H params (v i))
    (hGamma : ∀ psi, Gamma psi → Force R H params v P p psi) : Force R H params v P p phi := by
  induction d generalizing p with
  | hyp hh => exact hGamma _ hh
  | weaken hsub _ ih => exact ih v p hp hv (fun psi hpsi => hGamma psi (hsub psi hpsi))
  | impI _ ih =>
    apply (ForcingFormula.force_imp hM hpre hp v _ _).mpr
    intro q hq hqp hqa
    exact ih v q hq hv (fun psi hpsi => by
      rcases hpsi with he | hpsi
      · exact he.symm ▸ hqa
      · exact ForcingFormula.mono hM hpre psi v hp hq hqp (hGamma psi hpsi))
  | impE _ _ ia ib =>
    exact (ForcingFormula.force_imp hM hpre hp v _ _).mp (ia v p hp hv hGamma) p hp (hpre.1 p hp) (ib v p hp hv hGamma)
  | botE _ ih => exact (ih v p hp hv hGamma).elim
  | @classical n Gamma phi _ ih =>
    apply ForcingFormula.of_dense hM hpre phi v hp
    intro q hq hqp
    apply Classical.byContradiction
    intro hn
    have hneg : Force R H params v P q phi.neg :=
      (ForcingFormula.force_neg hM hpre hq v phi).mpr (fun r hr hrq hphi => hn ⟨r,hr,hrq,hphi⟩)
    exact ih v q hq hv (fun psi hpsi => by
      rcases hpsi with he | hpsi
      · exact he.symm ▸ hneg
      · exact ForcingFormula.mono hM hpre psi v hp hq hqp (hGamma psi hpsi))
  | conjI _ _ ia ib => exact ⟨ia v p hp hv hGamma,ib v p hp hv hGamma⟩
  | conjL _ ih => exact (ih v p hp hv hGamma).1
  | conjR _ ih => exact (ih v p hp hv hGamma).2
  | disjL _ ih =>
    apply (ForcingFormula.force_disj _ _ _ _ _ _ _ _).mpr
    intro q hq hqp
    exact ⟨q,hq,hpre.1 q hq,Or.inl (ForcingFormula.mono hM hpre _ v hp hq hqp (ih v p hp hv hGamma))⟩
  | disjR _ ih =>
    apply (ForcingFormula.force_disj _ _ _ _ _ _ _ _).mpr
    intro q hq hqp
    exact ⟨q,hq,hpre.1 q hq,Or.inr (ForcingFormula.mono hM hpre _ v hp hq hqp (ih v p hp hv hGamma))⟩
  | disjE _ _ _ ia ib ic =>
    apply ForcingFormula.of_dense hM hpre _ v hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,ha | hb⟩ := (ForcingFormula.force_disj _ _ _ _ _ _ _ _).mp (ia v p hp hv hGamma) q hq hqp
    · refine ⟨r,hr,hrq,ib v r hr hv ?_⟩
      intro psi hpsi
      rcases hpsi with he | hpsi
      · exact he.symm ▸ ha
      · exact ForcingFormula.mono hM hpre psi v hp hr (hpre.2 r q p hr hq hp hrq hqp) (hGamma psi hpsi)
    · refine ⟨r,hr,hrq,ic v r hr hv ?_⟩
      intro psi hpsi
      rcases hpsi with he | hpsi
      · exact he.symm ▸ hb
      · exact ForcingFormula.mono hM hpre psi v hp hr (hpre.2 r q p hr hq hp hrq hqp) (hGamma psi hpsi)
  | allI _ ih =>
    apply (ForcingFormula.force_all hM hpre hp v _).mpr
    intro x hx
    apply ih (Fin.lastCases x v) p hp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last] using hx
      · simpa only [Fin.lastCases_castSucc] using hv j
    · rintro psi ⟨chi,hchi,he⟩
      subst psi
      exact (raise hM hpre chi v x p hp).mpr (hGamma chi hchi)
  | allE t _ ih =>
    exact (instantiate hM hpre _ t v p hp).mpr
      ((ForcingFormula.force_all hM hpre hp v _).mp (ih v p hp hv hGamma) (v t) (hv t))
  | @exI n Gamma a t _ ih =>
    intro q hq hqp
    let vx : Fin (n+1) → M.Carrier .set := Fin.lastCases (v t) v
    have hinst : Force R H params vx P p a := (instantiate hM hpre a t v p hp).mp (ih v p hp hv hGamma)
    exact ⟨q,hq,hpre.1 q hq,v t,hv t,ForcingFormula.mono hM hpre a vx hp hq hqp hinst⟩
  | exE _ _ ia ib =>
    apply ForcingFormula.of_dense hM hpre _ v hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,x,hx,ha⟩ := ia v p hp hv hGamma q hq hqp
    refine ⟨r,hr,hrq,(raise hM hpre _ v x r hr).mp (ib (Fin.lastCases x v) r hr ?_ ?_)⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last] using hx
      · simpa only [Fin.lastCases_castSucc] using hv j
    · intro psi hpsi
      rcases hpsi with he | ⟨chi,hchi,he⟩
      · exact he.symm ▸ ha
      · subst psi
        exact (raise hM hpre chi v x r hr).mpr
          (ForcingFormula.mono hM hpre chi v hp hr (hpre.2 r q p hr hq hp hrq hqp) (hGamma chi hchi))
  | eqRefl t => exact ForcingAtomicBasic.eq_refl hM hpre (v t) p hp
  | eqSubst psi _ _ ia ib =>
    apply (instantiate hM hpre _ _ v p hp).mpr
    apply (ForcingFormula.tuple_congr hM hpre psi _ _ p hp ?_).mp
      ((instantiate hM hpre _ _ v p hp).mp (ib v p hp hv hGamma))
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last,ForcingFormula.force_equal] using ia v p hp hv hGamma
    · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (v j) p hp
  | rename r _ ih =>
    apply (rename hM hpre _ r v p hp).mpr
    apply ih (fun i => v (r i)) p hp (fun i => hv (r i))
    intro psi hpsi
    exact (rename hM hpre psi r v p hp).mp (hGamma _ ⟨psi,hpsi,rfl⟩)

/-- Finite packing in the existing source syntax, used only for the native certificate. -/
def conjunction {m : Nat} : List (Formula m) → Formula m
  | [] => .imp .bot .bot
  | p :: ps => p.conj (conjunction ps)

theorem conjunction_semantics {m : Nat} (env : Fin m → M.Carrier .set) (ps : List (Formula m)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (conjunction ps) ↔
      ∀ p, p ∈ ps → Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env p := by
  induction ps with
  | nil =>
    constructor
    · intro _ p hp
      exact False.elim (List.not_mem_nil hp)
    · intro _
      exact fun h => h
  | cons p ps ih =>
    simp only [conjunction,Formula.Realize,ih,List.mem_cons]
    constructor
    · rintro ⟨hp,hps⟩ q (he | hq)
      · exact he.symm ▸ hp
      · exact hps q hq
    · intro h
      exact ⟨h p (Or.inl rfl),fun q hq => h q (Or.inr hq)⟩

def sentence {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (Gamma : List (Formula n)) (phi : Formula n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem p P).imp
    ((conjunction ((List.finRange n).map (fun i => MinimalPredicates.pred H id (v i)))).imp
      ((conjunction (Gamma.map (formula R H id v P p))).imp (formula R H id v P p phi))))).close

theorem models {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (Gamma : List (Formula n)) (phi : Formula n)
    (d : Source.Derives (fun psi => psi ∈ Gamma) phi) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence R H v P p Gamma phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre hp hv hGamma
  have hv' := (conjunction_semantics (M := M) env _).mp hv
  have hg' := (conjunction_semantics (M := M) env _).mp hGamma
  apply (ForcingFormula.formula_semantics (M := M) env R H id v P p phi).mpr
  apply sound hM ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) d (fun i => env (v i)) (env p) hp
  · intro i
    exact (ForcingClassEvaluation.predicate_semantics (M := M) env H id (v i)).mp
      (hv' _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
  · intro psi hpsi
    exact (ForcingFormula.formula_semantics (M := M) env R H id v P p psi).mp
      (hg' _ (List.mem_map.mpr ⟨psi,hpsi,rfl⟩))

theorem kernel_certificate {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (Gamma : List (Formula n)) (phi : Formula n)
    (d : Source.Derives (fun psi => psi ∈ Gamma) phi) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H v P p Gamma phi)) :=
  ModelTransfer.derives (fun _ hM => models R H v P p Gamma phi d hM)

end PPAC.Migration.ForcingSound
