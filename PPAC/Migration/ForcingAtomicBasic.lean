/- Pinned AtomicForcing: monotonicity, symmetry, dense closure, edge introduction,
and reflexivity. The source Preorder is represented by reflexivity/transitivity
of the same formula R on the internal condition carrier P. The forcing relations
are the previously constructed ones, never fields of an assumed forcing package. -/
import PPAC.Migration.ForcingAtomicRelations

namespace PPAC.Migration.ForcingAtomicBasic
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces forces)
open ForcingMapConditions (MapRel)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preorder {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last m) P.castSucc).imp
    (ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) (Fin.last m)))).conj
    (.all (.all (.all ((Formula.mem (Fin.last m).castSucc.castSucc P.castSucc.castSucc.castSucc).imp
      ((Formula.mem (Fin.last (m+1)).castSucc P.castSucc.castSucc.castSucc).imp
        ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).imp
          ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
            (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
            ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
              (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
              (ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
                (Fin.last m).castSucc.castSucc (Fin.last (m+2)))))))))))

def PreorderOn {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P : M.Carrier .set) : Prop :=
  (∀ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p P → MapRel R params p p) ∧
  (∀ a b c, (Definitional.Project.FirstOrderSemantics.reduct M).mem a P →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem b P →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem c P →
    MapRel R params a b → MapRel R params b c → MapRel R params a c)

theorem preorder_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (preorder R rho P) ↔
      PreorderOn R (fun i => v (rho i)) (v P) := by
  simp only [preorder,PreorderOn,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem condition (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p : M.Carrier .set}
    {equality : Bool} (h : Forces equality R params P x y p) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P := by
  cases equality with
  | false => exact ((ForcingAtomicRelations.mem_iff hM R params P x y p).mp h).1
  | true => exact ((ForcingAtomicRelations.eq_iff hM R params P x y p).mp h).1

theorem mem_mono (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p q : M.Carrier .set}
    (hpre : PreorderOn R params P) (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R params q p) (h : Forces false R params P x y p) : Forces false R params P x y q := by
  obtain ⟨hp,hm⟩ := (ForcingAtomicRelations.mem_iff hM R params P x y p).mp h
  exact (ForcingAtomicRelations.mem_iff hM R params P x y q).mpr
    ⟨hq,fun r hr hrq => hm r hr (hpre.2 r q p hr hq hp hrq hqp)⟩

theorem eq_mono (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p q : M.Carrier .set}
    (hpre : PreorderOn R params P) (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R params q p) (h : Forces true R params P x y p) : Forces true R params P x y q := by
  obtain ⟨hp,h1,h2⟩ := (ForcingAtomicRelations.eq_iff hM R params P x y p).mp h
  exact (ForcingAtomicRelations.eq_iff hM R params P x y q).mpr ⟨hq,
    (fun nu r hr he s hs hsq hsr => h1 nu r hr he s hs (hpre.2 s q p hs hq hp hsq hqp) hsr),
    (fun nu r hr he s hs hsq hsr => h2 nu r hr he s hs (hpre.2 s q p hs hq hp hsq hqp) hsr)⟩

theorem eq_symm (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p : M.Carrier .set}
    (h : Forces true R params P x y p) : Forces true R params P y x p := by
  obtain ⟨hp,h1,h2⟩ := (ForcingAtomicRelations.eq_iff hM R params P x y p).mp h
  exact (ForcingAtomicRelations.eq_iff hM R params P y x p).mpr ⟨hp,h2,h1⟩

def dense {n m : Nat} (equality : Bool) (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y p : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (forces equality R (paramsUp (paramsUp rho)) P.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))))))))

def Dense {n : Nat} (equality : Bool) (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
    ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧ Forces equality R params P x y r

theorem dense_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (equality : Bool) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (dense equality R rho P x y p) ↔
      Dense equality R (fun i => v (rho i)) (v P) (v x) (v y) (v p) := by
  simp only [dense,Dense,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem mem_of_dense (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : Dense false R params P x y p) : Forces false R params P x y p := by
  apply (ForcingAtomicRelations.mem_iff hM R params P x y p).mpr
  refine ⟨hp,?_⟩
  intro q hq hqp
  obtain ⟨r,hr,hrq,hrm⟩ := h q hq hqp
  obtain ⟨s,nu,t,hs,hsr,ht,he,hst,heq⟩ :=
    ((ForcingAtomicRelations.mem_iff hM R params P x y r).mp hrm).2 r hr (hpre.1 r hr)
  exact ⟨s,nu,t,hs,hpre.2 s r q hs hr hq hsr hrq,ht,he,hst,heq⟩

theorem eq_of_dense (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : Dense true R params P x y p) : Forces true R params P x y p := by
  have step : ∀ a b, Dense true R params P a b p → ForcingAtomicRelations.EqHalf R params P a b p := by
    intro a b hab nu s hs he q hq hqp hqs
    apply mem_of_dense hM hpre hq
    intro t ht htq
    obtain ⟨r,hr,hrt,hrf⟩ := hab t ht (hpre.2 t q p ht hq hp htq hqp)
    exact ⟨r,hr,hrt,((ForcingAtomicRelations.eq_iff hM R params P a b r).mp hrf).2.1
      nu s hs he r hr (hpre.1 r hr)
        (hpre.2 r q s hr hq hs (hpre.2 r t q hr ht hq hrt htq) hqs)⟩
  apply (ForcingAtomicRelations.eq_iff hM R params P x y p).mpr
  refine ⟨hp,step x y h,step y x ?_⟩
  intro q hq hqp
  obtain ⟨r,hr,hrq,hrf⟩ := h q hq hqp
  exact ⟨r,hr,hrq,eq_symm hM hrf⟩

theorem mem_of_edge_eq (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y nu p r : M.Carrier .set}
    (hpre : PreorderOn R params P) (hr : (Definitional.Project.FirstOrderSemantics.reduct M).mem r P)
    (hpr : MapRel R params p r) (he : PureKuratowski.PairMember M nu r y)
    (h : Forces true R params P x nu p) : Forces false R params P x y p := by
  have hp := condition hM h
  apply (ForcingAtomicRelations.mem_iff hM R params P x y p).mpr
  refine ⟨hp,?_⟩
  intro q hq hqp
  exact ⟨q,nu,r,hq,hpre.1 q hq,hr,he,hpre.2 q p r hq hp hr hqp hpr,eq_mono hM hpre hq hqp h⟩

def reflexiveAt {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    (forces true R (paramsUp rho) P.castSucc x.castSucc x.castSucc (Fin.last m)))

theorem reflexiveAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (reflexiveAt R rho P x) ↔
      ∀ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p (v P) →
        Forces true R (fun i => v (rho i)) (v P) (v x) (v x) p := by
  simp only [reflexiveAt,Formula.Realize,ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem eq_refl (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (x p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) : Forces true R params P x x p := by
  let matrix := reflexiveAt R (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases P params
  have hm : ∀ y, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases y inputs) matrix ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → Forces true R params P y y q := by
    intro y
    simpa only [inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      reflexiveAt_semantics (M := M) (Fin.lastCases y inputs) R (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  have all := ForcingMapLaws.formula_induction hM matrix inputs (by
    intro y ih
    apply (hm y).mpr
    intro q hq
    have half : ForcingAtomicRelations.EqHalf R params P y y q := by
      intro nu r hr he s hs _ hsr
      exact mem_of_edge_eq hM hpre hr hsr he ((hm nu).mp (ih nu r he) s hs)
    exact (ForcingAtomicRelations.eq_iff hM R params P y y q).mpr ⟨hq,half,half⟩)
  exact (hm x).mp (all x) p hp

def monotoneBody {n m : Nat} (equality : Bool) (R : Formula (n+2)) (params : Fin n → Fin m)
    (P x y p q : Fin m) : Formula m :=
  (preorder R params P).imp ((Formula.mem q P).imp ((ReplacementPredicates.rel R params q p).imp
    ((forces equality R params P x y p).imp (forces equality R params P x y q))))

def monotoneSentence {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) : Source.Sentence :=
  (monotoneBody equality R id P x y p q).close

def denseSentence {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p : Fin n) : Source.Sentence :=
  ((preorder R id P).imp ((Formula.mem p P).imp ((dense equality R id P x y p).imp
    (forces equality R id P x y p)))).close

def symmetrySentence {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) : Source.Sentence :=
  ((forces true R id P x y p).imp (forces true R id P y x p)).close

def reflexivitySentence {n : Nat} (R : Formula (n+2)) (P x p : Fin n) : Source.Sentence :=
  ((preorder R id P).imp ((Formula.mem p P).imp (forces true R id P x x p))).close

def edgeSentence {n : Nat} (R : Formula (n+2)) (P x y nu p r : Fin n) : Source.Sentence :=
  ((preorder R id P).imp ((Formula.mem r P).imp ((ReplacementPredicates.rel R id p r).imp
    ((Source.SetLanguage.edge y nu r).imp ((forces true R id P x nu p).imp (forces false R id P x y p)))))).close

theorem monotone_body_models {n m : Nat} (equality : Bool) (R : Formula (n+2)) (params : Fin n → Fin m)
    (P x y p q : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (monotoneBody equality R params P x y p q).close).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hq hqp h
  have hp := (preorder_semantics (M := M) v R params P).mp hpre
  have hqp' := (ForcingMapConditions.rel_semantics (M := M) v R params q p).mp hqp
  have h' := (ForcingAtomicRelations.forces_semantics (M := M) v equality R params P x y p).mp h
  apply (ForcingAtomicRelations.forces_semantics (M := M) v equality R params P x y q).mpr
  cases equality with
  | false => exact mem_mono hM hp hq hqp' h'
  | true => exact eq_mono hM hp hq hqp' h'

theorem monotone_models {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (monotoneSentence equality R P x y p q)).TrueIn M :=
  monotone_body_models equality R id P x y p q hM

theorem dense_models {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (denseSentence equality R P x y p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hp hd
  have hpre' := (preorder_semantics (M := M) v R id P).mp hpre
  have hd' := (dense_semantics (M := M) v equality R id P x y p).mp hd
  apply (ForcingAtomicRelations.forces_semantics (M := M) v equality R id P x y p).mpr
  cases equality with
  | false => exact mem_of_dense hM hpre' hp hd'
  | true => exact eq_of_dense hM hpre' hp hd'

theorem symmetry_models {n : Nat} (R : Formula (n+2)) (P x y p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (symmetrySentence R P x y p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  exact (ForcingAtomicRelations.forces_semantics (M := M) v true R id P y x p).mpr
    (eq_symm hM ((ForcingAtomicRelations.forces_semantics (M := M) v true R id P x y p).mp h))

theorem reflexivity_models {n : Nat} (R : Formula (n+2)) (P x p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (reflexivitySentence R P x p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hp
  exact (ForcingAtomicRelations.forces_semantics (M := M) v true R id P x x p).mpr
    (eq_refl hM ((preorder_semantics (M := M) v R id P).mp hpre) (v x) (v p) hp)

theorem edge_models {n : Nat} (R : Formula (n+2)) (P x y nu p r : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (edgeSentence R P x y nu p r)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hr hpr he h
  exact (ForcingAtomicRelations.forces_semantics (M := M) v false R id P x y p).mpr
    (mem_of_edge_eq hM ((preorder_semantics (M := M) v R id P).mp hpre) hr
      ((ForcingMapConditions.rel_semantics (M := M) v R id p r).mp hpr)
      ((KuratowskiZF.source_edge v y nu r).mp he)
      ((ForcingAtomicRelations.forces_semantics (M := M) v true R id P x nu p).mp h))

theorem monotone_kernel_certificate {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (monotoneSentence equality R P x y p q)) :=
  ModelTransfer.derives (fun _ hM => monotone_models equality R P x y p q hM)

theorem dense_kernel_certificate {n : Nat} (equality : Bool) (R : Formula (n+2)) (P x y p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (denseSentence equality R P x y p)) :=
  ModelTransfer.derives (fun _ hM => dense_models equality R P x y p hM)

theorem symmetry_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (symmetrySentence R P x y p)) :=
  ModelTransfer.derives (fun _ hM => symmetry_models R P x y p hM)

theorem reflexivity_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (reflexivitySentence R P x p)) :=
  ModelTransfer.derives (fun _ hM => reflexivity_models R P x p hM)

theorem edge_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y nu p r : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (edgeSentence R P x y nu p r)) :=
  ModelTransfer.derives (fun _ hM => edge_models R P x y nu p r hM)

end PPAC.Migration.ForcingAtomicBasic
