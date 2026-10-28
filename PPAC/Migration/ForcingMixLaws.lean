/- Pinned EquivariantMixing.mem_equivariantMix / eq_equivariantMix_at.
Consumer: Models.LocalQuotients.support_descent. The family and activations
are internal graphs; all conditions and raw names are quantified internally.
The existing atomic recursion and regularity laws supply the source proof. -/
import PPAC.Migration.ForcingMixName

namespace PPAC.Migration.ForcingMixLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingMixName (Mix)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Activations (P J a : M.Carrier .set) : Prop :=
  ∀ i t, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i t a → (Definitional.Project.FirstOrderSemantics.reduct M).mem t P

def activations {m : Nat} (P J a : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc J.castSucc.castSucc).imp
    ((Source.SetLanguage.edge a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.mem (Fin.last (m+1)) P.castSucc.castSucc))))

theorem activations_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P J a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (activations P J a) ↔
      Activations (v P) (v J) (v a) := by
  simp only [activations,Activations,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def ActiveMember {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a nu p : M.Carrier .set) : Prop :=
  ∃ i sigma t, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J ∧
    PureKuratowski.PairMember M i sigma f ∧ PureKuratowski.PairMember M i t a ∧
    MapRel R env p t ∧ Forces false R env P nu sigma p

def activeMember {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m)
    (P J f a nu p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun j => j.castSucc.castSucc.castSucc
  let rr := fun j => up (rho j)
  let i := (Fin.last m).castSucc.castSucc
  let sigma := (Fin.last (m+1)).castSucc
  let t := Fin.last (m+2)
  .ex (.ex (.ex ((Formula.mem i (up J)).conj
    ((Source.SetLanguage.edge (up f) i sigma).conj
      ((Source.SetLanguage.edge (up a) i t).conj
        ((rel R rr (up p) t).conj (forces false R rr (up P) (up nu) sigma (up p))))))))

theorem activeMember_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a nu p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (activeMember R rho P J f a nu p) ↔
        ActiveMember R (fun j => v (rho j)) (v P) (v J) (v f) (v a) (v nu) (v p) := by
  simp only [activeMember,ActiveMember,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Regular {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a nu p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ActiveMember R env P J f a nu r

def regular {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m)
    (P J f a nu p : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((rel R (paramsUp rho) (Fin.last m) p.castSucc).imp (.ex
      ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (activeMember R (paramsUp (paramsUp rho)) P.castSucc.castSucc J.castSucc.castSucc
            f.castSucc.castSucc a.castSucc.castSucc nu.castSucc.castSucc (Fin.last (m+1))))))))

theorem regular_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a nu p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (regular R rho P J f a nu p) ↔
        Regular R (fun j => v (rho j)) (v P) (v J) (v f) (v a) (v nu) (v p) := by
  simp only [regular,Regular,Formula.Realize,activeMember_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem mem_mix (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P J f a name nu p : M.Carrier .set}
    (hpre : PreorderOn R env P) (ha : Activations P J a) (hn : Mix R env P J f a name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔ Regular R env P J f a nu p := by
  constructor
  · intro hm q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env P nu name p).mp hm).2 q hq hqp
    obtain ⟨_,i,sigma,t,d,hi,hf,hat,_,hct,hmem⟩ := (ForcingMixName.edge_mix hM hn child c).mp he
    exact ⟨r,hr,hrq,i,sigma,t,hi,hf,hat,hpre.2 r c t hr hc (ha i t hi hat) hrc hct,
      (ForcingAtomicLaws.mem_congr_left hM hpre heq).mpr
        (ForcingAtomicBasic.mem_mono hM hpre hr hrc hmem)⟩
  · intro h
    apply (ForcingAtomicRelations.mem_iff hM R env P nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,sigma,t,hi,hf,hat,hrt,hm⟩ := h q hq hqp
    obtain ⟨s,child,c,hs,hsr,hc,he,hsc,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env P nu sigma r).mp hm).2 r hr (hpre.1 r hr)
    have he' := (ForcingMixName.edge_mix hM hn child s).mpr
      ⟨hs,i,sigma,t,c,hi,hf,hat,he,hpre.2 s r t hs hr (ha i t hi hat) hsr hrt,
        ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hsc he (ForcingAtomicBasic.eq_refl hM hpre child s hs)⟩
    exact ⟨s,child,s,hs,hpre.2 s r q hs hr hq hsr hrq,hs,he',hpre.1 s hs,heq⟩

def Coherent {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a : M.Carrier .set) : Prop :=
  ∀ i j sigma tau s t p, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem j J →
    PureKuratowski.PairMember M i sigma f → PureKuratowski.PairMember M j tau f →
    PureKuratowski.PairMember M i s a → PureKuratowski.PairMember M j t a →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P →
    MapRel R env p s → MapRel R env p t → Forces true R env P sigma tau p

def coherent {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+7) := fun x => x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr := fun x => up (rho x)
  let i := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let j := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc
  let sigma := (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc
  let tau := (Fin.last (m+3)).castSucc.castSucc.castSucc
  let s := (Fin.last (m+4)).castSucc.castSucc
  let t := (Fin.last (m+5)).castSucc
  let p := Fin.last (m+6)
  let body := (Formula.mem i (up J)).imp ((Formula.mem j (up J)).imp
    ((Source.SetLanguage.edge (up f) i sigma).imp ((Source.SetLanguage.edge (up f) j tau).imp
      ((Source.SetLanguage.edge (up a) i s).imp ((Source.SetLanguage.edge (up a) j t).imp
        ((Formula.mem p (up P)).imp ((rel R rr p s).imp ((rel R rr p t).imp
          (forces true R rr (up P) sigma tau p)))))))))
  .all (.all (.all (.all (.all (.all (.all body))))))

theorem coherent_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (coherent R rho P J f a) ↔
      Coherent R (fun j => v (rho j)) (v P) (v J) (v f) (v a) := by
  simp only [coherent,Coherent,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem eq_at (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P J f a name i sigma t : M.Carrier .set}
    (hpre : PreorderOn R env P) (ha : Activations P J a) (hn : Mix R env P J f a name)
    (hcoh : Coherent R env P J f a) (hi : (Definitional.Project.FirstOrderSemantics.reduct M).mem i J)
    (hf : PureKuratowski.PairMember M i sigma f) (hat : PureKuratowski.PairMember M i t a) :
    Forces true R env P name sigma t := by
  have ht := ha i t hi hat
  have same nu q (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P)
      (hqt : MapRel R env q t) : Forces false R env P nu name q ↔ Forces false R env P nu sigma q := by
    constructor
    · intro hm
      apply ForcingAtomicBasic.mem_of_dense hM hpre hq
      intro r hr hrq
      obtain ⟨s,hs,hsr,j,tau,b,hj,hfj,haj,hsb,hmem⟩ := (mem_mix hM hpre ha hn hq).mp hm r hr hrq
      exact ⟨s,hs,hsr,(ForcingAtomicLaws.mem_congr_right hM hpre
        (hcoh j i tau sigma b t s hj hi hfj hf haj hat hs hsb
          (hpre.2 s q t hs hq ht (hpre.2 s r q hs hr hq hsr hrq) hqt))).mp hmem⟩
    · intro hm
      apply (mem_mix hM hpre ha hn hq).mpr
      intro r hr hrq
      exact ⟨r,hr,hpre.1 r hr,i,sigma,t,hi,hf,hat,hpre.2 r q t hr hq ht hrq hqt,
        ForcingAtomicBasic.mem_mono hM hpre hr hrq hm⟩
  apply (ForcingAtomicRelations.eq_iff hM R env P name sigma t).mpr
  refine ⟨ht,?_,?_⟩
  · intro nu c hc he q hq hqt hqc
    exact (same nu q hq hqt).mp
      (ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hqc he (ForcingAtomicBasic.eq_refl hM hpre nu q hq))
  · intro nu c hc he q hq hqt hqc
    exact (same nu q hq hqt).mpr
      (ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hqc he (ForcingAtomicBasic.eq_refl hM hpre nu q hq))

def membershipSentence {n : Nat} (R : Formula (n+2)) (P J f a name nu p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((activations P J a).imp
    ((ForcingMixName.mix R id P J f a name).imp ((Formula.mem p P).imp
      ((forces false R id P nu name p).iff (regular R id P J f a nu p)))))).close

def equalitySentence {n : Nat} (R : Formula (n+2)) (P J f a name i sigma t : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((activations P J a).imp
    ((ForcingMixName.mix R id P J f a name).imp ((coherent R id P J f a).imp
      ((Formula.mem i J).imp ((Source.SetLanguage.edge f i sigma).imp
        ((Source.SetLanguage.edge a i t).imp (forces true R id P name sigma t)))))))).close

theorem membership_models {n : Nat} (R : Formula (n+2)) (P J f a name nu p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (membershipSentence R P J f a name nu p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp ha hn hcond
  have h := mem_mix hM ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hp)
    ((activations_semantics (M := M) env P J a).mp ha)
    ((ForcingMixName.mix_semantics (M := M) env R id P J f a name).mp hn) (nu := env nu) hcond
  have h' := (ForcingAtomicRelations.forces_semantics (M := M) env false R id P nu name p).trans
    (h.trans (regular_semantics (M := M) env R id P J f a nu p).symm)
  exact ⟨h'.mp,h'.mpr⟩

theorem equality_models {n : Nat} (R : Formula (n+2)) (P J f a name i sigma t : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (equalitySentence R P J f a name i sigma t)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp ha hn hc hi hf hat
  apply (ForcingAtomicRelations.forces_semantics (M := M) env true R id P name sigma t).mpr
  exact eq_at hM ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hp)
    ((activations_semantics (M := M) env P J a).mp ha)
    ((ForcingMixName.mix_semantics (M := M) env R id P J f a name).mp hn)
    ((coherent_semantics (M := M) env R id P J f a).mp hc) hi
    ((KuratowskiZF.source_edge env f i sigma).mp hf) ((KuratowskiZF.source_edge env a i t).mp hat)

theorem membership_kernel_certificate {n : Nat} (R : Formula (n+2)) (P J f a name nu p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (membershipSentence R P J f a name nu p)) :=
  ModelTransfer.derives (fun _ hM => membership_models R P J f a name nu p hM)

theorem equality_kernel_certificate {n : Nat} (R : Formula (n+2)) (P J f a name i sigma t : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (equalitySentence R P J f a name i sigma t)) :=
  ModelTransfer.derives (fun _ hM => equality_models R P J f a name i sigma t hM)

end PPAC.Migration.ForcingMixLaws

