/- Existence of the original atomic forcing recursion on all internal names.
Concrete step: ForcingAtomicStep. Existing Collection, Separation, Union,
Kuratowski pairs and the accepted pair induction discharge the construction.
No external well-foundedness or choice of a family of subgraphs is used. -/
import PPAC.Migration.ForcingAtomicGraphs
import YesMetaZFC.SetTheory.Collection

namespace PPAC.Migration.ForcingAtomicRecursion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicGraphs (Lookup Covered Good Value)
open ForcingAtomicStep (Equation)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem lookup_union {family U : M.Carrier .set}
    (hU : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem z part) (x y output : M.Carrier .set) :
    Lookup U x y output ↔ ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧ Lookup part x y output := by
  constructor
  · rintro ⟨key,hkey,he⟩
    obtain ⟨part,hpart,hvalue⟩ := (ForcingEvaluation.union_edge hU key output).mp he
    exact ⟨part,hpart,key,hkey,hvalue⟩
  · rintro ⟨part,hpart,key,hkey,he⟩
    exact ⟨key,hkey,(ForcingEvaluation.union_edge hU key output).mpr ⟨part,hpart,he⟩⟩

theorem union_good (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P family U : M.Carrier .set}
    (hf : ∀ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family → Good R params P part)
    (hU : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem z part) : Good R params P U := by
  intro x y output hout
  obtain ⟨part,hpart,hvalue⟩ := (lookup_union hU x y output).mp hout
  obtain ⟨hc,heq⟩ := hf part hpart x y output hvalue
  have agree : ∀ a b, (∃ v, Lookup part a b v) → ∀ v, Lookup part a b v ↔ Lookup U a b v := by
    intro a b hab v
    constructor
    · intro hv
      exact (lookup_union hU a b v).mpr ⟨part,hpart,hv⟩
    · intro hv
      obtain ⟨other,hother,ho⟩ := (lookup_union hU a b v).mp hv
      obtain ⟨w,hw⟩ := hab
      exact (ForcingAtomicGraphs.compatible hM (hf other hother) (hf part hpart) a b v w ho hw).symm ▸ hw
  have hl := fun nu r h => agree nu y (hc.1 nu r h)
  have hr := fun nu r h => agree x nu (hc.2.1 nu r h)
  have hs := fun nu r h => agree nu x (hc.2.2 nu r h)
  refine ⟨⟨?_,?_,?_⟩,(ForcingAtomicStep.equation_congr
    (fun nu r h => ForcingAtomicGraphs.row_congr (hl nu r h))
    (fun nu r h => ForcingAtomicGraphs.row_congr (hr nu r h))
    (fun nu r h => ForcingAtomicGraphs.row_congr (hs nu r h))).mp heq⟩
  · intro nu r h
    obtain ⟨v,hv⟩ := hc.1 nu r h
    exact ⟨v,(hl nu r h v).mp hv⟩
  · intro nu r h
    obtain ⟨v,hv⟩ := hc.2.1 nu r h
    exact ⟨v,(hr nu r h v).mp hv⟩
  · intro nu r h
    obtain ⟨v,hv⟩ := hc.2.2 nu r h
    exact ⟨v,(hs nu r h v).mp hv⟩

/-- Child is a set-sized predecessor family, by the existing coordinate bound. -/
theorem children_set (hM : FirstOrder.Theory.Models M nativeZF) (parent : M.Carrier .set) :
    ∃ children, ∀ nu, (Definitional.Project.FirstOrderSemantics.reduct M).mem nu children ↔
      ∃ r, PureKuratowski.PairMember M nu r parent := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  obtain ⟨bound,hbound⟩ := ForcingMapConditions.coordinate_bound hM parent
  let q := ForcingNameInduction.child (1 : Fin 2) 0
  let inputs : Fin 1 → M.Carrier .set := fun _ => parent
  have sep := (GodelDefOutput.separation_semantics E q).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation q).semantically_entails M hM))
  obtain ⟨children,hc⟩ := sep inputs bound
  have hq : ∀ nu, Formula.Realize E (Fin.lastCases nu inputs) q ↔ ∃ r, PureKuratowski.PairMember M nu r parent := by
    intro nu
    exact ForcingNameInduction.child_semantics (M := M) (Fin.lastCases nu inputs) 1 0
  refine ⟨children,fun nu => ?_⟩
  constructor
  · intro hn
    exact (hq nu).mp ((hc nu).mp hn).2
  · rintro ⟨r,hr⟩
    exact (hc nu).mpr ⟨(hbound nu r hr).1,(hq nu).mpr ⟨r,hr⟩⟩

def witness {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y g : Fin m) : Formula m :=
  (ForcingAtomicGraphs.good R rho P g).conj
    (.ex (ForcingAtomicGraphs.lookup g.castSucc x.castSucc y.castSucc (Fin.last m)))

theorem witness_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (witness R rho P x y g) ↔
      Good R (fun i => v (rho i)) (v P) (v g) ∧ ∃ output, Lookup (v g) (v x) (v y) output := by
  simp only [witness, Formula.Realize, ForcingAtomicGraphs.good_semantics (M := M),
    ForcingAtomicGraphs.lookup_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Collection gathers witnesses; Separation removes its possible junk elements. -/
theorem collect_branch (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P parent other : M.Carrier .set) (swap : Bool)
    (ih : ∀ nu r, PureKuratowski.PairMember M nu r parent →
      ∃ output, Value R params P (if swap then nu else other) (if swap then other else nu) output) :
    ∃ family, (∀ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family → Good R params P part) ∧
      ∀ nu r, PureKuratowski.PairMember M nu r parent →
        ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
          ∃ output, Lookup part (if swap then nu else other) (if swap then other else nu) output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  obtain ⟨children,hchildren⟩ := children_set hM parent
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases other (Fin.lastCases P params)
  let rho : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let pp := (Fin.last n).castSucc.castSucc.castSucc
  let oo := (Fin.last (n+1)).castSucc.castSucc
  let nu := (Fin.last (n+2)).castSucc
  let gg := Fin.last (n+3)
  let matrix := witness R rho pp (if swap then nu else oo) (if swap then oo else nu) gg
  have hm : ∀ z part, Formula.Realize E (Fin.lastCases part (Fin.lastCases z inputs)) matrix ↔
      Good R params P part ∧ ∃ output, Lookup part (if swap then z else other) (if swap then other else z) output := by
    intro z part
    have h := witness_semantics (M := M) (Fin.lastCases part (Fin.lastCases z inputs)) R rho pp
      (if swap then nu else oo) (if swap then oo else nu) gg
    cases swap <;> simpa only [matrix,inputs,rho,pp,oo,nu,gg,E,if_true,if_false,Bool.false_eq_true,
      Fin.lastCases_last,Fin.lastCases_castSucc] using h
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) (n+2) :=
    { bound := fun i => inputs i.rev, free := fun _ => parent }
  have hRel := ForcingMapConditions.binary_semantics hM matrix inputs parent
  obtain ⟨family,hfamily⟩ := SetTheory.ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary matrix) env children (by
      intro z hz
      obtain ⟨r,hr⟩ := (hchildren z).mp hz
      obtain ⟨output,part,hpart,hout⟩ := ih z r hr
      exact ⟨part,(hRel z part).mpr ((hm z part).mpr ⟨hpart,output,hout⟩)⟩)
  let query := ForcingAtomicGraphs.good R (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+2))
  have hq : ∀ part, Formula.Realize E (Fin.lastCases part inputs) query ↔ Good R params P part := by
    intro part
    simpa only [query,E,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      ForcingAtomicGraphs.good_semantics (M := M) (Fin.lastCases part inputs) R
        (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc (Fin.last (n+2))
  have sep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨filtered,hfiltered⟩ := sep inputs family
  refine ⟨filtered,(fun part h => (hq part).mp ((hfiltered part).mp h).2),?_⟩
  intro z r hr
  obtain ⟨part,hpart,hw⟩ := hfamily z ((hchildren z).mpr ⟨r,hr⟩)
  obtain ⟨hg,hout⟩ := (hm z part).mp ((hRel z part).mp hw)
  exact ⟨part,(hfiltered part).mpr ⟨hpart,(hq part).mpr hg⟩,hout⟩

theorem collect_children (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y : M.Carrier .set)
    (il : ∀ nu r, PureKuratowski.PairMember M nu r x → ∃ output, Value R params P nu y output)
    (ir : ∀ nu r, PureKuratowski.PairMember M nu r y → ∃ output, Value R params P x nu output)
    (isw : ∀ nu r, PureKuratowski.PairMember M nu r y → ∃ output, Value R params P nu x output) :
    ∃ g, Good R params P g ∧ Covered g x y := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨fl,hfl,cl⟩ := collect_branch hM R params P x y true il
  obtain ⟨fr,hfr,cr⟩ := collect_branch hM R params P y x false ir
  obtain ⟨fs,hfs,cs⟩ := collect_branch hM R params P y x true isw
  obtain ⟨pair,hpair⟩ := SetTheory.KP.exists_pair hKP fl fr
  obtain ⟨triple,htriple⟩ := SetTheory.KP.exists_insert hKP pair fs
  obtain ⟨family,hfamily⟩ := SetTheory.KP.exists_union hKP triple
  have hf : ∀ part, E part family ↔ E part fl ∨ E part fr ∨ E part fs := by
    intro part
    constructor
    · intro hp
      obtain ⟨f,hf,hp⟩ := (hfamily part).mp hp
      rcases (htriple f).mp hf with hf | hf
      · rcases (hpair f).mp hf with h | h
        · exact Or.inl (h ▸ hp)
        · exact Or.inr (Or.inl (h ▸ hp))
      · exact Or.inr (Or.inr (hf ▸ hp))
    · intro hp
      rcases hp with hp | hp | hp
      · exact (hfamily part).mpr ⟨fl,(htriple fl).mpr (Or.inl ((hpair fl).mpr (Or.inl rfl))),hp⟩
      · exact (hfamily part).mpr ⟨fr,(htriple fr).mpr (Or.inl ((hpair fr).mpr (Or.inr rfl))),hp⟩
      · exact (hfamily part).mpr ⟨fs,(htriple fs).mpr (Or.inr rfl),hp⟩
  obtain ⟨g,hg⟩ := SetTheory.KP.exists_union hKP family
  refine ⟨g,union_good hM (fun part hp => ?_) hg,?_,?_,?_⟩
  · rcases (hf part).mp hp with h | h | h
    · exact hfl part h
    · exact hfr part h
    · exact hfs part h
  · intro nu r h
    obtain ⟨part,hpart,output,hout⟩ := cl nu r h
    exact ⟨output,(lookup_union hg nu y output).mpr ⟨part,(hf part).mpr (Or.inl hpart),hout⟩⟩
  · intro nu r h
    obtain ⟨part,hpart,output,hout⟩ := cr nu r h
    exact ⟨output,(lookup_union hg x nu output).mpr ⟨part,(hf part).mpr (Or.inr (Or.inl hpart)),hout⟩⟩
  · intro nu r h
    obtain ⟨part,hpart,output,hout⟩ := cs nu r h
    exact ⟨output,(lookup_union hg nu x output).mpr ⟨part,(hf part).mpr (Or.inr (Or.inr hpart)),hout⟩⟩

theorem lookup_insert {g extended key x y output : M.Carrier .set} (hkey : PureKuratowski.Code M key x y)
    (he : ∀ a b, PureKuratowski.PairMember M a b extended ↔
      PureKuratowski.PairMember M a b g ∨ (a = key ∧ b = output)) (a b v : M.Carrier .set) :
    Lookup extended a b v ↔ Lookup g a b v ∨ (a = x ∧ b = y ∧ v = output) := by
  constructor
  · rintro ⟨k,hk,hv⟩
    rcases (he k v).mp hv with hv | ⟨h1,h2⟩
    · exact Or.inl ⟨k,hk,hv⟩
    · subst k
      obtain ⟨h3,h4⟩ := PureKuratowski.code_injective hk hkey
      exact Or.inr ⟨h3,h4,h2⟩
  · intro hv
    rcases hv with ⟨k,hk,hv⟩ | ⟨h1,h2,h3⟩
    · exact ⟨k,hk,(he k v).mpr (Or.inl hv)⟩
    · subst a
      subst b
      subst v
      exact ⟨key,hkey,(he key output).mpr (Or.inr ⟨rfl,rfl⟩)⟩

theorem extend_good (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g extended x y output : M.Carrier .set}
    (hg : Good R params P g) (hc : Covered g x y) (hs : Equation R params P g x y output)
    (he : ∀ a b v, Lookup extended a b v ↔ Lookup g a b v ∨ (a = x ∧ b = y ∧ v = output)) :
    Good R params P extended := by
  have agree : ∀ v, Lookup g x y v → v = output := fun v hv =>
    ForcingAtomicStep.equation_unique hM (hg x y v hv).2 hs
  have transferLookup : ∀ a b, (∃ v, Lookup g a b v) → ∀ v, Lookup g a b v ↔ Lookup extended a b v := by
    intro a b hab v
    constructor
    · intro hv
      exact (he a b v).mpr (Or.inl hv)
    · intro hv
      rcases (he a b v).mp hv with hv | ⟨h1,h2,h3⟩
      · exact hv
      · subst a
        subst b
        subst v
        obtain ⟨w,hw⟩ := hab
        exact agree w hw ▸ hw
  have transfer : ∀ a b v, Covered g a b → Equation R params P g a b v →
      Covered extended a b ∧ Equation R params P extended a b v := by
    intro a b v hcover hstep
    have hl := fun nu r h => transferLookup nu b (hcover.1 nu r h)
    have hr := fun nu r h => transferLookup a nu (hcover.2.1 nu r h)
    have hs' := fun nu r h => transferLookup nu a (hcover.2.2 nu r h)
    refine ⟨⟨?_,?_,?_⟩,(ForcingAtomicStep.equation_congr
      (fun nu r h => ForcingAtomicGraphs.row_congr (hl nu r h))
      (fun nu r h => ForcingAtomicGraphs.row_congr (hr nu r h))
      (fun nu r h => ForcingAtomicGraphs.row_congr (hs' nu r h))).mp hstep⟩
    · intro nu r h
      obtain ⟨w,hw⟩ := hcover.1 nu r h
      exact ⟨w,(hl nu r h w).mp hw⟩
    · intro nu r h
      obtain ⟨w,hw⟩ := hcover.2.1 nu r h
      exact ⟨w,(hr nu r h w).mp hw⟩
    · intro nu r h
      obtain ⟨w,hw⟩ := hcover.2.2 nu r h
      exact ⟨w,(hs' nu r h w).mp hw⟩
  intro a b v hv
  rcases (he a b v).mp hv with hv | ⟨h1,h2,h3⟩
  · exact transfer a b v (hg a b v hv).1 (hg a b v hv).2
  · subst a
    subst b
    subst v
    exact transfer x y output hc hs

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y : M.Carrier .set) :
    ∃ output, Value R params P x y output := by
  let p : Formula (n+3) := .ex (ForcingAtomicGraphs.value R (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3)))
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases P params
  have hp : ∀ a b, ForcingMapConditions.MapRel p inputs a b ↔ ∃ output, Value R params P a b output := by
    intro a b
    simp only [p,inputs,ForcingMapConditions.MapRel,Formula.Realize,ForcingAtomicGraphs.value_semantics (M := M),
      Fin.lastCases_last,Fin.lastCases_castSucc]
    rfl
  have all := ForcingPairInduction.formula_induction hM p inputs (by
    intro a b il ir isw
    apply (hp a b).mpr
    obtain ⟨g,hg,hc⟩ := collect_children hM R params P a b
      (fun nu r h => (hp nu b).mp (il nu r h))
      (fun nu r h => (hp a nu).mp (ir nu r h))
      (fun nu r h => (hp nu a).mp (isw nu r h))
    obtain ⟨output,hs⟩ := ForcingAtomicStep.equation_exists hM R params P g a b
    obtain ⟨key,hkey⟩ := KuratowskiZF.exists_code hM a b
    obtain ⟨edge,hedge⟩ := KuratowskiZF.exists_code hM key output
    obtain ⟨extended,hext⟩ := SetTheory.KP.exists_insert
      (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) g edge
    have he := lookup_insert hkey (ForcingEvaluation.insert_edge hedge hext)
    exact ⟨output,extended,extend_good hM hg hc hs he,(he a b output).mpr (Or.inr ⟨rfl,rfl,rfl⟩)⟩)
  exact (hp x y).mp (all x y)

def existenceSentence {n : Nat} (R : Formula (n+2)) (P x y : Fin n) : Source.Sentence :=
  (Formula.ex (ForcingAtomicGraphs.value R Fin.castSucc P.castSucc x.castSucc y.castSucc (Fin.last n))).close

theorem existence_models {n : Nat} (R : Formula (n+2)) (P x y : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence R P x y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output,ho⟩ := exists_value hM R v (v P) (v x) (v y)
  refine ⟨output,?_⟩
  have h := ForcingAtomicGraphs.value_semantics (M := M) (Fin.lastCases output v) R Fin.castSucc
    P.castSucc x.castSucc y.castSucc (Fin.last n)
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at h
  exact h.mpr ho

theorem existence_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence R P x y)) :=
  ModelTransfer.derives (fun _ hM => existence_models R P x y hM)

end PPAC.Migration.ForcingAtomicRecursion
