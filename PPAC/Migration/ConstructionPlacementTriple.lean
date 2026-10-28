/- Pinned DiagramPlacements.three_copy_placement:329, consumed by
descent_comparison_placement:511. Follow the SAME fresh shared-copy proof,
using actual internal images and the already migrated two-placement extension. -/
import PPAC.Migration.ConstructionPlacementPasting

namespace PPAC.Migration.ConstructionPlacementTriple
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
open ForcingConditionGraphs (Permutation)
open ForcingLabelPermutations (Fixes)
open ConstructionPlacementPasting (Union Intersection ImageIntersection AgreesOn)
open ConstructionPlacementExtensions (Avoids)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ImageAt (p S z : M.Carrier .set) : Prop :=
  ∃ x, (Project.FirstOrderSemantics.reduct M).mem x S ∧ PureKuratowski.PairMember M x z p

def ImageInside (p S K : M.Carrier .set) : Prop :=
  ∀ z, ImageAt p S z → (Project.FirstOrderSemantics.reduct M).mem z K

def Overlap (p v K a A : M.Carrier .set) : Prop :=
  ∀ z, ImageAt p v z ∧ (Project.FirstOrderSemantics.reduct M).mem z K ↔ ImageAt a A z

def ExactImages (p q v B : M.Carrier .set) : Prop :=
  ∀ z, ImageAt p v z ∧ ImageAt q v z ↔ ImageAt p B z

def Inputs (I A B root v K a b : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).MemberSubset A v ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset B v ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset v I ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset K I ∧
    Intersection A B root ∧ Permutation I a ∧ Permutation I b ∧
    Fixes root a ∧ Fixes root b ∧ ImageIntersection a A b A root ∧
    ImageInside a A K ∧ ImageInside b A K

def Result (I A B v K a b p q : M.Carrier .set) : Prop :=
  Permutation I p ∧ Permutation I q ∧ AgreesOn A p a ∧ AgreesOn A q b ∧
    AgreesOn B p q ∧ Overlap p v K a A ∧ Overlap q v K b A ∧ ExactImages p q v B

theorem image_mono {p A v : M.Carrier .set}
    (h : (Project.FirstOrderSemantics.reduct M).MemberSubset A v) :
    ∀ z, ImageAt p A z → ImageAt p v z := by
  rintro z ⟨x,hx,hxz⟩
  exact ⟨x,h x hx,hxz⟩

theorem image_congr {I S p a : M.Carrier .set}
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset S I)
    (hp : Permutation I p) (ha : Permutation I a) (h : AgreesOn S p a) :
    ∀ z, ImageAt p S z ↔ ImageAt a S z := by
  intro z
  constructor
  · rintro ⟨x,hx,hxz⟩
    obtain ⟨y,hxy,_⟩ := ha.1.1.2 x (hSub x hx)
    have he := ForcingConditionGraphs.function_unique hp.1.1 hxz (h x y hx hxy)
    exact ⟨x,hx,by simpa only [he] using hxy⟩
  · rintro ⟨x,hx,hxz⟩
    exact ⟨x,hx,h x z hx hxz⟩

/-- Source image_inter_of_fresh, with the actual whole domain union. -/
theorem image_inter_of_fresh {A B v K U p : M.Carrier .set}
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A v)
    (hB : (Project.FirstOrderSemantics.reduct M).MemberSubset B v)
    (hU : Union U A B) (hAvoid : Avoids K p v U) :
    ∀ z, ImageAt p v z ∧ (Project.FirstOrderSemantics.reduct M).mem z K ↔
      (ImageAt p A z ∨ ImageAt p B z) ∧ (Project.FirstOrderSemantics.reduct M).mem z K := by
  intro z
  constructor
  · rintro ⟨⟨x,hx,hxz⟩,hz⟩
    by_cases hu : (Project.FirstOrderSemantics.reduct M).mem x U
    · exact ⟨((hU x).mp hu).elim (fun h => Or.inl ⟨x,h,hxz⟩) (fun h => Or.inr ⟨x,h,hxz⟩),hz⟩
    · exact False.elim (hAvoid x z hx hu hxz hz)
  · rintro ⟨h,hz⟩
    exact ⟨h.elim (image_mono hA z) (image_mono hB z),hz⟩

theorem move_root_off (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I root B K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu)
    (hRoot : (Project.FirstOrderSemantics.reduct M).MemberSubset root I)
    (hB : (Project.FirstOrderSemantics.reduct M).MemberSubset B I)
    (hK : (Project.FirstOrderSemantics.reduct M).MemberSubset K I)
    (hRootSmall : Small root mu) (hBSmall : Small B mu) (hKSmall : Small K mu) :
    ∃ g, Permutation I g ∧ Fixes root g ∧ Avoids K g B root := by
  obtain ⟨e,he,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM root
  have hNative := (ForcingConditionGraphs.native_permutation hM root e).mp he
  have hInjection : ForcingSupportSize.Injection root I e := by
    apply (ForcingSupportSize.native_injection hM root I e).mpr
    refine ⟨⟨hNative.1.1.1,hNative.1.1.2.1,?_⟩,hNative.1.2⟩
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hNative.1.1.2.2 x hx
    exact ⟨y,hRoot y hy,hxy⟩
  obtain ⟨g,hg,hExt,hAvoid⟩ := ConstructionPlacementExtensions.extend_permutation_off hM hChoice
    hw hMu hLarge hRoot hB hK hRootSmall hBSmall hKSmall
    ((ForcingSupportSize.native_injection hM root I e).mp hInjection)
  exact ⟨g,hg,fun x hx => hExt x x ((hIdentity x x).mpr ⟨hx,rfl⟩),hAvoid⟩

theorem fixed_root_image_inter {I root B K g : M.Carrier .set}
    (hg : Permutation I g) (hFix : Fixes root g)
    (hRootB : (Project.FirstOrderSemantics.reduct M).MemberSubset root B)
    (hRootK : (Project.FirstOrderSemantics.reduct M).MemberSubset root K)
    (hAvoid : Avoids K g B root) :
    ∀ z, ImageAt g B z ∧ (Project.FirstOrderSemantics.reduct M).mem z K ↔
      (Project.FirstOrderSemantics.reduct M).mem z root := by
  intro z
  constructor
  · rintro ⟨⟨x,hx,hxz⟩,hz⟩
    by_cases hr : (Project.FirstOrderSemantics.reduct M).mem x root
    · have he := ForcingConditionGraphs.function_unique hg.1.1 hxz (hFix x hr)
      exact he.symm ▸ hr
    · exact False.elim (hAvoid x z hx hr hxz hz)
  · intro hz
    exact ⟨⟨z,hRootB z hz,hFix z hz⟩,hRootK z hz⟩

theorem overlap_of_two {I A B root v K U a g p : M.Carrier .set}
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A v)
    (hB : (Project.FirstOrderSemantics.reduct M).MemberSubset B v)
    (hV : (Project.FirstOrderSemantics.reduct M).MemberSubset v I)
    (hRootA : (Project.FirstOrderSemantics.reduct M).MemberSubset root A)
    (hp : Permutation I p) (ha : Permutation I a) (hg : Permutation I g)
    (hFixA : Fixes root a) (hpa : AgreesOn A p a) (hpg : AgreesOn B p g)
    (hAK : ImageInside a A K)
    (hGamma : ∀ z, ImageAt g B z ∧ (Project.FirstOrderSemantics.reduct M).mem z K ↔
      (Project.FirstOrderSemantics.reduct M).mem z root)
    (hU : Union U A B) (hAvoid : Avoids K p v U) : Overlap p v K a A := by
  intro z
  have hImageA := image_congr (fun x hx => hV x (hA x hx)) hp ha hpa z
  have hImageB := image_congr (fun x hx => hV x (hB x hx)) hp hg hpg z
  constructor
  · intro h
    obtain ⟨h,hz⟩ := (image_inter_of_fresh hA hB hU hAvoid z).mp h
    rcases h with h | h
    · exact hImageA.mp h
    · have hr := (hGamma z).mp ⟨hImageB.mp h,hz⟩
      exact ⟨z,hRootA z hr,hFixA z hr⟩
  · intro h
    exact ⟨image_mono hA z (hImageA.mpr h),hAK z h⟩

theorem three_copy_placement (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I A B root v K a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (h : Inputs I A B root v K a b)
    (hv : Small v mu) (hK : Small K mu) : ∃ p q, Result I A B v K a b p q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨hA,hB,hV,hKI,hInter,ha,hb,hFixA,hFixB,hInd,hAK,hBK⟩ := h
  have hAI : (Project.FirstOrderSemantics.reduct M).MemberSubset A I := fun x hx => hV x (hA x hx)
  have hBI : (Project.FirstOrderSemantics.reduct M).MemberSubset B I := fun x hx => hV x (hB x hx)
  have hRootA : (Project.FirstOrderSemantics.reduct M).MemberSubset root A := fun x hx => ((hInter x).mp hx).1
  have hRootB : (Project.FirstOrderSemantics.reduct M).MemberSubset root B := fun x hx => ((hInter x).mp hx).2
  have hRootI : (Project.FirstOrderSemantics.reduct M).MemberSubset root I := fun x hx => hAI x (hRootA x hx)
  have hRootK : (Project.FirstOrderSemantics.reduct M).MemberSubset root K :=
    fun x hx => hAK x ⟨x,hRootA x hx,hFixA x hx⟩
  have hASmall := ForcingSupportSize.small_subset hM hA hv
  have hBSmall := ForcingSupportSize.small_subset hM hB hv
  have hRootSmall := ForcingSupportSize.small_subset hM hRootA hASmall
  obtain ⟨g,hg,hFixG,hAvoidG⟩ := move_root_off hM hChoice hw hMu hLarge hRootI hBI hKI hRootSmall hBSmall hK
  have hGamma := fixed_root_image_inter hg hFixG hRootB hRootK hAvoidG
  have hAG : ImageIntersection a A g B root := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z,hRootA z hz,hFixA z hz⟩,((hGamma z).mpr hz).1⟩
    · rintro ⟨hzA,hzG⟩
      exact (hGamma z).mp ⟨hzG,hAK z hzA⟩
  have hBG : ImageIntersection b A g B root := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z,hRootA z hz,hFixB z hz⟩,((hGamma z).mpr hz).1⟩
    · rintro ⟨hzB,hzG⟩
      exact (hGamma z).mp ⟨hzG,hBK z hzB⟩
  obtain ⟨U,p,hU,hp,hpa,hpg,hAvoidP⟩ := ConstructionPlacementPasting.extend_two_placements
    hM hChoice hw hMu hLarge ⟨hAI,hBI,hInter,ha,hg,hFixA,hFixG,hAG⟩ hV hKI hASmall hBSmall hv hK
  have hOverlapP := overlap_of_two hA hB hV hRootA hp ha hg hFixA hpa hpg hAK hGamma hU hAvoidP
  obtain ⟨P,hP,hPI⟩ := ForcingLabelConjugacy.exists_image hM (J := v) hp.1
  have hPSmall := ForcingSupportSize.small_image hM hp hP hv
  obtain ⟨K2,hK2⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) K P
  have hK2Sub : (Project.FirstOrderSemantics.reduct M).MemberSubset K2 I :=
    fun x hx => ((hK2 x).mp hx).elim (hKI x) (hPI x)
  have hK2Small : Small K2 mu := (ForcingSupportSize.native_small hM K2 mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM K mu).mp hK)
      ((ForcingSupportSize.native_small hM P mu).mp hPSmall) hK2)
  obtain ⟨V,q,hVUnion,hq,hqb,hqg,hAvoidQ⟩ := ConstructionPlacementPasting.extend_two_placements
    hM hChoice hw hMu hLarge ⟨hAI,hBI,hInter,hb,hg,hFixB,hFixG,hBG⟩ hV hK2Sub hASmall hBSmall hv hK2Small
  have hAvoidQK : Avoids K q v V := fun x y hx hn hxy hy =>
    hAvoidQ x y hx hn hxy ((hK2 y).mpr (Or.inl hy))
  have hAvoidQP : Avoids P q v V := fun x y hx hn hxy hy =>
    hAvoidQ x y hx hn hxy ((hK2 y).mpr (Or.inr hy))
  have hOverlapQ := overlap_of_two hA hB hV hRootA hq hb hg hFixB hqb hqg hBK hGamma hVUnion hAvoidQK
  have hSame : AgreesOn B p q := by
    intro x y hx hqxy
    obtain ⟨z,hgxz,_⟩ := hg.1.1.2 x (hBI x hx)
    have he := ForcingConditionGraphs.function_unique hq.1.1 hqxy (hqg x z hx hgxz)
    simpa only [he] using hpg x z hx hgxz
  refine ⟨p,q,hp,hq,hpa,hqb,hSame,hOverlapP,hOverlapQ,?_⟩
  intro z
  have hPBg := image_congr hBI hp hg hpg z
  have hQBg := image_congr hBI hq hg hqg z
  have hQAb := image_congr hAI hq hb hqb z
  constructor
  · rintro ⟨hzP,hzQ⟩
    obtain ⟨h,_⟩ := (image_inter_of_fresh hA hB hVUnion hAvoidQP z).mp ⟨hzQ,(hP z).mpr hzP⟩
    rcases h with h | h
    · have hzB := hQAb.mp h
      have hzA := (hOverlapP z).mp ⟨hzP,hBK z hzB⟩
      have hzRoot := (hInd z).mpr ⟨hzA,hzB⟩
      exact ⟨z,hRootB z hzRoot,hpg z z (hRootB z hzRoot) (hFixG z hzRoot)⟩
    · exact hPBg.mpr (hQBg.mp h)
  · intro hz
    exact ⟨image_mono hB z hz,image_mono hB z (hQBg.mpr (hPBg.mp hz))⟩

def imageAt {m : Nat} (p S z : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound S.succ))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound z.succ) (.bound p.succ)))

theorem imageAt_freeClosed {m : Nat} (p S z : Fin m) : (imageAt p S z).FreeClosed := by
  simp -implicitDefEqProofs [imageAt,Definitional.Formula.FreeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem imageAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p S z : Fin m) :
    Project.Formula.satisfies env (imageAt p S z) ↔ ImageAt (env.bound p) (env.bound S) (env.bound z) := by
  simp only [imageAt,ImageAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff
      (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def imageInside {m : Nat} (p S K : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (imageAt p.succ S.succ 0) (.mem (.bound 0) (.bound K.succ)))

theorem imageInside_freeClosed {m : Nat} (p S K : Fin m) : (imageInside p S K).FreeClosed := by
  simp -implicitDefEqProofs [imageInside,Definitional.Formula.FreeClosed,imageAt_freeClosed]

theorem imageInside_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p S K : Fin m) :
    Project.Formula.satisfies env (imageInside p S K) ↔ ImageInside (env.bound p) (env.bound S) (env.bound K) := by
  simp only [imageInside,ImageInside,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,imageAt_semantics hM,Project.Term.eval_bound]
  rfl

def overlap {m : Nat} (p v K a A : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.conj (imageAt p.succ v.succ 0) (.mem (.bound 0) (.bound K.succ)))
    (imageAt a.succ A.succ 0))

theorem overlap_freeClosed {m : Nat} (p v K a A : Fin m) : (overlap p v K a A).FreeClosed := by
  simp -implicitDefEqProofs [overlap,Definitional.Formula.FreeClosed,imageAt_freeClosed]

theorem overlap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p v K a A : Fin m) :
    Project.Formula.satisfies env (overlap p v K a A) ↔
      Overlap (env.bound p) (env.bound v) (env.bound K) (env.bound a) (env.bound A) := by
  simp only [overlap,Overlap,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,imageAt_semantics hM,Project.Term.eval_bound]
  rfl

def exactImages {m : Nat} (p q v B : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.conj (imageAt p.succ v.succ 0) (imageAt q.succ v.succ 0)) (imageAt p.succ B.succ 0))

theorem exactImages_freeClosed {m : Nat} (p q v B : Fin m) : (exactImages p q v B).FreeClosed := by
  simp -implicitDefEqProofs [exactImages,Definitional.Formula.FreeClosed,imageAt_freeClosed]

theorem exactImages_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p q v B : Fin m) :
    Project.Formula.satisfies env (exactImages p q v B) ↔
      ExactImages (env.bound p) (env.bound q) (env.bound v) (env.bound B) := by
  simp only [exactImages,ExactImages,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,imageAt_semantics hM]
  rfl

def inputs {m : Nat} (I A B root v K a b : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.subset (.bound A) (.bound v)) (.conj (Project.Formula.subset (.bound B)
  (.bound v)) (.conj (Project.Formula.subset (.bound v) (.bound I)) (.conj (Project.Formula.subset
  (.bound K) (.bound I)) (.conj (ConstructionPlacementPasting.intersection A B root) (.conj
  (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I a)) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.permutation I b)) (.conj (ProjectSyntax.encode id
  (ForcingLabelPermutations.fixes root a)) (.conj (ProjectSyntax.encode id
  (ForcingLabelPermutations.fixes root b)) (.conj (ConstructionPlacementPasting.imageIntersection a A b
  A root) (.conj (imageInside a A K) (imageInside b A K))))))))))))
theorem inputs_freeClosed {m : Nat} (I A B root v K a b : Fin m) :
    (inputs I A B root v K a b).FreeClosed := by
  simp -implicitDefEqProofs [inputs,Definitional.Formula.FreeClosed,Project.Formula.subset,
    ConstructionPlacementPasting.intersection_freeClosed,ProjectSyntax.freeClosed,
    ConstructionPlacementPasting.imageIntersection_freeClosed,imageInside_freeClosed]

theorem inputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A B root v K a b : Fin m) :
    Project.Formula.satisfies env (inputs I A B root v K a b) ↔
      Inputs (env.bound I) (env.bound A) (env.bound B) (env.bound root)
        (env.bound v) (env.bound K) (env.bound a) (env.bound b) := by
  simp only [inputs,Inputs,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    ConstructionPlacementPasting.intersection_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingLabelPermutations.fixes_semantics (M := M),
    ConstructionPlacementPasting.imageIntersection_semantics hM,imageInside_semantics hM,Project.Term.eval_bound]
  rfl

def result {m : Nat} (I A B v K a b p q : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I p)) (.conj (ProjectSyntax.encode
  id (ForcingConditionGraphs.permutation I q)) (.conj (ConstructionPlacementPasting.agreesOn A p a)
  (.conj (ConstructionPlacementPasting.agreesOn A q b) (.conj (ConstructionPlacementPasting.agreesOn B p
  q) (.conj (overlap p v K a A) (.conj (overlap q v K b A) (exactImages p q v B))))))))
theorem result_freeClosed {m : Nat} (I A B v K a b p q : Fin m) :
    (result I A B v K a b p q).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionPlacementPasting.agreesOn_freeClosed,overlap_freeClosed,exactImages_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A B v K a b p q : Fin m) :
    Project.Formula.satisfies env (result I A B v K a b p q) ↔
      Result (env.bound I) (env.bound A) (env.bound B) (env.bound v) (env.bound K)
        (env.bound a) (env.bound b) (env.bound p) (env.bound q) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ConstructionPlacementPasting.agreesOn_semantics hM,
    overlap_semantics hM,exactImages_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 10))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 10)) (.bound (1 : Fin 10))) (.imp (.neg
    (ProjectSyntax.encode id (ForcingSupportSize.small (2 : Fin 10) 1))) (.imp (inputs (2 : Fin 10) 3 4 5
    6 7 8 9) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin 10) 1)) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (7 : Fin 10) 1)) (.existsE (.existsE (result (2 :
    Fin 10).succ.succ (3 : Fin 10).succ.succ (4 : Fin 10).succ.succ (6 : Fin 10).succ.succ (7 : Fin
    10).succ.succ (8 : Fin 10).succ.succ (9 : Fin 10).succ.succ 1 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed,inputs_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),inputs_semantics hM,result_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hLarge h hv hK => three_copy_placement hM hChoice hw hMu hLarge h hv hK

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionPlacementTriple
