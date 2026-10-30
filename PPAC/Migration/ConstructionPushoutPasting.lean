/- Pinned MergerPushouts.IsPushout.flip/paste/cancel_left:385-448.
Consumers: CellReorder.Square.paste/cancel_left, future_cut and future_omitted_square.
Reuse the EXISTING Hom, SquareComm, IsPushout and actual graph composition. -/
import PPAC.Migration.ConstructionProbePushoutSyntax

namespace PPAC.Migration.ConstructionPushoutPasting
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom SquareComm IsPushout composition_value composition_preserves)
open ConstructionProbeMappedPath (NodeMap exists_node_map)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Compose the given internal homomorphisms using the existing native constructor. -/
theorem exists_hom_comp (hM : FirstOrder.Theory.Models M nativeZF)
    {A B C mulA mulB mulC eA eB eC f g : M.Carrier .set}
    (hf : Hom A B mulA mulB eA eB f) (hg : Hom B C mulB mulC eB eC g) :
    ∃ comp, Hom A C mulA mulC eA eC comp ∧ NodeMap f g comp := by
  obtain ⟨comp,hcomp,hgraph⟩ := exists_node_map hM hf.1 hg.1
  exact ⟨comp,⟨hcomp,(hgraph eA eC).mpr ⟨eB,hf.2.1,hg.2.1⟩,
    composition_preserves hgraph hf.2.2 hg.2.2⟩,hgraph⟩

/-- Associativity of the SAME graph compositions; no new graph backend. -/
theorem nodeMap_assoc {f g h fg gh out : M.Carrier .set}
    (hfg : NodeMap f g fg) (hgh : NodeMap g h gh) :
    NodeMap fg h out ↔ NodeMap f gh out := by
  have he (x z : M.Carrier .set) :
      (∃ y, PureKuratowski.PairMember M x y fg ∧ PureKuratowski.PairMember M y z h) ↔
      (∃ y, PureKuratowski.PairMember M x y f ∧ PureKuratowski.PairMember M y z gh) := by
    constructor
    · rintro ⟨y,hxy,hyz⟩
      obtain ⟨b,hxb,hby⟩ := (hfg x y).mp hxy
      exact ⟨b,hxb,(hgh b z).mpr ⟨y,hby,hyz⟩⟩
    · rintro ⟨y,hxy,hyz⟩
      obtain ⟨b,hyb,hbz⟩ := (hgh y z).mp hyz
      exact ⟨b,(hfg x b).mpr ⟨y,hxy,hyb⟩,hbz⟩
  exact ⟨fun ho x z => (ho x z).trans (he x z),fun ho x z => (ho x z).trans (he x z).symm⟩

/-- Postcompose both sides of an actual commuting square. -/
theorem square_post {f g i j k s t : M.Carrier .set}
    (hc : SquareComm f g i j) (hi : NodeMap i k s) (hj : NodeMap j k t) :
    SquareComm f g s t := by
  intro x a b y hxa hxb
  rw [hi a y,hj b y]
  exact exists_congr (fun z => and_congr_left (fun _ => hc x a b z hxa hxb))

/-- Redirect a composite across the commuting square, with actual source domains. -/
theorem square_redirect {A B C f g s t out : M.Carrier .set}
    (hf : MapsTo A B f) (hg : MapsTo A C g)
    (hc : SquareComm f g s t) (ho : NodeMap f s out) : NodeMap g t out := by
  intro x y
  constructor
  · intro hx
    obtain ⟨b,hxb,hby⟩ := (ho x y).mp hx
    obtain ⟨c,hxc,_⟩ := hg.1.2 x (ForcingConditionGraphs.function_input hf.1 hxb)
    exact ⟨c,hxc,(hc x b c y hxb hxc).mp hby⟩
  · rintro ⟨c,hxc,hcy⟩
    obtain ⟨b,hxb,_⟩ := hf.1.2 x (ForcingConditionGraphs.function_input hg.1 hxc)
    exact (ho x y).mpr ⟨b,hxb,(hc x b c y hxb hxc).mpr hcy⟩

/-- The commutativity part of source horizontal pasting. -/
theorem square_paste {A B C D ab ac bd cd be df ef ae cf : M.Carrier .set}
    (hab : MapsTo A B ab) (hbd : MapsTo B D bd) (hcd : MapsTo C D cd)
    (hae : NodeMap ab be ae) (hcf : NodeMap cd df cf)
    (hleft : SquareComm ab ac bd cd) (hright : SquareComm be bd ef df) :
    SquareComm ae ac ef cf := by
  intro x e c y hxe hxc
  obtain ⟨b,hxb,hbe⟩ := (hae x e).mp hxe
  obtain ⟨d,hbd',_⟩ := hbd.1.2 b (hab.2 x b hxb)
  have hcd' := (hleft x b c d hxb hxc).mp hbd'
  exact (hright b e d y hbe hbd').trans (composition_value hcd hcf hcd').symm

/-- The original diagonal reflection, on the unchanged full universal property. -/
theorem flip {B C D mulB mulC mulD eB eC eD ab ac bd cd : M.Carrier .set}
    (h : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) :
    IsPushout B C D mulB mulC mulD eB eC eD ac ab cd bd := by
  refine ⟨fun x c b y hxc hxb => (h.1 x b c y hxb hxc).symm,?_⟩
  intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨L,hL,hLB,hLC,hu⟩ := h.2 Q J mulQ eQ t s hJ hMul hUnit hAssoc ht hs
    (fun x b c y hxb hxc => (hc x c b y hxc hxb).symm)
  exact ⟨L,hL,hLC,hLB,fun R hR hRC hRB => hu R hR hRB hRC⟩

/-- Pinned IsPushout.paste, with actual composite graphs and universal targets. -/
theorem paste (hM : FirstOrder.Theory.Models M nativeZF)
    {A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : M.Carrier .set}
    (hab : MapsTo A B ab)
    (hbd : Hom B D mulB mulD eB eD bd) (hcd : Hom C D mulC mulD eC eD cd)
    (hbe : Hom B E mulB mulE eB eE be) (hdf : Hom D F mulD mulF eD eF df)
    (hae : NodeMap ab be ae) (hcf : NodeMap cd df cf)
    (h : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd)
    (h' : IsPushout D E F mulD mulE mulF eD eE eF be bd ef df) :
    IsPushout C E F mulC mulE mulF eC eE eF ae ac ef cf := by
  refine ⟨square_paste hab hbd.1 hcd.1 hae hcf h.1 h'.1,?_⟩
  intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨sb,hsb,hsbGraph⟩ := exists_hom_comp hM hbe hs
  have hleft : SquareComm ab ac sb t := by
    intro x b c y hxb hxc
    obtain ⟨eb,heb,_⟩ := hbe.1.1.2 b (hab.2 x b hxb)
    have hxe := (hae x eb).mpr ⟨b,hxb,heb⟩
    exact (composition_value hbe.1 hsbGraph heb).trans (hc x eb c y hxe hxc)
  obtain ⟨d,hd,hdB,hdC,hdUnique⟩ := h.2 Q J mulQ eQ sb t hJ hMul hUnit hAssoc hsb ht hleft
  have hright : SquareComm be bd s d := by
    intro b eb db y hbe' hbd'
    exact (composition_value hbe.1 hsbGraph hbe').symm.trans
      (composition_value hbd.1 hdB hbd')
  obtain ⟨L,hL,hLE,hLD,hLUnique⟩ := h'.2 Q J mulQ eQ s d hJ hMul hUnit hAssoc hs hd hright
  have hLC : NodeMap cf L t := (nodeMap_assoc hcf hLD).mpr hdC
  refine ⟨L,hL,hLE,hLC,?_⟩
  intro R hR hRE hRC
  obtain ⟨rD,hrD,hrDGraph⟩ := exists_hom_comp hM hdf hR
  have hrDB : NodeMap bd rD sb := square_redirect hbe.1 hbd.1
    (square_post h'.1 hRE hrDGraph) hsbGraph
  have hrDC : NodeMap cd rD t := (nodeMap_assoc hcf hrDGraph).mp hRC
  have he : rD = d := hdUnique rD hrD hrDB hrDC
  subst rD
  exact hLUnique R hR hRE hrDGraph

/-- Pinned IsPushout.cancel_left, used for each omitted reordered cell. -/
theorem cancel_left (hM : FirstOrder.Theory.Models M nativeZF)
    {A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : M.Carrier .set}
    (hab : MapsTo A B ab)
    (hbd : Hom B D mulB mulD eB eD bd) (hcd : Hom C D mulC mulD eC eD cd)
    (hbe : Hom B E mulB mulE eB eE be) (hdf : Hom D F mulD mulF eD eF df)
    (hae : NodeMap ab be ae) (hcf : NodeMap cd df cf)
    (h : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd)
    (hc : SquareComm be bd ef df)
    (ho : IsPushout C E F mulC mulE mulF eC eE eF ae ac ef cf) :
    IsPushout D E F mulD mulE mulF eD eE eF be bd ef df := by
  refine ⟨hc,?_⟩
  intro Q J mulQ eQ s d hJ hMul hUnit hAssoc hs hd hright
  obtain ⟨c,hcHom,hcGraph⟩ := exists_hom_comp hM hcd hd
  have houter := square_paste hab hbd.1 hcd.1 hae hcGraph h.1 hright
  obtain ⟨L,hL,hLE,hLC,hLUnique⟩ := ho.2 Q J mulQ eQ s c hJ hMul hUnit hAssoc hs hcHom houter
  obtain ⟨rD,hrD,hrDGraph⟩ := exists_hom_comp hM hdf hL
  obtain ⟨sb,hsb,hsbGraph⟩ := exists_hom_comp hM hbe hs
  have hdB : NodeMap bd d sb := square_redirect hbe.1 hbd.1 hright hsbGraph
  have hrDB : NodeMap bd rD sb := square_redirect hbe.1 hbd.1
    (square_post hc hLE hrDGraph) hsbGraph
  have hrDC : NodeMap cd rD c := (nodeMap_assoc hcf hrDGraph).mp hLC
  obtain ⟨u,_,_,_,hu⟩ := h.2 Q J mulQ eQ sb c hJ hMul hUnit hAssoc hsb hcHom
    (square_post h.1 hdB hcGraph)
  have he : rD = d := (hu rD hrD hrDB hrDC).trans (hu d hd hdB hcGraph).symm
  subst rD
  refine ⟨L,hL,hLE,hrDGraph,?_⟩
  intro R hR hRE hRD
  exact hLUnique R hR hRE ((nodeMap_assoc hcf hRD).mpr hcGraph)

/-- Identity composition on the existing literal graph. -/
theorem identity_comp {A Q f ident : M.Carrier .set}
    (hf : MapsTo A Q f) (hi : ForcingConditionGraphs.IdentityGraph A ident) : NodeMap ident f f := by
  intro x y
  constructor
  · intro hxy
    exact ⟨x,(hi x x).mpr ⟨ForcingConditionGraphs.function_input hf.1 hxy,rfl⟩,hxy⟩
  · rintro ⟨z,hxz,hzy⟩
    have he := ((hi x z).mp hxz).2
    exact he.symm ▸ hzy

/-- Source of_id, used by the base case of CellReorder.future_cut. -/
theorem of_id (hM : FirstOrder.Theory.Models M nativeZF)
    {A B mulA mulB eA eB f idA idB : M.Carrier .set}
    (hf : Hom A B mulA mulB eA eB f)
    (hIA : ForcingConditionGraphs.IdentityGraph A idA)
    (hIB : ForcingConditionGraphs.IdentityGraph B idB) :
    IsPushout B A B mulB mulA mulB eB eA eB idA f f idB := by
  refine ⟨?_,?_⟩
  · intro x a b y hxa hxb
    have he := ((hIA x a).mp hxa).2
    subst a
    constructor
    · intro hxy
      exact (hIB b y).mpr ⟨hf.1.2 x b hxb,
        (ForcingConditionGraphs.function_unique hf.1.1 hxy hxb).symm⟩
    · intro hby
      exact ((hIB b y).mp hby).2 ▸ hxb
  · intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
    have hft : NodeMap f t s := by
      intro x y
      constructor
      · intro hxy
        have hx := ForcingConditionGraphs.function_input hs.1.1 hxy
        obtain ⟨b,hxb,_⟩ := hf.1.1.2 x hx
        exact ⟨b,hxb,(hc x x b y ((hIA x x).mpr ⟨hx,rfl⟩) hxb).mp hxy⟩
      · rintro ⟨b,hxb,hby⟩
        have hx := ForcingConditionGraphs.function_input hf.1.1 hxb
        exact (hc x x b y ((hIA x x).mpr ⟨hx,rfl⟩) hxb).mpr hby
    refine ⟨t,ht,hft,identity_comp ht.1 hIB,?_⟩
    intro R hR _ hRI
    apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM B Q R).mp hR.1).1.1
      ((ForcingSupportSize.native_mapsTo hM B Q t).mp ht.1).1.1
    intro x y
    exact (identity_comp hR.1 hIB x y).trans (hRI x y).symm

def flipSentence {m : Nat} (B C D mulB mulC mulD eB eC eD ab ac bd cd : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (ConstructionProbePushoutSyntax.isPushout B C D mulB mulC mulD eB eC eD ac ab cd bd))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, 
      ConstructionProbePushoutSyntax.isPushout_freeClosed
      
      
      ]

theorem flip_models {m : Nat} (B C D mulB mulC mulD eB eC eD ab ac bd cd : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (flipSentence B C D mulB mulC mulD eB eC eD ab ac bd cd)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (flipSentence B C D mulB mulC mulD eB eC eD ab ac bd cd)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    
    
    ConstructionProbePushoutSyntax.isPushout_semantics hM
    
    
    ]
  exact flip

theorem flip_kernel_certificate {m : Nat} (B C D mulB mulC mulD eB eC eD ab ac bd cd : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (flipSentence B C D mulB mulC mulD eB eC eD ab ac bd cd)) :=
  ModelTransfer.derives (fun _ hM => flip_models B C D mulB mulC mulD eB eC eD ab ac bd cd hM)

def pasteSentence {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ab A B)) (.imp (ConstructionProbePushoutSyntax.hom B D mulB mulD eB eD bd) (.imp (ConstructionProbePushoutSyntax.hom C D mulC mulD eC eD cd) (.imp (ConstructionProbePushoutSyntax.hom B E mulB mulE eB eE be) (.imp (ConstructionProbePushoutSyntax.hom D F mulD mulF eD eF df) (.imp (ConstructionProbeMappedPathSyntax.nodeMap ab be ae) (.imp (ConstructionProbeMappedPathSyntax.nodeMap cd df cf) (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (.imp (ConstructionProbePushoutSyntax.isPushout D E F mulD mulE mulF eD eE eF be bd ef df) (ConstructionProbePushoutSyntax.isPushout C E F mulC mulE mulF eC eE eF ae ac ef cf))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.isPushout_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem paste_models {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (pasteSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (pasteSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbePushoutSyntax.isPushout_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact paste hM

theorem paste_kernel_certificate {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (pasteSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)) :=
  ModelTransfer.derives (fun _ hM => paste_models A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf hM)

def cancelSentence {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ab A B)) (.imp (ConstructionProbePushoutSyntax.hom B D mulB mulD eB eD bd) (.imp (ConstructionProbePushoutSyntax.hom C D mulC mulD eC eD cd) (.imp (ConstructionProbePushoutSyntax.hom B E mulB mulE eB eE be) (.imp (ConstructionProbePushoutSyntax.hom D F mulD mulF eD eF df) (.imp (ConstructionProbeMappedPathSyntax.nodeMap ab be ae) (.imp (ConstructionProbeMappedPathSyntax.nodeMap cd df cf) (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (.imp (ConstructionProbePushoutSyntax.squareComm be bd ef df) (.imp (ConstructionProbePushoutSyntax.isPushout C E F mulC mulE mulF eC eE eF ae ac ef cf) (ConstructionProbePushoutSyntax.isPushout D E F mulD mulE mulF eD eE eF be bd ef df)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.isPushout_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbePushoutSyntax.squareComm_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem cancel_models {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (cancelSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (cancelSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbePushoutSyntax.isPushout_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbePushoutSyntax.squareComm_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact cancel_left hM

theorem cancel_kernel_certificate {m : Nat} (A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (cancelSentence A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf)) :=
  ModelTransfer.derives (fun _ hM => cancel_models A B C D E F mulB mulC mulD mulE mulF eB eC eD eE eF ab ac bd cd be df ef ae cf hM)

def identitySentence {m : Nat} (A B mulA mulB eA eB f idA idB : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionProbePushoutSyntax.hom A B mulA mulB eA eB f)
      (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph A idA))
        (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph B idB))
          (ConstructionProbePushoutSyntax.isPushout B A B mulB mulA mulB eB eA eB idA f f idB))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed, ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem identity_models {m : Nat} (A B mulA mulB eA eB f idA idB : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (identitySentence A B mulA mulB eA eB f idA idB)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (identitySentence A B mulA mulB eA eB f idA idB)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionProbePushoutSyntax.isPushout_semantics hM]
  exact of_id hM

theorem identity_kernel_certificate {m : Nat} (A B mulA mulB eA eB f idA idB : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (identitySentence A B mulA mulB eA eB f idA idB)) :=
  ModelTransfer.derives (fun _ hM => identity_models A B mulA mulB eA eB f idA idB hM)

end PPAC.Migration.ConstructionPushoutPasting
