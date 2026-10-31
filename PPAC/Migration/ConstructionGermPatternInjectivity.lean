/- Pinned StableSelectors.good_dense:207-219, bounded-pattern injectivity.
Consume the actual full germ pattern, unequal-class detector separation,
countable site coverage and simultaneous opposite bits below alpha.
The common late index is INTERNAL; no external standardness of omega. -/
import PPAC.Migration.ConstructionGermPattern
import PPAC.Migration.ConstructionGermSeparation
import PPAC.Migration.ConstructionCohenPairSeparation
import PPAC.Migration.ConstructionGermDetectorSites

namespace PPAC.Migration.ConstructionGermPatternInjectivity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N alpha B A E T det R pr F J pairs p lo hi : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hSep : ConstructionGermSeparation.Separation w D chain H N det)
    (hCover : ConstructionGermDetectorSites.Covers w H det J)
    (hPairs : ConstructionCohenPairSeparation.Pairs J pairs)
    (hReq : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z pairs → ConstructionCohenPairSeparation.Requirement alpha lo hi z p)
    (hExtend : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExact : ConstructionGermEventual.Exact w pr)
    (hPattern : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F)
    (hne : lo ≠ hi) : Injection G T F := by
  refine ⟨hPattern.1,?_⟩
  intro C1 C2 P hC1P hC2P
  apply Classical.byContradiction
  intro hCne
  obtain ⟨_,g,hg,hClassG,hRawG⟩ := (hPattern.2 C1 P).mp hC1P
  obtain ⟨_,h,hh,hClassH,hRawH⟩ := (hPattern.2 C2 P).mp hC2P
  obtain ⟨delta,bsep,hdelta,hbsep,hSeparate⟩ := hSep g h C1 C2 hg hh hClassG hClassH hCne
  obtain ⟨e,hde,_⟩ := hRawG.1.1.2 delta hdelta
  obtain ⟨s,hs,hse⟩ := ((hRawG.2 delta e).mp hde).2
  obtain ⟨t,ht,hte⟩ := ((hRawH.2 delta e).mp hde).2
  obtain ⟨beq,hbeq,hEqual⟩ := (hExact s t e e hse hte).mp rfl
  obtain ⟨bg,hbg,hCg⟩ := hCover g hg
  obtain ⟨bh,hbh,hCh⟩ := hCover h hh
  have upper (a b : M.Carrier .set) (ha : (Project.FirstOrderSemantics.reduct M).mem a w)
      (hb : (Project.FirstOrderSemantics.reduct M).mem b w) :
      ∃ n, (Project.FirstOrderSemantics.reduct M).mem n w ∧ NatLe a n ∧ NatLe b n := by
    rcases ConstructionFractionOrder.nat_compare hM hw ha hb with e | hab | hba
    · exact ⟨b,hb,Or.inl e,Or.inl rfl⟩
    · exact ⟨b,hb,Or.inr hab,Or.inl rfl⟩
    · exact ⟨a,ha,Or.inl rfl,Or.inr hba⟩
  obtain ⟨n1,hn1,hsep1,heq1⟩ := upper bsep beq hbsep hbeq
  obtain ⟨n2,hn2,hg2,hh2⟩ := upper bg bh hbg hbh
  obtain ⟨n,hn,h1n,h2n⟩ := upper n1 n2 hn1 hn2
  have trans {a b : M.Carrier .set} (hab : NatLe a b) (hbn : NatLe b n) : NatLe a n :=
    ZF.eqOrMem_trans (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) n hn) hab hbn
  obtain ⟨d,x,y,z,hd,hx,hxy,hxz,hyz⟩ := hSeparate n hn (trans hsep1 h1n)
  have hyJ := hCg delta n d x y hd hx (trans hg2 h2n) hxy
  have hzJ := hCh delta n d x z hd hx (trans hh2 h2n) hxz
  obtain ⟨pair,hpair⟩ := KuratowskiZF.exists_code hM y z
  obtain ⟨y',z',b,hpair',hb,hybit,hzbit⟩ := hReq pair ((hPairs pair).mpr ⟨y,z,hyJ,hzJ,hyz,hpair⟩)
  obtain ⟨ey,ez⟩ := PureKuratowski.code_injective hpair' hpair
  subst y'
  subst z'
  obtain ⟨row,hnrow,_⟩ := hs.1.1.2 n hn
  have hRowG := ((hs.2 n row).mp hnrow).2
  have hRowH := ((ht.2 n row).mp ((hEqual n hn (trans heq1 h1n) row).mp hnrow)).2
  have lift {a v : M.Carrier .set} (hav : PureKuratowski.PairMember M a v p) : PureKuratowski.PairMember M a v R := by
    obtain ⟨u,hu,hup⟩ := hav
    exact ⟨u,hu,hExtend u hup⟩
  obtain ⟨ay,hay,haybit⟩ := hybit
  obtain ⟨az,haz,hazbit⟩ := hzbit
  have hLow := (hRowG.2 b lo).mpr ⟨hb,d,x,y,ay,hd,hx,hxy,hay,lift haybit⟩
  have hHigh := (hRowH.2 b hi).mpr ⟨hb,d,x,z,az,hd,hx,hxz,haz,lift hazbit⟩
  exact hne (ForcingConditionGraphs.function_unique hRowG.1.1 hLow hHigh)

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N alpha B A E T det R pr F J pairs p lo hi : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hSep : ConstructionGermSeparation.Separation w D chain H N det)
    (hCover : ConstructionGermDetectorSites.Covers w H det J)
    (hPairs : ConstructionCohenPairSeparation.Pairs J pairs)
    (hReq : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z pairs → ConstructionCohenPairSeparation.Requirement alpha lo hi z p)
    (hExtend : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExact : ConstructionGermEventual.Exact w pr)
    (hPattern : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo) : Injection G T F := by
  apply injective hM hw hSep hCover hPairs hReq hExtend hExact hPattern
  intro e
  subst hi
  exact hlo lo hhi.predecessor_mem

def constructionSentence {m : Nat} (w D chain H G N alpha B A E T det R pr F J pairs p lo hi : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionGermSeparation.separation w D chain H N det) (.imp (ConstructionGermDetectorSites.coversFormula w H det J) (.imp (ConstructionCohenPairSeparation.pairs J pairs) (.imp (.forallE (.imp (.mem (.bound 0) (.bound pairs.succ)) (ConstructionCohenPairSeparation.requirement alpha.succ lo.succ hi.succ 0 p.succ))) (.imp (Project.Formula.subset (.bound p) (.bound R)) (.imp (ConstructionGermEventual.exactProjection w pr) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (ProjectSyntax.encode id (Source.SetLanguage.injection F G T))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.subset,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.extensionalEq,ProjectSyntax.freeClosed,
      ConstructionGermSeparation.separation_freeClosed,ConstructionGermDetectorSites.coversFormula_freeClosed,
      ConstructionCohenPairSeparation.pairs_freeClosed,ConstructionCohenPairSeparation.requirement_freeClosed,
      ConstructionGermEventual.exactProjection_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem construction_models {m : Nat} (w D chain H G N alpha B A E T det R pr F J pairs p lo hi : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D chain H G N alpha B A E T det R pr F J pairs p lo hi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D chain H G N alpha B A E T det R pr F J pairs p lo hi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionGermSeparation.separation_semantics hM,
    ConstructionGermDetectorSites.coversFormula_semantics hM,ConstructionCohenPairSeparation.pairs_semantics hM,
    ConstructionCohenPairSeparation.requirement_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,
    ConstructionGermPattern.pattern_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M)]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w D chain H G N alpha B A E T det R pr F J pairs p lo hi : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w D chain H G N alpha B A E T det R pr F J pairs p lo hi)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D chain H G N alpha B A E T det R pr F J pairs p lo hi hM)

end PPAC.Migration.ConstructionGermPatternInjectivity
