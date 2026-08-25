import Duper
import Duper.TPTP

-- set_option pp.all true
-- set_option pp.rawOnError true
-- set_option duper.printPortfolioInstance true
-- set_option duper.printTimeInformation true
-- set_option trace.duper.proofReconstruction true
set_option trace.debug true

-- set_option duper.split true

set_option trace.duper.prover.saturate true in
set_option trace.duper.setOfSupport.debug true in
set_option trace.duper.rule.split true in
set_option trace.duper.printProof true in
theorem test1 (x y : Nat) (h : x = y) : x = y := by duper [h]

-- set_option trace.duper.prover.saturate true in
-- set_option trace.duper.setOfSupport.debug true in
set_option trace.duper.rule.split true in
set_option trace.duper.printProof true in
theorem test3 (f g : α → α) : (∀ x, f x = g x) = (∀ x, f x = g x) := by duper

-- [duper.proofReconstruction] #0's newProof: fun hp => eq_true «_exHyp_uniq.39.223»
-- [duper.proofReconstruction] lvlReqs : [([], 0)], req: []
-- [duper.proofReconstruction] Instantiating parent (¬(∀ (x : _exTy_0), e!_0 x = e!_1 x) = ∀ (x : _exTy_0), e!_0 x = e!_1 x) =
--       True ≡≡ (¬(∀ (x : _exTy_0), e!_0 x = e!_1 x) = ∀ (x : _exTy_0), e!_0 x = e!_1 x) = True with param subst [] ↦ []
-- [duper.proofReconstruction] Reconstructing proof for #1 : [] ↦ [] @ ((∀ (x : _exTy_0), e!_0 x = e!_1 x) = ∀ (x : _exTy_0), e!_0 x = e!_1 x) =
--       False, Rule Name: clausification
-- [duper.proofReconstruction] parents: [_fvar.39.616], instTr: [], instC: ((∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) =
--         ∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) =
--       False
-- [duper.proofReconstruction] #1's newProof: fun hp => (fun h => Duper.clausify_not h) clause.0.0
-- [duper.proofReconstruction] lvlReqs : [([], 0)], req: []
-- [duper.proofReconstruction] Instantiating parent ((∀ (x : _exTy_0), e!_0 x = e!_1 x) = ∀ (x : _exTy_0), e!_0 x = e!_1 x) =
--       False ≡≡ ((∀ (x : _exTy_0), e!_0 x = e!_1 x) = ∀ (x : _exTy_0), e!_0 x = e!_1 x) = False with param subst [] ↦ []
-- [duper.proofReconstruction] Reconstructing proof for #2 : [] ↦ [] @ (∀ (x : _exTy_0), e!_0 x = e!_1 x) ≠
--       ∀ (x : _exTy_0), e!_0 x = e!_1 x, Rule Name: clausification
-- [duper.proofReconstruction] parents: [_fvar.39.620], instTr: [], instC: (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) ≠
--       ∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x
-- [duper.proofReconstruction] #2's newProof: fun hp => (fun h => Duper.not_of_eq_false h) clause.1.0
-- [duper.proofReconstruction] lvlReqs : [([], 0)], req: []
-- [duper.proofReconstruction] Instantiating parent (∀ (x : _exTy_0), e!_0 x = e!_1 x) ≠
--       ∀ (x : _exTy_0),
--         e!_0 x =
--           e!_1 x ≡≡ (∀ (x : _exTy_0), e!_0 x = e!_1 x) ≠ ∀ (x : _exTy_0), e!_0 x = e!_1 x with param subst [] ↦ []
-- [duper.proofReconstruction] Reconstructing proof for #3 : [] ↦ [] @ (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False ∨
--       (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False, Rule Name: clausification
-- [duper.proofReconstruction] parents: [_fvar.39.625], instTr: [], instC: (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) = False ∨
--       (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) = False
-- [duper.proofReconstruction] #3's newProof: fun hp => (fun h => Duper.clausify_prop_inequality1 h) clause.2.0
-- [duper.proofReconstruction] lvlReqs : [([], 0)], req: []
-- [duper.proofReconstruction] Instantiating parent (∀ (x : _exTy_0), e!_0 x = e!_1 x) ≠
--       ∀ (x : _exTy_0),
--         e!_0 x =
--           e!_1 x ≡≡ (∀ (x : _exTy_0), e!_0 x = e!_1 x) ≠ ∀ (x : _exTy_0), e!_0 x = e!_1 x with param subst [] ↦ []
-- [duper.proofReconstruction] Reconstructing proof for #4 : [] ↦ [] @ (∀ (x : _exTy_0), e!_0 x = e!_1 x) = True ∨
--       (∀ (x : _exTy_0), e!_0 x = e!_1 x) = True, Rule Name: clausification
-- [duper.proofReconstruction] parents: [_fvar.39.625], instTr: [], instC: (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) = True ∨
--       (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) = True
-- [duper.proofReconstruction] #4's newProof: fun hp => (fun h => Duper.clausify_prop_inequality2 h) clause.2.0
-- [duper.proofReconstruction] lvlReqs : [([], 0)], req: []
-- [duper.proofReconstruction] Instantiating parent (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False ∨
--       (∀ (x : _exTy_0), e!_0 x = e!_1 x) =
--         False ≡≡ ∀ (x_0 : _exTy_0),
--       (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False ∨ (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False with param subst [] ↦ []
-- [duper.proofReconstruction] Reconstructing skolem, _uniq.39.638 ≡≡ skol.0 : _exTy_0 → _exTy_0 := Duper.Skolem.some fun x => ¬e!_0 x = e!_1 x
-- [duper.proofReconstruction] Reconstructing proof for #5 : [] ↦ [] @ ∀ (a : _exTy_0),
--       (∀ (x : _exTy_0), e!_0 x = e!_1 x) = False ∨
--         (¬e!_0 (skol.0 a) = e!_1 (skol.0 a)) = True, Rule Name: clausification
-- [duper.proofReconstruction] parents: [_fvar.39.631], instTr: [fun x_0 => x_0,
--      fun x_0 x =>
--        ¬@_fvar.39.208 x =
--            @_fvar.39.209
--              x], instC: ∀ (a : _fvar.39.207),
--       (∀ (x : _fvar.39.207), @_fvar.39.208 x = @_fvar.39.209 x) = False ∨
--         (¬@_fvar.39.208 (@_fvar.39.638 a) = @_fvar.39.209 (@_fvar.39.638 a)) = True
-- [duper.proofReconstruction] #5's newProof: fun hp a =>
--       (fun h =>
--           Or.elim h
--             (fun h => Or.inr (eq_true (Duper.Skolem.spec ((fun x_0 => x_0) a) (Duper.exists_of_forall_eq_false h))))
--             fun h => Or.inl h)
--         clause.3.0

set_option trace.duper.prover.saturate true in
set_option trace.duper.setOfSupport.debug true in
set_option trace.duper.printProof true in
set_option trace.duper.proofReconstruction true in
set_option duper.split true in
-- set_option trace.duper.split true in
theorem cleanest_split (x y : Prop) (h1 : x) (h2 : y) : x ∧ y := by duper [h1, h2]

#print cleanest_split

set_option trace.duper.prover.saturate true in
set_option trace.duper.setOfSupport.debug true in
set_option trace.duper.printProof true in
set_option trace.duper.proofReconstruction true in
set_option duper.split true in
theorem cleanest_split2 (w x y z : Prop) (h1 : x) (h2 : y) (h3 : y = w) (h4 : x = z) : x ∧ (y = w) ∧ (x = z) ∧ y := by duper [h1, h2, h3, h4]

-- set_option trace.duper.prover.saturate true in
-- set_option trace.duper.setOfSupport.debug true in
-- set_option trace.duper.printProof true in
-- set_option trace.duper.proofReconstruction true in
-- set_option duper.split true in
-- theorem long_split (w x y z : Prop) (h1 : x) (h2 : y) (h3 : w) (h4 : z) : x ∧ y ∧ w ∧ z := by duper [h1, h2, h3, h4]

-- theorem potentially_split (f : Int → Int → Prop) (x : Int) : f x 0 ∨ f x 1 :=

-- set_option duper.split true in
-- tptp' testingts "../CASC-30/THF/TNE/SEV244^6.p" by duper [*] {portfolioInstance := 9}

-- set_option duper.split true in
-- tptp' testingts "../CASC-30/THF/TEQ/AGT030^1.p" by duper [*] {portfolioInstance := 9}

-- set_option maxHeartbeats 2000000 in
-- set_option duper.split true in
-- set_option trace.duper.printProof true in
-- theorem H_.cTHM2A_pme : ¬∀ (K : (Iota → Prop) → Iota → Prop),
--     (∀ (Xx Xy : Iota → Prop), (∀ (Xx0 : Iota), Xx Xx0 → Xy Xx0) → ∀ (Xx0 : Iota), K Xx Xx0 → K Xy Xx0) →
--       ∀ (Xx : Iota),
--         K (fun Xx0 => ∃ S, (∀ (Xx1 : Iota), S Xx1 → K S Xx1) ∧ S Xx0) Xx ↔ ∃ S, (∀ (Xx0 : Iota), S Xx0 → K S Xx0) ∧ S Xx → False := by duper [*] {portfolioInstance := 9}

-- set_option trace.duper.prover.saturate true in
-- set_option trace.duper.printProof true in
-- set_option trace.duper.proofReconstruction true in
-- set_option duper.split true in
-- theorem longer_split (w x y z a b c d e f g h x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop) (h1 : w) (h2 : x) (h3 : y) (h4 : z) (h5 : a) (h6 : b) (h7 : c) (h8 : d)
--   (h9 : e) (h10 : f) (h11 : g) (h12 : h) (j1 : x1) (j2 : x2) (j3 : x3) (j4 : x4) (j5 : x5) (j6 : x6) (j7 : x7) (j8 : x8) (j9 : x9) (j10 : x10)
--   : w ∧ x ∧ y ∧ z ∧ a ∧ b ∧ c ∧ d ∧ e ∧ f ∧ g ∧ h ∧ x1 ∧ x2 ∧ x3 ∧ x4 ∧ x5 ∧ x6 ∧ x7 ∧ x8 ∧ x9 ∧ x10 := by duper [*]

-- set_option trace.duper.prover.saturate true in
-- set_option duper.split true in
-- set_option trace.duper.rule.split true in
-- theorem longest_split (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
--   x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40
--   x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60
--   x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80
--   x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100 : Prop)
--   (h1 : x1) (h2 : x2) (h3 : x3) (h4 : x4) (h5 : x5) (h6 : x6) (h7 : x7) (h8 : x8)
--   (h9 : x9) (h10 : x10) (h11 : x11) (h12 : x12) (h13 : x13) (h14 : x14) (h15 : x15)
--   (h16 : x16) (h17 : x17) (h18 : x18) (h19 : x19) (h20 : x20) (h21 : x21) (h22 : x22)
--   (h23 : x23) (h24 : x24) (h25 : x25) (h26 : x26) (h27 : x27) (h28 : x28) (h29 : x29)
--   (h30 : x30) (h31 : x31) (h32 : x32) (h33 : x33) (h34 : x34) (h35 : x35) (h36 : x36)
--   (h37 : x37) (h38 : x38) (h39 : x39) (h40 : x40) (h41 : x41) (h42 : x42) (h43 : x43)
--   (h44 : x44) (h45 : x45) (h46 : x46) (h47 : x47) (h48 : x48) (h49 : x49) (h50 : x50)
--   (h51 : x51) (h52 : x52) (h53 : x53) (h54 : x54) (h55 : x55) (h56 : x56) (h57 : x57)
--   (h58 : x58) (h59 : x59) (h60 : x60) (h61 : x61) (h62 : x62) (h63 : x63) (h64 : x64)
--   (h65 : x65) (h66 : x66) (h67 : x67) (h68 : x68) (h69 : x69) (h70 : x70) (h71 : x71)
--   (h72 : x72) (h73 : x73) (h74 : x74) (h75 : x75) (h76 : x76) (h77 : x77) (h78 : x78)
--   (h79 : x79) (h80 : x80) (h81 : x81) (h82 : x82) (h83 : x83) (h84 : x84) (h85 : x85)
--   (h86 : x86) (h87 : x87) (h88 : x88) (h89 : x89) (h90 : x90) (h91 : x91) (h92 : x92)
--   (h93 : x93) (h94 : x94) (h95 : x95) (h96 : x96) (h97 : x97) (h98 : x98) (h99 : x99)
--   (h100 : x100)
--   : x1 ∧ x2 ∧ x3 ∧ x4 ∧ x5 ∧ x6 ∧ x7 ∧ x8 ∧ x9 ∧ x10 ∧
--     x11 ∧ x12 ∧ x13 ∧ x14 ∧ x15 ∧ x16 ∧ x17 ∧ x18 ∧ x19 ∧ x20 ∧
--     x21 ∧ x22 ∧ x23 ∧ x24 ∧ x25 ∧ x26 ∧ x27 ∧ x28 ∧ x29 ∧ x30 ∧
--     x31 ∧ x32 ∧ x33 ∧ x34 ∧ x35 ∧ x36 ∧ x37 ∧ x38 ∧ x39 ∧ x40 ∧
--     x41 ∧ x42 ∧ x43 ∧ x44 ∧ x45 ∧ x46 ∧ x47 ∧ x48 ∧ x49 ∧ x50 := by
--   duper [*]

-- needs 250 clauses without splitting
-- 253 with

-- set_option trace.duper.prover.saturate true in
-- set_option trace.duper.setOfSupport.debug true in
-- set_option trace.duper.rule.split true in
-- theorem test_split (a b : (α → α) → α → α) (f g h j : α → α) :
-- (∀ x, a f x = b g x) = (∀ x, a f x = b g x) ∧ (∀ x, h x = j x) = (∀ x, h x = j x) := by duper

-- set_option trace.duper.rule.split true in
-- set_option duper.split true in
-- theorem puzzle1 {ι : Type} (johanna : ι) (bill : ι) (peanuts : ι)
--   (food : ι → Prop) (alive : ι → Prop)
--   (likes : ι → ι → Prop) (eats : ι → ι → Prop) (was_killed_by : ι → ι → Prop)
--   (h1 : ∀ x, food x → likes johanna x)
--   (h2 : ∀ x, (∃ y, eats y x ∧ ¬ was_killed_by y x) → food x)
--   (h3 : eats bill peanuts)
--   (h4 : alive bill)
--   (h5 : ∀ y, alive y → ∀ x, ¬ was_killed_by y x) :
-- likes johanna peanuts := by duper [*]

theorem exclude_mid (p : Prop) : (p → False) ∧ (¬p → False) → False := by
  intro h
  exact h.2 h.1

theorem exclude_mid_no_tactic (p : Prop) : (p → False) ∧ (¬p → False) → False :=
  fun ⟨hp, hnp⟩ => hnp hp

theorem true_imp_false_gg : (true → False) → False :=
  fun h => h rfl

theorem add_imp (a : Prop) (h : a) : ∃ p : Bool, (p → a) ∧ (¬p → False) := by
  apply Exists.intro true
  apply And.intro
  · intros
    exact h
  · intro np
    exact False.elim (np rfl)

theorem one_split (a b c d : Prop) (h : a ∨ b ∨ c ∨ d) : ∃ p : Bool, (p → (a ∨ b)) ∧ (¬p → (c ∨ d)) := by
  rcases h with ha | hb | hc | hd
  -- · exact ⟨true,  fun _ => Or.inl ha, fun hn => absurd rfl hn⟩
  · apply Exists.intro true
    apply And.intro
    · intro hp
      exact Or.inl ha
    · intro hn
      exact False.elim (hn rfl)
  · exact ⟨true,  fun _ => Or.inr hb, fun hn => absurd rfl hn⟩
  -- · exact ⟨false, fun hf => Bool.noConfusion hf, fun _ => Or.inl hc⟩
  · apply Exists.intro false
    apply And.intro
    · intro hn
      exact Bool.noConfusion hn
    · intro hp
      exact Or.inl hc
  · exact ⟨false, fun hf => Bool.noConfusion hf, fun _ => Or.inr hd⟩

example (p : Bool) (a a' : Prop) (h : a → a') : (p → a) → (p → a') := by
  intro hpa hp
  exact h (hpa hp)

example (p : Bool) (a a' : Prop) (h : a → a') : (p → a) → (p → a') :=
  fun hpa => (fun hp => h (hpa hp))

theorem split_usage (a b c d : Prop) (h1 : a ∨ b → False) (h2 : c ∨ d → False) : a ∨ b ∨ c ∨ d → False := by
  intro h
  have h3 := one_split a b c d h
  obtain ⟨p, hp1, hp2⟩ := h3
  cases p
  · exact h2 (hp2 (fun hf => Bool.noConfusion hf))
  · exact h1 (hp1 rfl)
