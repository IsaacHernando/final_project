-- import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
-- import Mathlib.Init.Data.Int.CompLemmas
-- import Mathlib.NumberTheory.LegendreSymbol.ZModChar

-- open legendreSym Nat Int List ZMod

-- lemma pos_eq_natAbs {a : ℤ} (h : a ≥ 0) : a = a.natAbs := by
--   cases a
--   simp only [ofNat_eq_coe, natAbs_ofNat]
--   norm_cast at h

-- lemma legendre_neg_mul (p : ℕ) [hp : Fact p.Prime] (h : a ≤ 0)
--   : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
--     have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
--     nth_rewrite 1 [this]
--     have : -a = a.natAbs := by simpa using pos_eq_natAbs (Int.neg_nonneg_of_nonpos h)
--     rw [this]
--     exact legendreSym.mul p (-1) a.natAbs

-- lemma natAbs_legendre_eq_prod_factors (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (h : a ≠ 0)
--   : legendreSym p a.natAbs
--       = List.prod (a.natAbs.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp)):= by
--   nth_rewrite 1 [←  prod_factors (natAbs_ne_zero.mpr h)]
--   rw [Lean.Internal.coeM, @bind_pure_comp]
--   simp only [map_eq_map, pmap_eq_map, map_map]
--   induction factors (natAbs a)
--   case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
--   case cons _ _ c =>
--     simp only [map_cons, prod_cons, Function.comp_apply]
--     rw [←c, ←legendreSym.mul]
--     congr

-- def legendreSym_of_factors_list (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
--   map (fun a => legendreSym p a) a.natAbs.factors

-- def legendreSym_of_reciprocity_map (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
--   pmap (fun q hq =>
--           if q = 2 then χ₈ p
--           else
--             let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
--             (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) a.natAbs.factors (fun _ x => x)

-- variable {p : ℕ} [Fact p.Prime] in
-- lemma factors_list_eq_reciprocity_map (a : ℤ) (hp' : p ≠ 2)
--   : legendreSym_of_factors_list p a = legendreSym_of_reciprocity_map p a := by
--       apply List.ext
--       intros n
--       dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
--       simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
--       split
--       case a.h_1 _ _ _ _ o _ =>
--         simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
--           Option.map_eq_none', get?_eq_none]
--         simpa only [get?_eq_none] using o
--       case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
--         simp only [Option.map_eq_map, Option.map_eq_some']
--         use o₄
--         constructor
--         ·
--           simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_some']
--           exact ⟨o₄, ⟨o₆ ,rfl⟩⟩
--         ·
--           letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
--           split_ifs
--           case pos h => rw [h] ; exact legendreSym.at_two hp'
--           case neg h => exact quadratic_reciprocity' h hp'

-- def reciprocity_recursion (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : ℤ :=
--     if _ : a = 0 then 0
--     else if _ : p = 2 then legendreSym p (a % p)
--     else List.prod <|
--       pmap (fun q hq =>
--             if _ : q = 2 then χ₈ p
--             else
--               let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
--               (-1) ^ (q / 2 * (p / 2)) * reciprocity_recursion q (p % q)) a.factors (fun _ x => x)
-- termination_by
--   reciprocity_recursion p a => a
-- decreasing_by
--   simp_wf
--   exact Nat.lt_of_lt_of_le (mod_lt p Fin.size_pos') (le_of_mem_factors hq)

-- lemma reciprocity_recursion_eq_legendreSym (p : ℕ) [hp : Fact p.Prime] (a : ℕ) :
--   reciprocity_recursion p a = legendreSym p a := by
--     unfold reciprocity_recursion
--     split_ifs
--     case pos h => rw [h] ; simp
--     case pos => rw [← legendreSym.mod]
--     case neg h1 h2 =>
--       rw [pos_eq_natAbs ((ofNat_nonneg a)),
--         natAbs_legendre_eq_prod_factors p (a := (a : ℤ)) (ofNat_ne_zero.mpr h1)]
--       simp only [pmap_eq_map]
--       change _ = (legendreSym_of_factors_list p a).prod
--       rw [factors_list_eq_reciprocity_map, legendreSym_of_reciprocity_map]
--       congr ; ext x hx ; congr ; ext ; congr
--       letI : Fact x.Prime := ⟨prime_of_mem_factors hx⟩
--       rw [legendreSym.mod x]
--       exact reciprocity_recursion_eq_legendreSym x (p % x)
--       assumption
-- termination_by _ p hp a => a
-- decreasing_by
--   simp_wf
--   apply Nat.lt_of_lt_of_le (mod_lt p (pos_of_mem_factors hx)) (le_of_mem_factors hx)

-- def reciprocity_recursion' (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
--   if _ : p = 2 then legendreSym p (a % p)
--   else if _ : a < 0 then (χ₄ p) * (reciprocity_recursion p a.natAbs)
--   else (reciprocity_recursion p a.natAbs)

-- @[csimp]
-- lemma reciprocity_recursion_eq_legendreSym' :
--   @reciprocity_recursion' = @legendreSym := by
--     ext p hp a
--     dsimp only [reciprocity_recursion']
--     split_ifs
--     case pos => rw [← legendreSym.mod]
--     case pos h h' =>
--       rw [legendre_neg_mul p (Int.le_of_lt h'), at_neg_one h, reciprocity_recursion_eq_legendreSym]
--     case neg h =>
--       symm
--       nth_rewrite 1 [pos_eq_natAbs (Int.not_lt.mp h)]
--       rw [reciprocity_recursion_eq_legendreSym]

-- def legendre_reciprocity (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
--    if _ : a = 0 then 0
--    else if _ : p = 2 then legendreSym p (a % p)
--    else if _ : a > 0 then (legendreSym_of_reciprocity_map p a).prod
--    else (χ₄ p) * (legendreSym_of_reciprocity_map p a).prod

-- @[csimp]
-- theorem legendreSym_eq_legendre_reciprocity : @legendreSym = @legendre_reciprocity := by
--   ext p hp a
--   simp only [legendre_reciprocity]
--   split_ifs
--   case pos h => rw [h, at_zero]
--   case pos => exact legendreSym.mod p a
--   case pos h h' k =>
--     rw [←factors_list_eq_reciprocity_map,
--       pos_eq_natAbs (Int.nonneg_of_pos k), natAbs_legendre_eq_prod_factors p h, pmap_eq_map]
--     dsimp [legendreSym_of_factors_list]
--     assumption
--   case neg h h' k =>
--     simp only [gt_iff_lt, not_lt] at k
--     rw [←factors_list_eq_reciprocity_map, legendre_neg_mul p,
--       natAbs_legendre_eq_prod_factors, pmap_eq_map, legendreSym.at_neg_one h']
--     congr 1
--     assumption'

/-import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

open legendreSym Nat Int List ZMod

variable (p : ℕ) [hp : Fact p.Prime]

lemma pos_eq_natAbs {a : ℤ} (h : a > 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  norm_cast at h

lemma legendre_neg_mul (h : a ≤ 0) (k : a ≠ 0)
  : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
    have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
    nth_rewrite 1 [this]
    have : -a = a.natAbs := by simpa using (pos_eq_natAbs (Int.neg_pos_of_neg (Ne.lt_of_le k h)))
    rw [this]
    exact legendreSym.mul p (-1) a.natAbs

lemma natAbs_legendre_eq_prod_factors {a : ℤ} (h : a ≠ 0)
  : legendreSym p a.natAbs
      = List.prod (a.natAbs.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp)):= by
  nth_rewrite 1 [←  prod_factors (natAbs_ne_zero.mpr h)]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction factors (natAbs a)
  case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
  case cons _ _ c =>
    simp only [map_cons, prod_cons, Function.comp_apply]
    rw [←c, ←legendreSym.mul]
    congr

def legendreSym_of_factors_list (a : ℤ) : List ℤ :=
  map (fun a => legendreSym p a) a.natAbs.factors

def legendreSym_of_reciprocity_map (a : ℤ) : List ℤ :=
  pmap (fun q hq =>
          if q = 2 then χ₈ p
          else
            let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
            (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) a.natAbs.factors (fun _ x => x)

variable {p : ℕ} [Fact p.Prime] in
lemma factors_list_eq_reciprocity_map (hp' : p ≠ 2)
  : legendreSym_of_factors_list p a = legendreSym_of_reciprocity_map p a := by
      apply List.ext
      intros n
      dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
      simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
      split
      case a.h_1 _ _ _ _ o _ =>
        simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
          Option.map_eq_none', get?_eq_none]
        simpa only [get?_eq_none] using o
      case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
        simp only [Option.map_eq_map, Option.map_eq_some']
        use o₄
        constructor
        ·
          simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_some']
          exact ⟨o₄, ⟨o₆ ,rfl⟩⟩
        ·
          letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
          split_ifs
          case pos h => rw [h] ; exact legendreSym.at_two hp'
          case neg h => exact quadratic_reciprocity' h hp'

def legendre_reciprocity (a : ℤ) : ℤ :=
   if _ : a = 0 then 0
   else if _ : p = 2 then legendreSym p (a % p)
   else if _ : a > 0 then (legendreSym_of_reciprocity_map p a).prod
   else (χ₄ p) * (legendreSym_of_reciprocity_map p a).prod

@[csimp]
theorem legendreSym_eq_legendre_reciprocity : @legendreSym = @legendre_reciprocity := by
  ext p hp a
  simp only [legendre_reciprocity]
  split_ifs
  case pos h => rw [h, at_zero]
  case pos => exact legendreSym.mod p a
  case pos h h' k =>
    rw [←factors_list_eq_reciprocity_map h',
      pos_eq_natAbs k, natAbs_legendre_eq_prod_factors p h, pmap_eq_map]
    dsimp [legendreSym_of_factors_list]
  case neg h h' k =>
    simp only [gt_iff_lt, not_lt] at k
    rw [←factors_list_eq_reciprocity_map h', legendre_neg_mul p k h,
      natAbs_legendre_eq_prod_factors, pmap_eq_map, legendreSym.at_neg_one h']
    congr 1
    assumption


------

lemma list_prod_eq_int_pos {a : ℤ} (h: a > 0) : List.prod (factors (natAbs a)) = a := by
  nth_rewrite 2 [pos_eq_natAbs h]
  norm_cast
  apply prod_factors
  simp only [ne_eq, natAbs_eq_zero]
  exact Int.ne_of_gt h

lemma legendre_factorization_pos {a : ℤ} (h : a > 0) : legendreSym p a = legendreSym p (List.prod (factors a.natAbs)) := by
  have := list_prod_eq_int_pos h
  norm_cast at this
  nth_rewrite 1 [←this]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  rfl

lemma natAbs_legendre_eq_prod_factors' {a : ℕ} (h : a ≠ 0)
  : legendreSym p a
      = List.prod (a.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp)):= by
  nth_rewrite 1 [←  prod_factors h]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction factors (natAbs a)
  case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
  case cons _ _ c =>
    simp only [map_cons, prod_cons, Function.comp_apply]
    rw [←c, ←legendreSym.mul]
    congr

def legendreSym_of_reciprocity_map' (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : List ℤ :=
  pmap (fun q hq =>
          if _ : q = 2 then χ₈ p
          else
            let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
            (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) a.factors (fun _ x => x)

-- mutual
-- lemma asdf (p : ℕ) [hp : Fact p.Prime] (a : ℕ)
--   : reciprocity_recursion_aux p a = legendreSym_of_reciprocity_map' p a := by {
--       unfold reciprocity_recursion_aux legendreSym_of_reciprocity_map'
--       apply List.ext
--       intros n
--       dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
--       simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
--       congr
--       funext pp ppp
--       congr
--       have : pp ∈ some pp := rfl
--       have asdff := ppp pp this
--       have asdfasdf : Fact (Nat.Prime pp) := ⟨ prime_of_mem_factors (ppp pp this)⟩
--       ext asdf
--       congr
--       rw [legendreSym.mod pp p]
--       rw [fa]
--       norm_cast
-- }
-- lemma fa (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : reciprocity_recursion p a = legendreSym p a := by {
--   unfold reciprocity_recursion
--   split_ifs
--   case pos h => rw [h] ; simp
--   case pos => rw [← legendreSym.mod]
--   case neg h1 h2 => {
--     change List.prod (reciprocity_recursion_aux p a) = _

--     rw [natAbs_legendre_eq_prod_factors' p h1]
--     have : map (fun a => legendreSym p a) a.factors = legendreSym_of_reciprocity_map' p a := sorry
--     simp
--     rw [this]
--     have : List.prod (legendreSym_of_reciprocity_map' p a) = legendreSym p a := sorry
--     rw [this]
--     rw [asdf]
--     sorry
--   }
-- }


-- end
-- termination_by
--   asdf p hp a => a
--   fa p hp a => p
-- decreasing_by {
--   simp_wf

--   sorry
-- }

def reciprocity_recursion (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : ℤ :=
    if _ : a = 0 then 0
    else if _ : p = 2 then legendreSym p (a % p)
    else List.prod <|
      pmap (fun q hq =>
            if _ : q = 2 then χ₈ p
            else
              let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
              (-1) ^ (q / 2 * (p / 2)) * reciprocity_recursion q (p % q)) a.factors (fun _ x => x)
termination_by
  reciprocity_recursion p a => a
decreasing_by
  simp_wf
  exact Nat.lt_of_lt_of_le (mod_lt p Fin.size_pos') (le_of_mem_factors hq)

lemma fyck (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (h : a ≠ 0) : List.prod (
    pmap (fun q hq =>
      if _ : q = 2 then χ₈ p
      else
        let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
        (-1) ^ (q / 2 * (p / 2)) * reciprocity_recursion q (p % q)) a.factors (fun _ x => x)) = legendreSym p a
:= by {
  rw [natAbs_legendre_eq_prod_factors' p h]
  simp only [pmap_eq_map]
  have : map (fun a => legendreSym p a) a.factors = legendreSym_of_reciprocity_map' p a := sorry
  rw [this]
  dsimp only [legendreSym_of_reciprocity_map']
  congr
  funext pp ppp
  congr
  funext hh
  congr
  have : Fact pp.Prime := ⟨prime_of_mem_factors ppp ⟩
  rw [legendreSym.mod pp]
  norm_cast
  unfold reciprocity_recursion
  split_ifs
  case pos h => rw [h] ; simp

  case neg h1 h2 h3 h4 => {
    rw [fyck pp (p % pp) h4]

  }
}
termination_by fyck p hp a h => a
decreasing_by
  simp_wf
  exact Nat.lt_of_lt_of_le (mod_lt p Fin.size_pos') (le_of_mem_factors ppp)
-/

/-import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

open legendreSym Nat Int List ZMod

lemma pos_eq_natAbs {a : ℤ} (h : a > 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  norm_cast at h

lemma neg_mul_eq_natAbs {a : ℤ} (h : a < 0) : -a = a.natAbs := by
  have := pos_eq_natAbs (Int.neg_pos_of_neg h)
  norm_cast at this
  simp at this
  norm_cast

lemma list_prod_eq_int_pos {a : ℤ} (h: a > 0) : List.prod (factors (natAbs a)) = a := by
  nth_rewrite 2 [pos_eq_natAbs h]
  norm_cast
  apply prod_factors
  simp only [ne_eq, natAbs_eq_zero]
  exact Int.ne_of_gt h

lemma list_prod_eq_int_neg {a : ℤ} (h: a < 0) : List.prod (factors (natAbs a)) = -a := by
  have : natAbs a = natAbs (-a) := by simp
  rw [this]
  have aa := pos_eq_natAbs (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  apply list_prod_eq_int_pos
  simp only [gt_iff_lt, Left.neg_pos_iff]
  assumption

lemma list_prod_eq_int_neg' (h : a < 0) : (-1) * List.prod (factors (natAbs a)) = a := by
  rw [list_prod_eq_int_neg]
  simp only [mul_neg, neg_mul, one_mul, neg_neg]
  assumption

lemma pos_int_is_nat {a : ℤ} (h : a > 0) : a.toNat = a := toNat_of_nonneg (Int.nonneg_of_pos h)

variable (p : ℕ) [hp : Fact p.Prime] (a : ℤ)

lemma legendre_neg_mul : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (-a)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  exact legendreSym.mul p (-1) (-a)

lemma legendre_neg_mul' {a : ℤ} (h : a < 0) : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  have : natAbs a = natAbs (-a) := by simp
  have aa := pos_eq_natAbs (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  rw [this]
  apply legendreSym.mul

lemma legendre_factorization_pos {a : ℤ} (h : a > 0) : legendreSym p a = legendreSym p (List.prod (factors a.natAbs)) := by
  have := list_prod_eq_int_pos h
  norm_cast at this
  nth_rewrite 1 [←this]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  rfl

lemma legendre_factorization_neg {a : ℤ} (h : a < 0)
  : legendreSym p a = (legendreSym p (-1)) * legendreSym p (List.prod (factors a.natAbs)) := by
    rw [legendre_neg_mul']
    congr 1
    · nth_rewrite 1 [legendre_factorization_pos]
      norm_cast ; norm_cast
      have := neg_mul_eq_natAbs h
      have h' : -a > 0 := by exact Int.neg_pos_of_neg h
      rw [this] at h'
      norm_cast at h'
    · assumption

lemma factorization_eq_prod_factorization_pos (p : ℕ) [hp: Fact p.Prime] (a : ℤ) (h : a > 0) : (legendreSym p a) = List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp  q) (fun _ _ => hp) ):= by
  rw [legendre_factorization_pos, Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction (factors (natAbs a))
  case nil => simp only [map_nil, prod_nil, at_one]
  case cons => simp only [map_cons, prod_cons, Function.comp_apply, legendreSym.mul] ; congr 1
  assumption

lemma factorization_eq_prod_factorization_neg (p : ℕ) [hp: Fact p.Prime] (a : ℤ) (h : a < 0) : (legendreSym p a) = (legendreSym p (-1)) * List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp q) (fun _ _ => hp) ):= by
  rw [legendre_neg_mul]
  congr 1
  rw [neg_mul_eq_natAbs]
  case e_a =>
    have hh := factorization_eq_prod_factorization_pos p (a.natAbs) (by simp ; exact Int.ne_of_lt h)
    rw [hh]
    norm_cast
  assumption

lemma legendre_eq_natAbs (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (h : a > 0)
  : legendreSym p a = legendreSym p a.natAbs := by rw [← pos_eq_natAbs h]

lemma legendre_neg_mul2 (p : ℕ) [hp : Fact p.Prime] (h : a ≤ 0) (k : a ≠ 0)
  : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
    have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
    nth_rewrite 1 [this]
    have : -a = a.natAbs := by simpa using (pos_eq_natAbs (Int.neg_pos_of_neg (Ne.lt_of_le k h)))
    rw [this]
    exact legendreSym.mul p (-1) a.natAbs

lemma natAbs_legendre_eq_prod_factors (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (h : a ≠ 0)
  : legendreSym p a.natAbs
      = List.prod (a.natAbs.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp)):= by
  nth_rewrite 1 [←  prod_factors (natAbs_ne_zero.mpr h)]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction factors (natAbs a)
  case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
  case cons _ _ c =>
    simp only [map_cons, prod_cons, Function.comp_apply]
    rw [←c, ←legendreSym.mul]
    congr

def legendreSym_of_factors_list (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
  map (fun a => legendreSym p a) a.natAbs.factors

def reciprocity_recursion (p : ℕ) [hp : Fact p.Prime] (q : ℕ) [hq : Fact q.Prime] : ℤ :=
  if _ : p = q then 0
  else if _ : (q % p) = 2 then χ₈ p
  else if _ : q = 2 then χ₈ p
  else if _ : p = 2 then legendreSym p (q % p)
  else
    (-1)^((p/2)*(q/2)) *
      ((p % q).factors.pmap (fun a ha =>
        let _ : Fact a.Prime := ⟨prime_of_mem_factors ha⟩
        have : a < q := Nat.lt_of_le_of_lt (le_of_mem_factors ha) (mod_lt p <| Fin.size_pos' (n := q))
        @reciprocity_recursion q _ a _) (fun _ hx => hx)).prod

def legendreSym_of_reciprocity_map (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
  pmap (fun q hq =>
          let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
          reciprocity_recursion p q)
        a.natAbs.factors (fun _ x => x)

def legendre_recursion_list (p : ℕ ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] : List ℤ := pmap
      (fun a ha =>
        let _ : Fact (Nat.Prime a) := ⟨prime_of_mem_factors ha⟩
        have : a < q := Nat.lt_of_le_of_lt (le_of_mem_factors ha) (mod_lt p <| Fin.size_pos' (n := q))
        reciprocity_recursion q a)
      (factors (p % q)) (fun _ hx => hx)

lemma reciprocity_map_eq_recursion_list (p : ℕ ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
  : legendreSym_of_factors_list q (p % q) = legendre_recursion_list p q := by {
    dsimp only [legendre_recursion_list, legendreSym_of_factors_list]
    apply List.ext
    intros n
    simp
    simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
    split
    case a.h_1 o₁ o₂ o₃ o₄ o₅ o₆ o₇ => {
      simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
          Option.map_eq_none', get?_eq_none]
      simpa only [get?_eq_none] using o₆
    }
    case a.h_2 o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ => {
      simp only [Option.map_eq_map, Option.map_eq_some']
      use o₆
      constructor
      case h.left => {
        simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_some']
        exact ⟨o₆, ⟨o₈ ,rfl⟩⟩
      }
      case h.right => {
          letI : Fact (Nat.Prime o₆) := ⟨prime_of_mem_factors (o₇ o₆ rfl)⟩
          dsimp only [reciprocity_recursion, reciprocity_recursion._unary]
          dsimp only [WellFounded.fix, WellFounded.fixF]

          sorry
      }
    }
  }

lemma legendreSym_eq_reciprocity_recursion (p : ℕ ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] :
  legendreSym p q = reciprocity_recursion p q := by {
    unfold reciprocity_recursion
    split_ifs
    case pos h => rw [← h, legendreSym.mod p p, EuclideanDomain.mod_self, at_zero]
    case pos h =>
      rw [legendreSym.mod p q, ←at_two]
      have : (2 : ℤ) = (2 : ℕ) := rfl
      rw [this, ← h]
      rfl
      have this : 2 < p := by
        rw [←h]
        apply mod_lt q (Fin.size_pos' (n := p))
      exact Nat.ne_of_gt this
    case pos h h' h'' =>
      have this : q = (2 : ℤ) := congrArg Nat.cast h''
      rw [this, at_two]
      rw [h''] at h
      assumption
    case pos => exact legendreSym.mod p ↑q
    case neg a b c d e f => {
      rw [quadratic_reciprocity' e f]
      congr 1
      rw [mul_comm]
      have : (p ) > 0 := by {
        exact Fin.size_pos'
      }
      have asdfasdf : (p : ℤ ) > 0 := by exact ofNat_pos.mpr this
      rw [legendre_eq_natAbs q asdfasdf]
      have : p ≠ 0 := by exact Nat.pos_iff_ne_zero.mp this
      have : (p : ℤ ) ≠ 0 := by exact ofNat_ne_zero.mpr this
      rw [natAbs_legendre_eq_prod_factors q this]

      have :=reciprocity_map_eq_recursion_list p q
      dsimp only [legendre_recursion_list] at this
      simp
      rw [← this]
      dsimp only [legendreSym_of_factors_list]
      sorry
    }
  }

variable {p : ℕ} [Fact p.Prime] in
lemma factors_list_eq_reciprocity_map (a : ℤ)
  : legendreSym_of_factors_list p a = legendreSym_of_reciprocity_map p a := by
      apply List.ext
      intros n
      dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
      simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
      split
      case a.h_1 _ _ _ _ o _ =>
        simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
          Option.map_eq_none', get?_eq_none]
        simpa only [get?_eq_none] using o
      case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
        simp only [Option.map_eq_map, Option.map_eq_some']
        use o₄
        constructor
        ·
          simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_some']
          exact ⟨o₄, ⟨o₆ ,rfl⟩⟩
        · {
          letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
          exact legendreSym_eq_reciprocity_recursion p o₄
        }

def legendre_reciprocity (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
   if _ : a = 0 then 0
   else
      if _ : p = 2 then legendreSym p (a % p)
      else
        if _ : a > 0 then (legendreSym_of_reciprocity_map p a).prod
        else (χ₄ p) * (legendreSym_of_reciprocity_map p a).prod

@[csimp]
theorem legendreSym_eq_legendre_reciprocity : @legendreSym = @legendre_reciprocity := by
  ext p hp a
  simp only [legendre_reciprocity]
  split_ifs
  case pos h => rw [h, at_zero]
  case pos => exact legendreSym.mod p a
  case pos h h' k =>
    rw [←factors_list_eq_reciprocity_map a,
      pos_eq_natAbs k, natAbs_legendre_eq_prod_factors p h, pmap_eq_map]
    dsimp [legendreSym_of_factors_list]
  case neg h h' k =>
    simp only [gt_iff_lt, not_lt] at k
    rw [←factors_list_eq_reciprocity_map a, legendre_neg_mul2,
      natAbs_legendre_eq_prod_factors, pmap_eq_map, legendreSym.at_neg_one h']
    congr 1
    assumption'
-/
