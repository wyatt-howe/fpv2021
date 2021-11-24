import ..lectures.love12_basic_mathematical_structures_demo
import data.int.gcd

/-! # LoVe Homework 7: Basic Mathematical Structures 

This homework covers Ch 12 of the HHG.

-/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Numbers and embeddings (5 points)

We start with some questions to get you used to the "numeral tactics".

Remember that:
* `norm_num` will simplify numeral expressions without variables. 
* `norm_cast` will simplify expressions with coercions.
* If you have an assumption `hx`, you can also `norm_cast at hx`.
* `exact_mod_cast h` is like `exact h`, except it will call `norm_cast` on `h` and the goal.


1.1 (1 point).
Use these tactics to solve the following problems.
-/

lemma num1 : 12345 < 67890 := 
by norm_num

lemma num2 {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 := 
by norm_num

lemma num3 (x : ℤ) (hx : (x : ℝ) < 25*100) : x < 25*100 := 
by exact_mod_cast hx

/-!
1.2 (1 point). For each of these statements, either prove it, or prove its negation. 
Think about why the statement (or its negation) is true!
-/

lemma num4 : ¬(7/3 > 2) :=
-- by norm_num
begin
  apply not_lt.mpr,
  have h_int_div : (7/3 : ℕ) = (2 : ℕ) := by refl,
  apply eq.ge, apply eq.symm,  -- case = of ≤ vs <
  apply h_int_div,
end

lemma num5 : ¬( 40 - (2*30) + 20 = 0 ) := 
-- by norm_num
begin
  intro hf,

  have ht : 40 - (2*30) + 20 = 20 := begin
    calc 40 - (2*30) + 20
        = 40 - 60 + 20 : by norm_num
    ... = 0 + 20 : by norm_num
    ... = 20 : by refl,
  end,

  have hz : 0 = 20 := begin
    have hi : 20 = 40 - (2*30) + 20 := begin
      exact eq.symm ht,
    end,
    apply eq.symm,
    rw hi,
    apply hf,
  end,
  have hnz : 0 ≠ 20 := by linarith,

  apply hnz,
  apply hz,
end

lemma num6 : 5 / (2 - 1 - 1) + 8 = 2 * 4 := 
-- by norm_num
begin
  let lhs := 5 / (2 - 1 - 1) + 8,
  have hlhs : lhs = 8 := by calc
          5 / (2 - 1 - 1) + 8
        = 5 / (1 - 1) + 8 : by norm_num
    ... = 5 / 0 + 8 : by norm_num
    ... = 0 + 8 : by norm_num
    ... = 8 : by refl,

  let rhs := 2 * 4,
  have hrhs : rhs = 8 := by calc
          2 * 4
        = 8 : by refl,
  
  have h : lhs = rhs := begin
    apply hlhs,
    -- apply hrhs,
  end,

  apply h,
end


/-!
1.3 (3 points). 


This seems like a very natural way to write the theorem
"If `a` and `b` are coprime, then there are coefficients `u` and `v` such that `u*a + v*b = 1`."
But I've made a mistake! What did I do wrong? Correct the statement of the theorem and prove it.

You'll probably find the lemmas `nat.gcd_eq_gcd_ab` and `nat.coprime.gcd_eq_one` helpful.
-/
#check nat.gcd_eq_gcd_ab
#check nat.coprime.gcd_eq_one

-- Coefficients cannot both be natural numbers                         ↓
lemma sum_eq_one_of_coprime (a b : ℕ) (h : nat.coprime a b) : ∃ (u v : ℤ), u*a + v*b = 1 :=
begin
  have bezout := nat.gcd_eq_gcd_ab,
  have gcd_eq_one := nat.coprime.gcd_eq_one,

  let u := nat.gcd_a a b,
  let v := nat.gcd_b a b,
  have hb : ↑(nat.gcd a b) = ↑a * u + ↑b * v := begin
    apply bezout,
  end,

  have hgcd : ↑(nat.gcd a b) = 1 := begin
    norm_cast,
    apply gcd_eq_one h,
  end,

  have hq : ↑a * u + ↑b * v = 1 := by linarith,
  have hi : u * ↑a + v * ↑b = 1 := by linarith,  -- commutivity

  apply exists.intro u,
  apply exists.intro v,
  apply hi,
end

/-! ## Question 2: algebraic lemmas and classes (7 points)

2.1. (2 points) State and prove a lemma that says: 
for any element `x` of an additive monoid, if `x` has a left inverse `y` 
and a right inverse `z`, then `y = z`. 
-/

-- your answer here
lemma add_monoid_trans_eq_inv {α : Type} [c : add_monoid α] :
  -- ∀x, (∃y, (y + x = c.zero) → (∃z, (x + z = c.zero) → (y = z))) :=
  -- ∀x, ∃y, ∃z, y+x=c.zero → x+z=c.zero → y=z :=
  ∀x, ∀y, ∀z, y+x=c.zero → x+z=c.zero → y=z :=
begin
  intro x,
  intros y z,
  intro linv,
  intro rinv,

  have h : y + x = x + z := by simp [linv, rinv],

  have hassoc : (y + x) + z = y + (x + z) := add_assoc y x z,

  have hl : (y + x) + z = c.zero + z := by simp [linv],

  have hr : y + (x + z) = y + c.zero := by simp [rinv],

  have hlr : c.zero + z = y + c.zero := begin
    apply (eq.congr hl hr).mp,
    apply hassoc,
  end,

  have hly : c.zero + z = y := begin
    simp [hlr],
    exact add_monoid.add_zero y,
  end,

  have hlz : c.zero + z = z := begin
    exact add_monoid.zero_add z,
  end,

  simp [hlz, ← hly],
end


/-!
2.2 (2 points). A `rng` (not a random number generator)
is an algebraic structure like a ring, but that does not require 
a multiplicative identity element.
<https://en.wikipedia.org/wiki/Rng_(algebra)>

Define a type class `rng` that represents the structure, in the style of 
the "monolithic group" from the Ch 12 demo. 
That is, your structure should not extend existing structures:
bundle all of the necessary axioms into your definition. 
-/

#check monolithic_group.group

@[class] structure rng (α : Type) : Type :=

-- (R, add) is an abelian group.
(add          : α → α → α)
(add_comm     : ∀a b, add a b = add b a)
(add_assoc    : ∀a b c, add (add a b) c = add a (add b c))

(zero         : α)
(zero_add     : ∀a, add zero a = a)
(add_zero     : ∀a, add a zero = a)

(inv          : α → α)
(add_inv      : ∀a, add (inv a) a = zero)

-- (R, mul) is a semigroup.
(mul          : α → α → α)
(mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c))

-- Multiplication distributes over addition.
(dist_left    : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(dist_right   : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

/-! 2.3 (2 points). Define an instance that shows that any `rng` is an `add_monoid`. -/

instance {α : Type} [rng α] : add_monoid α :=
begin
  tactic.unfreeze_local_instances,
  rename _inst_1 c,
  exact {
    -- Semigroup requirements
    add := c.add,
    add_assoc := c.add_assoc,

    -- Additional monoid requirements
    zero := c.zero,
    zero_add := c.zero_add,
    add_zero := c.add_zero,
  },
end

/-! 2.4 (1 point). Show that for any `α : Type`, the type of functions `α → α` is 
a monoid under the composition operator: `f * g = λ x, f (g x))` 
-/

instance (α : Type) : monoid (α → α) := 
begin
  exact {
    -- Semigroup requirements
    mul := λf, λg, λx, f (g x),
    mul_assoc := by norm_num,

    -- Additional monoid requirements
    one := λx, x,
    one_mul := by norm_num,
    mul_one := by norm_num,
  },
end

end LoVe