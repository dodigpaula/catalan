import Mathlib
open Nat

inductive bin_tree : Type
| leaf
| succ : bin_tree -> bin_tree
| node : (T1 T2 : bin_tree) -> bin_tree

-- Large task 5 : Rotating isomorphism

inductive plane_tree : Type
| join : (T : List plane_tree) -> plane_tree

inductive full_bin_tree : Type
| leaf
| join : (T1 T2 : full_bin_tree) -> full_bin_tree


-- We define the tree_rotation and its inverse then use both to prove bijection
mutual
def tree_rotation (T : full_bin_tree) : plane_tree := plane_tree.join (rotation_list T)

def rotation_list : full_bin_tree -> List plane_tree
  | full_bin_tree.leaf => [] -- Empty list is used to represent a leaf as a full binary tree always ends in a leaf on the rightmost path
  | full_bin_tree.join T1 T2 => (tree_rotation T1) :: (rotation_list T2)
end

mutual
def rotation_inv : plane_tree -> full_bin_tree
  | plane_tree.join [] => full_bin_tree.leaf
  | plane_tree.join (T1 :: L) => full_bin_tree.join (rotation_inv T1) (rotation_inv_list L)

def rotation_inv_list : List plane_tree -> full_bin_tree
  | [] => full_bin_tree.leaf
  | T1 :: L => full_bin_tree.join (rotation_inv T1) (rotation_inv_list L)
end

def injective (f : X → Y) : Prop :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

def surjective (f : X → Y) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : X → Y) := injective f ∧ surjective f

def full_bin_tree.size : full_bin_tree -> Nat
| full_bin_tree.leaf => 1
| full_bin_tree.join T1 T2 => T1.size + T2.size + 1

def plane_tree.leaf_num : plane_tree -> Nat
| plane_tree.join [] => 1
| plane_tree.join (T :: L) => T.leaf_num + (plane_tree.join L).leaf_num

def plane_tree.size : plane_tree -> Nat
| plane_tree.join [] => 2
| plane_tree.join (T :: L) => T.size + (plane_tree.join L).size

def size_eq : T.size + 1 = (tree_rotation T).size ∧ T.size + 1 = plane_tree.size (plane_tree.join (rotation_list T)) := by
  match T with
  | full_bin_tree.leaf => rw [tree_rotation, full_bin_tree.size, rotation_list, plane_tree.size]
                          simp
  | full_bin_tree.join T1 T2 => rw [tree_rotation, rotation_list, plane_tree.size]
                                have t1 : full_bin_tree.size T1 + 1 = plane_tree.size (tree_rotation T1) := And.left size_eq
                                have t2 : T2.size + 1 = plane_tree.size (plane_tree.join (rotation_list T2)) := And.right size_eq
                                rw [<- t1, full_bin_tree.size, <- t2]
                                simp
                                rw [Nat.add_comm, <- Nat.add_assoc, Nat.add_comm, Nat.add_comm (full_bin_tree.size T1)]
                                have t3 : full_bin_tree.size T2 + 1 = plane_tree.size (tree_rotation T2) := And.left size_eq
                                rw [t1, t3, <- Nat.add_assoc, Nat.add_comm, <- Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_comm, <- Nat.add_assoc, t1, Nat.add_assoc, Nat.add_comm 1, t3]

-- We show (rotation_inv (tree_rotation T) = T) with structural induction
theorem inv_rot_ind (T : full_bin_tree) : rotation_inv (tree_rotation T) = T ∧ rotation_inv_list (rotation_list T) = T := by
  rw [tree_rotation]
  apply And.intro
  case left =>
    match T with
    | full_bin_tree.leaf => rw [rotation_list, rotation_inv]
    | full_bin_tree.join T1 T2 => rw [rotation_list, rotation_inv]
                                  have t : (rotation_inv (tree_rotation T1)) = T1 := And.left (inv_rot_ind T1)
                                  rw [t]
                                  match T2 with
                                  | full_bin_tree.leaf => rw [rotation_list, rotation_inv_list]
                                  | full_bin_tree.join T11 T12 => rw [rotation_list, rotation_inv_list]
                                                                  have t1 : rotation_inv (tree_rotation T11) = T11 := And.left (inv_rot_ind T11)
                                                                  have t2 : rotation_inv_list (rotation_list T12) = T12 :=  And.right (inv_rot_ind T12)
                                                                  rw [t1, t2]
  case right =>
    match T with
    | full_bin_tree.leaf => rw [rotation_list, rotation_inv_list]
    | full_bin_tree.join T1 T2 => rw [rotation_list, rotation_inv_list]
                                  have t : (rotation_inv (tree_rotation T1)) = T1 := And.left (inv_rot_ind T1)
                                  rw [t]
                                  have t2 : rotation_inv_list (rotation_list T2) = T2 :=  And.right (inv_rot_ind T2)
                                  rw [t2]

theorem inv_rot (T : full_bin_tree) : rotation_inv (tree_rotation T) = T := And.left (inv_rot_ind T)

theorem inv_sur (T : full_bin_tree) : T = full_bin_tree.leaf ∨ ∃ R, ∃ L, T = rotation_inv (plane_tree.join (R :: L)) := by
match T with
  | full_bin_tree.leaf => simp
  | full_bin_tree.join T1 T2 => simp
                                have r : (rotation_inv_list (rotation_list T2)) = T2 := (And.right (inv_rot_ind T2))
                                have t : rotation_inv (tree_rotation T1) = T1 := (And.left (inv_rot_ind T1))
                                have x : rotation_inv (plane_tree.join ((tree_rotation T1) :: (rotation_list T2))) = full_bin_tree.join T1 T2 := by
                                  rw [rotation_inv, t, r]
                                rw [<- x]
                                apply Exists.intro
                                apply Exists.intro
                                trivial

-- Wasn't used
theorem rot_inv_list_ind : (∀ (R : plane_tree), R ∈ L1::L2 -> tree_rotation (rotation_inv R) = R) -> (∀ (R : plane_tree), R ∈ L2 -> tree_rotation (rotation_inv R) = R) := by
  intro h
  simp at h
  exact And.right h

-- Wasn't used
theorem rot_inv_implies_rot_inv_list : (∀ (R : plane_tree), R ∈ L -> tree_rotation (rotation_inv R) = R) -> rotation_list (rotation_inv_list L) = L := by
  intro h
  match L with
  | [] => rw [rotation_inv_list, rotation_list]
  | L1 :: L2 => have t : L1 ∈ L1 :: L2 := by simp
                have r : tree_rotation (rotation_inv L1) = L1 := (h L1) t
                rw [rotation_inv_list, rotation_list, r]
                simp at h
                have y : ∀ (R : plane_tree), R ∈ L2 → tree_rotation (rotation_inv R) = R := And.right h
                have z : rotation_list (rotation_inv_list L2) = L2 := rot_inv_implies_rot_inv_list y
                rw [z]

def zero_lt_gen_leaf_num (T : plane_tree): 0 < T.leaf_num := by
  match T with
  | plane_tree.join [] => rw [plane_tree.leaf_num]
                          exact Nat.zero_lt_one
  | plane_tree.join (T :: L) => rw [plane_tree.leaf_num]
                                have t1 : 0 < plane_tree.leaf_num T := zero_lt_gen_leaf_num T
                                have t2 : 0 < plane_tree.leaf_num (plane_tree.join L) := zero_lt_gen_leaf_num (plane_tree.join L)
                                rw [<- Nat.add_zero 0]
                                exact Nat.add_lt_add t1 t2

def one_le_gen_leaf_num (T : plane_tree): 1 ≤ T.leaf_num := (Nat.succ_le_of_lt (zero_lt_gen_leaf_num T))

-- We show (tree_rotation (rotation_inv T) = T) with induction on number of leaves
theorem rot_inv_ind (n : Nat) : ∀ ⦃R L⦄, (plane_tree.join (R :: L)).leaf_num ≤ n + 1 -> tree_rotation (rotation_inv (plane_tree.join (R :: L))) = (plane_tree.join (R :: L)) ∧ tree_rotation (rotation_inv R) = R ∧ (rotation_list (rotation_inv_list L) = L) := by
  induction n with
  | zero => intro R L
            intro h
            simp at h
            rw [plane_tree.leaf_num] at h
            have t : 1 + 1 ≤ plane_tree.leaf_num R + plane_tree.leaf_num (plane_tree.join L) := Nat.add_le_add (one_le_gen_leaf_num R) (one_le_gen_leaf_num (plane_tree.join L))
            have r : 1 + 1 ≤ 1 := by exact Nat.le_trans t h
            contradiction
  | succ k h => intro T1 T2
                intro r
                match T1 with
                | plane_tree.join [] => rw [rotation_inv, tree_rotation, rotation_inv, rotation_list, rotation_inv, tree_rotation, rotation_list]
                                        simp
                                        match T2 with
                                        | [] => rw [rotation_inv_list, rotation_list]
                                        | R1 :: L1 => rw [rotation_inv_list, rotation_list]
                                                      rw [plane_tree.leaf_num, plane_tree.leaf_num, plane_tree.leaf_num, Nat.succ_eq_add_one, Nat.add_comm] at r
                                                      have t : plane_tree.leaf_num (plane_tree.join (R1 :: L1)) ≤ k + 1 := by
                                                        rw [plane_tree.leaf_num]
                                                        exact Nat.le_of_add_le_add_right r
                                                      have x : tree_rotation (rotation_inv (plane_tree.join (R1 :: L1))) = plane_tree.join (R1 :: L1) ∧ tree_rotation (rotation_inv R1) = R1 ∧  rotation_list (rotation_inv_list L1) = L1 := h t
                                                      rw [(And.left (And.right x))]
                                                      rw [(And.right (And.right x))]
                | plane_tree.join (R :: L) => rw [rotation_inv, tree_rotation, rotation_list]
                                              rw [plane_tree.leaf_num, plane_tree.leaf_num] at r
                                              simp
                                              have help2 : ∀ ⦃a b k⦄, 1 ≤ b -> a + b ≤ k + 1 -> a ≤ k := by
                                                intro a b k
                                                intro h1 h2
                                                have t : a + 1 ≤ a + b := by rw [Nat.add_le_add_iff_left]
                                                                             exact h1
                                                have t : a + 1 ≤ k + 1 := Nat.le_trans t h2
                                                rw [Nat.add_le_add_iff_right] at t
                                                exact t
                                              have t : plane_tree.leaf_num (plane_tree.join (R :: L)) ≤ k + 1 := by
                                                rw [plane_tree.leaf_num]
                                                have t1 : plane_tree.leaf_num R + plane_tree.leaf_num (plane_tree.join L) ≤ succ k := help2 (one_le_gen_leaf_num (plane_tree.join T2)) r
                                                exact t1
                                              have x : tree_rotation (rotation_inv (plane_tree.join (R :: L))) = plane_tree.join (R :: L) := And.left (h t)
                                              rw [x]
                                              simp
                                              have t : plane_tree.leaf_num (plane_tree.join (plane_tree.join [] :: T2)) ≤ succ k := by
                                                rw [plane_tree.leaf_num, plane_tree.leaf_num]
                                                have x : 1 + 1 ≤ plane_tree.leaf_num R + plane_tree.leaf_num (plane_tree.join L) := Nat.add_le_add (one_le_gen_leaf_num R) (one_le_gen_leaf_num (plane_tree.join L))
                                                have y : 1 + 1 + plane_tree.leaf_num (plane_tree.join T2) ≤ plane_tree.leaf_num R + plane_tree.leaf_num (plane_tree.join L) + plane_tree.leaf_num (plane_tree.join T2) := Nat.add_le_add x (Nat.le_refl (plane_tree.leaf_num (plane_tree.join T2)))
                                                have z : 1 + 1 + plane_tree.leaf_num (plane_tree.join T2) ≤ succ k + 1 := Nat.le_trans y r
                                                rw [Nat.add_comm, Nat.add_le_add_iff_right] at z
                                                have w : succ (plane_tree.leaf_num (plane_tree.join T2)) ≤ succ k := (Nat.succ_le_succ z)
                                                rw [Nat.succ_eq_add_one, Nat.add_comm] at w
                                                exact w
                                              have x : rotation_list (rotation_inv_list T2) = T2 := And.right (And.right (h t))
                                              exact x

theorem rot_inv (T : plane_tree) : (tree_rotation (rotation_inv T)) = T := by
  match T with
  | plane_tree.join [] => rw [rotation_inv, tree_rotation, rotation_list]
  | plane_tree.join (R :: L) => have x : plane_tree.leaf_num (plane_tree.join (R :: L)) ≤ plane_tree.leaf_num (plane_tree.join (R :: L)) + 1 := Nat.le_add_right (plane_tree.leaf_num (plane_tree.join (R :: L))) 1
                                have t : tree_rotation (rotation_inv (plane_tree.join (R :: L))) = (plane_tree.join (R :: L)) ∧ tree_rotation (rotation_inv R) = R ∧ (rotation_list (rotation_inv_list L) = L) := rot_inv_ind ((plane_tree.join (R :: L)).leaf_num) x
                                exact And.left t

theorem rot_inv_list (L : List plane_tree) : rotation_list (rotation_inv_list L) = L := by
  have x : plane_tree.leaf_num (plane_tree.join (plane_tree.join [] :: L)) ≤ plane_tree.leaf_num (plane_tree.join (plane_tree.join [] :: L)) + 1 := Nat.le_add_right (plane_tree.leaf_num (plane_tree.join (plane_tree.join [] :: L))) 1
  have t : tree_rotation (rotation_inv (plane_tree.join (plane_tree.join [] :: L))) = (plane_tree.join (plane_tree.join [] :: L)) ∧ tree_rotation (rotation_inv (plane_tree.join [])) = plane_tree.join [] ∧ (rotation_list (rotation_inv_list L) = L) := rot_inv_ind ((plane_tree.join (plane_tree.join [] :: L)).leaf_num) x
  exact And.right (And.right t)

theorem inv_rot_list (T : full_bin_tree) : rotation_inv_list (rotation_list T) = T := And.right (inv_rot_ind T)

theorem tree_rotation_injective : injective tree_rotation := by
  unfold injective
  intro x y
  intro h
  match x, y with
  | full_bin_tree.leaf, full_bin_tree.leaf => simp
  | full_bin_tree.leaf, full_bin_tree.join T1 T2 => rw [tree_rotation, rotation_list, tree_rotation, rotation_list] at h
                                                    simp at h
  | full_bin_tree.join T1 T2, full_bin_tree.leaf => rw [tree_rotation, rotation_list, tree_rotation, tree_rotation, rotation_list] at h
                                                    simp at h
  | full_bin_tree.join L1 L2, full_bin_tree.join R1 R2 => have t : ∃ R, ∃ L, full_bin_tree.join L1 L2 = rotation_inv (plane_tree.join (R :: L)) := by
                                                            have t : full_bin_tree.join L1 L2 = full_bin_tree.leaf ∨ ∃ R, ∃ L, full_bin_tree.join L1 L2 = rotation_inv (plane_tree.join (R :: L)) := inv_sur (full_bin_tree.join L1 L2)
                                                            simp at t
                                                            exact t
                                                          match t with
                                                          | ⟨R, L, t⟩ => rw [t] at h
                                                                         rw [(rot_inv (plane_tree.join (R :: L)))] at h
                                                                         rw [h] at t
                                                                         rw [inv_rot] at t
                                                                         exact t

theorem rotation_surjective : surjective tree_rotation := by
  unfold surjective
  intro y
  match y with
  | plane_tree.join [] => have t : tree_rotation (full_bin_tree.leaf) = plane_tree.join [] := by
                            rw [tree_rotation, rotation_list]
                          apply Exists.intro
                          trivial
  | plane_tree.join (R :: L) => have t : tree_rotation (rotation_inv (plane_tree.join (R :: L))) = plane_tree.join (R :: L) := rot_inv (plane_tree.join (R :: L))
                                apply Exists.intro
                                trivial

theorem rotation_bijective : bijective tree_rotation := by
  unfold bijective
  exact And.intro tree_rotation_injective rotation_surjective

-------------------------------------------------------------------------
-- Large task 6 : n + 1 divides choose 2n n


-- Used to do proof
def fac : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem one_le_fac (n : Nat) : 1 ≤ fac n := by
  induction n with
  | zero => rw [Nat.zero_eq, fac]
  | succ m md => rw [fac]
                 have r : m + 1 > 0 := by
                  exact Nat.zero_lt_succ m
                 apply Nat.mul_le_mul r md

theorem zero_lt_fac (n : Nat) : 0 < fac n := by
  induction n with
  | zero => rw [Nat.zero_eq, fac]
            exact Nat.le_refl 1
  | succ m md => rw [fac]
                 have r : m + 1 > 0 := by
                  exact Nat.zero_lt_succ m
                 apply Nat.mul_le_mul r md

theorem le_fac (n : Nat) : n ≤ fac n := by
  match n with
  | 0 => rw [fac]
         exact Nat.zero_le 1
  | m + 1 =>  rw [<- Nat.succ_eq_add_one, Nat.succ_eq_add_one, fac]
              have r : m + 1 ≤ m + 1 := by
                exact Nat.le_refl (m + 1)
              have rr : 1 * fac m = fac m := by
                rw [Nat.one_mul]
              rw [<- Nat.one_mul (m + 1)]
              rw [<- Nat.mul_comm (m + 1)]
              rw [Nat.mul_assoc, rr]
              apply Nat.mul_le_mul r (one_le_fac m)

theorem choose_ge_eq_zero (n k : Nat) : (n < k) -> choose n k = 0 := by
intro r
induction n with
| zero => rw [Nat.zero_eq]
          match k with
          | zero => rw [Nat.zero_eq]
                    contradiction
          | succ m => rw [choose]
| succ m h => match k with
              | 0 => contradiction
              | x + 1 => rw [<- Nat.succ_eq_add_one, choose]
                         have t1 : m < x := (Nat.le_of_succ_le_succ r)
                         have t2 : m < succ x := Nat.le_succ_of_le t1
                         have t3 : choose m (succ x) = 0 := h t2
                         rw [t3]
                         simp
                         rw [choose_ge_eq_zero]
                         exact t1

theorem choose_self_eq_one (n : Nat) : choose n n = 1 := by
  match n with
  | 0 => rw [choose]
  | n + 1 =>  rw [choose]
              have r : n < n + 1 := (Nat.lt_succ_of_le (Nat.le_refl n))
              have t : choose n (n + 1) = 0 := choose_ge_eq_zero n (n + 1) r
              rw [t, choose_self_eq_one]

theorem mul_cycle_four (a b c d : Nat) : a * b * c * d = d * a * b * c := by
  rw [Nat.mul_comm, <- Nat.mul_assoc]
  rw [<- Nat.mul_assoc]

theorem mul_cycle_three (a b c : Nat) : a * b * c = c * a * b := by
  rw [Nat.mul_comm, Nat.mul_assoc]

-- Factorial formula for binomial coefficients cross multiplied
theorem choose_eq_fac (n k : Nat) : (k ≤ n -> choose n k * fac k * fac (n - k) = fac n) := by
  intro l
  match n with
  | 0 => match k with
            | zero => rw [choose, fac]
            | succ k => contradiction
  | n + 1 =>  rw [<- Nat.succ_eq_add_one, <- Nat.add_one]
              match k with
              | 0 => rw [choose, fac, Nat.mul_one, Nat.one_mul]
                     rfl
              | k + 1 => have r : k ≤ n := Nat.le_of_succ_le_succ l
                         rw [Nat.le_iff_lt_or_eq] at r
                         cases r with
                         | inr t2 => rw [t2]
                                     rw [choose_self_eq_one (n + 1)]
                                     rw [Nat.sub_self, fac, Nat.mul_one, Nat.one_mul]
                         | inl t1 => rw [fac, Nat.mul_comm, <- Nat.mul_assoc, <- Nat.mul_assoc]
                                     simp
                                     rw [mul_cycle_four, mul_cycle_four]
                                     have mul_assoc_four (a b c d : Nat) : a * b * c * d = a * (b * c * d) := by
                                      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
                                     have mul_cycle_four_three (a b c d : Nat) : a * b * c * d = a * d * b * c := by
                                      rw [Nat.mul_assoc, Nat.mul_assoc]
                                      rw [Nat.mul_comm b, Nat.mul_assoc, Nat.mul_comm c, <- Nat.mul_assoc, <- Nat.mul_assoc]
                                     rw [mul_cycle_four_three, mul_assoc_four]
                                     rw [choose]
                                     rw [Nat.mul_comm, Nat.add_mul, Nat.add_mul, Nat.mul_comm]
                                     have r : k + 1 ≤ n := Nat.succ_le_of_lt t1
                                     rw [choose_eq_fac, Nat.add_comm (fac n), <- Nat.mul_comm (fac k)]
                                     rw [Nat.mul_add, <- Nat.mul_assoc, <- Nat.mul_assoc]
                                     have z : (k + 1) * fac k = fac (k + 1) := by rw [fac]
                                     rw [z, mul_cycle_three, <- Nat.add_one_sub_one (n - k), Nat.sub_add_comm, Nat.add_succ, fac]
                                     rw [Nat.add_comm] at r
                                     have t3 : 1 ≤ n - k := (Nat.le_sub_of_add_le r)
                                     rw [<- Nat.add_comm] at r
                                     have t2 : n - k - 1 + 1 = n - k := Nat.sub_add_cancel t3
                                     have mul_comm_three_two (a b c : Nat) : a * b * c = a * c * b := by
                                       rw [Nat.mul_assoc, Nat.mul_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_comm b]
                                     rw [t2, Nat.sub_sub, mul_cycle_four, mul_cycle_four, mul_cycle_four, mul_cycle_four, mul_assoc_four, mul_cycle_three, mul_comm_three_two, choose_eq_fac]
                                     rw [<- Nat.add_mul]
                                     rw [<- Nat.add_assoc, Nat.sub_add_cancel, fac]
                                     exact (Nat.le_of_succ_le_succ l)
                                     exact r
                                     rw [Nat.add_comm] at r
                                     exact (Nat.le_sub_of_add_le r)
                                     exact (Nat.le_of_succ_le_succ l)

-- Factorial formula for binomial coefficients
-- Wasn't used
theorem choose_eq_fac_div (n k : Nat) : k ≤ n -> fac n / ((fac k) * (fac (n - k))) = choose n k := by
  intro h
  apply Nat.div_eq_of_eq_mul_left
  have r : 0 < fac k := zero_lt_fac k
  have t : 0 < fac (n - k) := zero_lt_fac (n - k)
  exact (Nat.mul_lt_mul_of_lt_of_lt r t)
  rw [<- Nat.mul_assoc]
  have l : choose n k * fac k * fac (n - k) = fac n := (choose_eq_fac n k h)
  rw [l]

theorem div_intro_left (a b c : Nat) : a * b = c -> a ∣ c := by
  intro r
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [<- r, Nat.mul_comm, Nat.mul_mod_left]

theorem div_intro_right (a b c : Nat) : a * b = c -> b ∣ c := by
  intro r
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [<- r, Nat.mul_comm, Nat.mul_mod_right]

theorem bin_is_integer (n k : Nat) : (k ≤ n) -> fac k * fac (n - k) ∣ fac n := by
  intro h
  have t1 : choose n k * (fac k * fac (n - k)) = fac n := by rw [<- Nat.mul_assoc]
                                                             exact (choose_eq_fac n k h)
  exact (div_intro_right (choose n k) ((fac k * fac (n - k))) (fac n) t1)

-- Wasn't used
theorem choose_mul_dvd (n k : Nat) : (k ≤ n) -> choose (n + 1) (k + 1) = ((n + 1) * choose n k) / (k + 1) := by
  intro h
  have z : (k + 1) * fac k = fac (k + 1) := by rw [fac]
  have w : (n + 1) * fac n = fac (n + 1) := by rw [fac]
  have t : (n + 1) - (k + 1) = (n - k) := by simp
  have r : k + 1 ≤ n + 1 := Nat.succ_le_succ h
  rw [<- (choose_eq_fac_div n k h), <- Nat.mul_div_assoc, w, Nat.div_div_eq_div_mul, mul_cycle_three, z,<- t, <- (choose_eq_fac_div (n + 1) (k + 1) r)]
  exact (bin_is_integer n k h)

theorem fac_eq (n : Nat) : (n + 1) * fac n = fac (n + 1) := by rw [fac]

-- Wasn't used
theorem lemma1 (n : Nat) (z : 0 < n): n * fac (n + 1) * fac (2 * n - (n + 1)) * fac (2 * n) = (n + 1) * fac n * fac n * fac (2 * n) := by
  have h : 1 ≤ n := (Nat.lt_of_succ_le z)
  rw [Nat.mul_right_cancel_iff (zero_lt_fac (2 * n))]
  have r : (2 * n - (n + 1)) = (n - 1) := by
    rw [Nat.two_mul, Nat.add_sub_add_left]
  rw [r]
  have t : n * fac (n - 1) = fac n := by
    have t1 : ((n - 1) + 1) * fac (n - 1) = fac ((n - 1) + 1) := fac_eq (n - 1)
    rw [Nat.add_comm, <- Nat.add_sub_assoc, Nat.one_add_sub_one] at t1
    exact t1
    exact h
  rw [<- t, <- Nat.mul_assoc, <- Nat.mul_assoc]
  rw [Nat.mul_right_cancel_iff (zero_lt_fac (n - 1))]
  rw [Nat.mul_assoc (n + 1), t, (fac_eq n), Nat.mul_comm]

theorem lemma2 (h : 0 < n) : n * choose (2 * n) n = (n + 1) * choose (2 * n) (n + 1) := by
  have z : (n + 1) ≤ (2 * n) := by
    rw [Nat.two_mul]
    rw [Nat.add_le_add_iff_left]
    exact (Nat.lt_of_succ_le h)
  have w : n ≤ 2 * n := Nat.le_of_succ_le z
  rw [<- (Nat.mul_left_cancel_iff (zero_lt_fac n)), <- (Nat.mul_left_cancel_iff (zero_lt_fac n))]
  rw [<- Nat.mul_assoc, Nat.mul_comm, Nat.mul_assoc, <- Nat.mul_assoc (choose (2 * n) n)]
  have r : choose (2 * n) n * fac n * fac n = fac (2 * n) := by
    have r : choose (2 * n) n * fac n * fac n = choose (2 * n) n * fac n * fac (2 * n - n) := by rw [Nat.two_mul]
                                                                                                 simp
    rw [r]
    exact (choose_eq_fac (2 * n) n w)
  rw [r]
  have t : n * fac (n - 1) = fac n := by
    have t1 : ((n - 1) + 1) * fac (n - 1) = fac ((n - 1) + 1) := fac_eq (n - 1)
    rw [Nat.add_comm, <- Nat.add_sub_assoc, Nat.one_add_sub_one] at t1
    exact t1
    exact h
  rw [<- t]
  rw [Nat.mul_assoc]
  rw [(Nat.mul_left_cancel_iff h (fac (2 * n)))]
  rw [<- Nat.mul_assoc, <- Nat.mul_assoc, <- Nat.mul_assoc, Nat.mul_comm, Nat.mul_comm (fac (n - 1))]
  rw [t, Nat.mul_comm (fac n)]
  have x : fac (n - 1) * fac n * (n + 1) = fac (n - 1) * fac (n + 1) := by rw [fac]
                                                                           rw [Nat.mul_comm]
                                                                           rw [Nat.mul_comm (fac (n - 1))]
                                                                           rw [<- Nat.mul_assoc]
                                                                           rw [Nat.mul_comm]
  rw [x]
  rw [Nat.mul_comm (fac (n - 1) * fac (n + 1)), Nat.mul_comm (fac (n - 1)), <- Nat.mul_assoc]
  rw [Nat.mul_comm]
  have q : (2 * n - (n + 1)) = (n - 1) := by
    rw [Nat.two_mul, Nat.add_sub_add_left]
  rw [<- q]
  rw [choose_eq_fac (2 * n) (n + 1) z]

theorem succ_divides_choose_mul (n : Nat) :  (n + 1) * (choose (2 * n) n - choose (2 * n) (n + 1)) = choose (2 * n) n := by
  by_cases t : 0 < n
  rw [Nat.mul_sub_left_distrib]
  rw [<- (lemma2 t)]
  rw [Nat.add_comm]
  rw [Nat.add_mul]
  simp
  rw [Nat.not_lt_eq] at t
  have t : n = 0 := Nat.eq_zero_of_le_zero t
  rw [t]
  simp

theorem succ_divides_choose : (n + 1) ∣ choose (2 * n) n := div_intro_left (n + 1) (choose (2 * n) n - choose (2 * n) (n + 1)) (choose (2 * n) n) (succ_divides_choose_mul n)
