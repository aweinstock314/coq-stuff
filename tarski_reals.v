(*
https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Synthetic_approach

   The synthetic approach axiomatically defines the real number system as a complete ordered field. Precisely, this means the following. A model for the real number system consists of a set R, two distinct elements 0 and      
   1 of R, two binary operations + and × on R (called addition and multiplication, respectively), and a binary relation ≤ on R, satisfying the following properties.                                                              
    1. (R, +, ×) forms a field. In other words,                                                                                                                                                                                   
          + For all x, y, and z in R, x + (y + z) = (x + y) + z and x × (y × z) = (x × y) × z. (associativity of addition and multiplication)                                                                                     
          + For all x and y in R, x + y = y + x and x × y = y × x. (commutativity of addition and multiplication)                                                                                                                 
          + For all x, y, and z in R, x × (y + z) = (x × y) + (x × z). (distributivity of multiplication over addition)                                                                                                           
          + For all x in R, x + 0 = x. (existence of additive identity)                                                                                                                                                           
          + 0 is not equal to 1, and for all x in R, x × 1 = x. (existence of multiplicative identity)                                                                                                                            
          + For every x in R, there exists an element −x in R, such that x + (−x) = 0. (existence of additive inverses)                                                                                                           
          + For every x ≠ 0 in R, there exists an element x^−1 in R, such that x × x^−1 = 1. (existence of multiplicative inverses)                                                                                               
    2. (R, ≤) forms a totally ordered set. In other words,                                                                                                                                                                        
          + For all x in R, x ≤ x. (reflexivity)                                                                                                                                                                                  
          + For all x and y in R, if x ≤ y and y ≤ x, then x = y. (antisymmetry)                                                                                                                                                  
          + For all x, y, and z in R, if x ≤ y and y ≤ z, then x ≤ z. (transitivity)                                                                                                                                              
          + For all x and y in R, x ≤ y or y ≤ x. (totality)                                                                                                                                                                      
    3. The field operations + and × on R are compatible with the order ≤. In other words,                                                                                                                                         
          + For all x, y and z in R, if x ≤ y, then x + z ≤ y + z. (preservation of order under addition)                                                                                                                         
          + For all x and y in R, if 0 ≤ x and 0 ≤ y, then 0 ≤ x × y (preservation of order under multiplication)                                                                                                                 
    4. The order ≤ is complete in the following sense: every non-empty subset of R bounded above has a least upper bound. In other words,                                                                                         
          + If A is a non-empty subset of R, and if A has an upper bound, then A has a least upper bound u, such that for every upper bound v of A, u ≤ v.   
*)
Record Real : Type := {
    t : Type;
    zero : t; one : t;
    add : t -> t -> t;
    mul : t -> t -> t;
    leq : t -> t -> Prop;
    (* field axioms *)
    r_add_assoc : forall x y z, add x (add y z) = add (add x y) z; r_mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z;
    r_add_commute : forall x y, add x y = add y x; r_mul_commute : forall x y, mul x y = mul y x;
    r_dist : forall x y z, mul x (add y z) = add (mul x y) (mul x z);
    r_add_id : forall x, add x zero = x; r_mul_id : forall x, mul x one = x;
    zero_one_distinct : zero <> one;
    negate : forall x, { y | add x y = zero };
    invert : forall x, { y | mul x y = one };
    (* total ord axioms *)
    r_refl : forall x, leq x x;
    r_antisym : forall x y, leq x y -> leq y x -> x = y;
    r_trans : forall x y z, leq x y -> leq y z -> leq x z;
    r_total : forall x y, leq x y \/ leq y x;
    (* field consistent with order *)
    add_respects_leq : forall x y z, leq x y -> leq (add x z) (add y z);
    mul_respects_leq : forall x y, leq zero x -> leq zero y -> leq zero (mul x y);
    (* completeness of order *)
    order_complete : forall (A : t -> Prop) (non_empty : exists v, A v), { u | A u /\ forall w, A w -> leq w u } ->
        { u | A u /\ (forall w, A w -> leq w u) /\ forall v, (A v -> forall w, A w -> leq w v) -> leq u v };
    }.
