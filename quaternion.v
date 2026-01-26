

Require Import Reals.
Require Import Lra.
Require Import Psatz. (* 必须导入，用于 nra 策略 *)
Open Scope R_scope.

(* ========================================================= *)
(* Part 1: Basic Definitions                                 *)
(* ========================================================= *)

Record Quat : Type := mkQuat {
  qw : R;
  qx : R;
  qy : R;
  qz : R
}.

Definition q_add (q1 q2 : Quat) : Quat :=
  mkQuat (qw q1 + qw q2) (qx q1 + qx q2) (qy q1 + qy q2) (qz q1 + qz q2).

Definition q_scale (c : R) (q : Quat) : Quat :=
  mkQuat (c * qw q) (c * qx q) (c * qy q) (c * qz q).

Definition q_neg (q : Quat) : Quat := q_scale (-1) q.

Definition q_mul (q1 q2 : Quat) : Quat :=
  mkQuat 
    (qw q1 * qw q2 - qx q1 * qx q2 - qy q1 * qy q2 - qz q1 * qz q2)
    (qw q1 * qx q2 + qx q1 * qw q2 + qy q1 * qz q2 - qz q1 * qy q2)
    (qw q1 * qy q2 - qx q1 * qz q2 + qy q1 * qw q2 + qz q1 * qx q2)
    (qw q1 * qz q2 + qx q1 * qy q2 - qy q1 * qx q2 + qz q1 * qw q2).

Definition q_conj (q : Quat) : Quat :=
  mkQuat (qw q) (- qx q) (- qy q) (- qz q).

Definition q_norm2 (q : Quat) : R :=
  (qw q)^2 + (qx q)^2 + (qy q)^2 + (qz q)^2.

Definition is_unit_quat (q : Quat) : Prop := q_norm2 q = 1.

Definition is_pure (q : Quat) : Prop := qw q = 0.

(* ========================================================= *)
(* Part 2: Arithmetic Lemmas                                 *)
(* ========================================================= *)

Lemma q_mul_assoc : forall q1 q2 q3, q_mul q1 (q_mul q2 q3) = q_mul (q_mul q1 q2) q3.
Proof.
  intros. destruct q1, q2, q3.
  unfold q_mul. simpl. f_equal; ring.
Qed.

Lemma q_conj_mul : forall q1 q2, q_conj (q_mul q1 q2) = q_mul (q_conj q2) (q_conj q1).
Proof.
  intros.
  destruct q1, q2.
  unfold q_mul, q_conj. simpl. f_equal; ring.
Qed.

(* 右逆: q * q_conj = 1 *)
Lemma q_mul_unit_inv : forall q, is_unit_quat q -> q_mul q (q_conj q) = mkQuat 1 0 0 0.
Proof.
  intros. destruct q.
  unfold is_unit_quat, q_norm2, q_mul, q_conj in *.
  simpl in *.
  f_equal.
  - transitivity (qw0^2 + qx0^2 + qy0^2 + qz0^2).
    + ring.
    + exact H.
  - ring. - ring. - ring.
Qed.

(* 左逆: q_conj * q = 1 *)
Lemma q_inv_l : forall q, is_unit_quat q -> q_mul (q_conj q) q = mkQuat 1 0 0 0.
Proof.
  intros. destruct q.
  unfold is_unit_quat, q_norm2, q_mul, q_conj in *.
  simpl in *.
  f_equal.
  - transitivity (qw0^2 + qx0^2 + qy0^2 + qz0^2).
    + ring.
    + exact H.
  - ring. - ring. - ring.
Qed.

(* ========================================================= *)
(* Part 3: Rotation Definition                               *)
(* ========================================================= *)

Definition rotate (q v : Quat) : Quat :=
  q_mul (q_mul q v) (q_conj q).

(* ========================================================= *)
(* Part 4: Double Cover Proof                                *)
(* ========================================================= *)

Theorem double_cover_equality : forall (q v : Quat),
  rotate q v = rotate (q_neg q) v.
Proof.
  intros.
  unfold rotate, q_neg, q_scale.
  destruct q, v.
  unfold q_mul, q_conj.
  simpl. f_equal; ring.
Qed.

Theorem rotation_homomorphism : forall (q1 q2 v : Quat),
  is_unit_quat q1 -> is_unit_quat q2 ->
  rotate (q_mul q1 q2) v = rotate q1 (rotate q2 v).
Proof.
  intros.
  unfold rotate.
  rewrite q_conj_mul.      
  rewrite q_mul_assoc.     
  rewrite q_mul_assoc.
  rewrite q_mul_assoc.
  reflexivity.
Qed.

(* ========================================================= *)
(* Part 5: Kernel Proof                                      *)
(* ========================================================= *)

Definition Q_ONE := mkQuat 1 0 0 0.
Definition Q_NEG_ONE := mkQuat (-1) 0 0 0.
Definition I_vec := mkQuat 0 1 0 0.
Definition J_vec := mkQuat 0 0 1 0.

Lemma commute_basis_implies_real : forall q,
  q_mul q I_vec = q_mul I_vec q ->
  q_mul q J_vec = q_mul J_vec q ->
  qx q = 0 /\ qy q = 0 /\ qz q = 0.
Proof.
  intros q H1 H2.
  destruct q.
  unfold q_mul, I_vec, J_vec in *.
  simpl in *.
  injection H1 as Eq1 Eq2 Eq3 Eq4.
  injection H2 as Eq5 Eq6 Eq7 Eq8.
  split; [| split]; lra.
Qed.

Theorem kernel_is_plus_minus_one : forall q,
  is_unit_quat q ->
  (forall v, is_pure v -> rotate q v = v) -> 
  q = Q_ONE \/ q = Q_NEG_ONE.
Proof.
  intros q UnitQ IsIdentity.
  
  (* Step 1: 证明 q 与 i 交换 *)
  assert (H_comm_i : q_mul q I_vec = q_mul I_vec q).
  {
     specialize (IsIdentity I_vec).
     assert (P: is_pure I_vec) by (unfold I_vec, is_pure; reflexivity).
     apply IsIdentity in P.
     unfold rotate in P.
     
     assert (H_eq: q_mul (q_mul (q_mul q I_vec) (q_conj q)) q = q_mul I_vec q).
     { rewrite P. reflexivity. }
     
     rewrite <- q_mul_assoc in H_eq.
     rewrite q_inv_l in H_eq; [| assumption].
     
     destruct q;
     unfold q_mul, I_vec in *; simpl in *.
     
     injection H_eq as E1 E2 E3 E4.
     f_equal; lra.
  }

  (* Step 2: 证明 q 与 j 交换 *)
  assert (H_comm_j : q_mul q J_vec = q_mul J_vec q).
  {
     specialize (IsIdentity J_vec).
     assert (P: is_pure J_vec) by (unfold J_vec, is_pure; reflexivity).
     apply IsIdentity in P.
     unfold rotate in P.
     
     assert (H_eq: q_mul (q_mul (q_mul q J_vec) (q_conj q)) q = q_mul J_vec q).
     { rewrite P. reflexivity. }
     
     rewrite <- q_mul_assoc in H_eq.
     rewrite q_inv_l in H_eq; [| assumption].
     
     destruct q; unfold q_mul, J_vec in *; simpl in *.
     injection H_eq as E1 E2 E3 E4.
     f_equal; lra.
  }
  
  (* Step 3: 推导 q 为实数 *)
  apply commute_basis_implies_real in H_comm_i;
  [| assumption].
  destruct H_comm_i as [Hx [Hy Hz]].
  
  (* Step 4: 求解 w *)
  unfold is_unit_quat, q_norm2 in UnitQ.
  rewrite Hx, Hy, Hz in UnitQ.
  destruct q. simpl in *. subst.
  (* w^2 = 1 *)
  assert (qw0 = 1 \/ qw0 = -1).
  {
      assert (H_eq: qw0^2 - 1 = 0) by lra.
      replace (qw0^2 - 1) with ((qw0 - 1) * (qw0 + 1)) in H_eq by ring.
      apply Rmult_integral in H_eq.
      destruct H_eq as [H1 | H2].
      - left; lra.
      - right; lra.
  }
  
  destruct H; [left | right]; unfold Q_ONE, Q_NEG_ONE; f_equal; lra.
Qed.

(* ========================================================= *)
(* Part 6: Drift and Normalization                           *)
(* ========================================================= *)

(* --- 6.1 辅助引理：模长与缩放性质 --- *)

(* 证明：模长是乘性的 |q1*q2| = |q1|*|q2| *)
Lemma q_norm2_mul_distrib : forall q1 q2,
  q_norm2 (q_mul q1 q2) = (q_norm2 q1) * (q_norm2 q2).
Proof.
  intros. destruct q1, q2.
  unfold q_norm2, q_mul. simpl.
  ring.
Qed.

(* 证明：共轭不改变模长 *)
Lemma q_norm2_conj : forall q, q_norm2 (q_conj q) = q_norm2 q.
Proof.
  intros. destruct q.
  unfold q_norm2, q_conj. simpl.
  ring.
Qed.

(* 证明：缩放对模长的影响 |c*q|^2 = c^2 * |q|^2 *)
Lemma q_norm2_scale : forall c q,
  q_norm2 (q_scale c q) = (c * c) * (q_norm2 q).
Proof.
  intros. destruct q.
  unfold q_norm2, q_scale. simpl.
  ring.
Qed.

(* --- 6.2 漂移后果验证 --- *)

(* 【定理：非单位四元数会导致向量变形】 
   证明：如果 q 未归一化，rotate q v 的长度会被放大 |q|^4 倍。
   (此处假设 rotate 定义为 q v q_conj) *)
Theorem drift_causes_scaling : forall (q v : Quat),
  is_pure v -> 
  q_norm2 (rotate q v) = (q_norm2 q)^2 * (q_norm2 v).
Proof.
  intros q v PureV.
  unfold rotate.
  rewrite q_norm2_mul_distrib.
  rewrite q_norm2_mul_distrib.
  rewrite q_norm2_conj.
  ring.
Qed.

(* --- 6.3 归一化定义与验证 --- *)

(* 定义归一化函数：normalize(q) = q / |q| *)
Definition normalize (q : Quat) : Quat :=
  q_scale (/ sqrt (q_norm2 q)) q.


Lemma inv_sqrt_sq_eq_inv : forall x : R, 
  0 < x -> 
  (/ sqrt x) * (/ sqrt x) = / x.
Proof.
  intros x Hx_pos.
  
  (* 1. 证明 sqrt x 不为 0 *)
  assert (H_sqrt_nz: sqrt x <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. exact Hx_pos. }

  (* 2. 使用 transitivity 桥接 *)
  transitivity (/ (sqrt x * sqrt x)).
  
  (* Step A: 证明 1/u * 1/u = 1/(u*u)。 *)
  (* 'field' 策略能自动解决这个问题，只要分母非零 *)
  - field. 
    exact H_sqrt_nz.

  (* Step B: 证明 1/(sqrt x * sqrt x) = 1/x *)
  - f_equal. (* 去掉倒数符号 *)
    rewrite sqrt_sqrt.
    + reflexivity.
    + lra. (* 0 < x -> 0 <= x *)
Qed.

(* 【核心定理：归一化后的四元数必然是单位四元数】 *)
Theorem normalization_correct : forall q,
  q_norm2 q <> 0 -> 
  is_unit_quat (normalize q).
Proof.
  intros q Hnz.
  unfold is_unit_quat, normalize.
  
  (* 1. 展开缩放模长公式 *)
  rewrite q_norm2_scale.
  
  (* 2. 令 k = |q|^2 *)
  set (k := q_norm2 q).
  
  (* 3. 证明 k > 0 (平方和非零即为正) *)
  assert (Hk_pos: 0 < k).
  { unfold k, q_norm2 in *. destruct q. nra. }
  
  (* 4. 直接调用我们刚刚精心证明的引理 *)
  rewrite inv_sqrt_sq_eq_inv.
  
  - (* 主目标简化为：/ k * k = 1 *)
    field. 
    lra. (* k != 0 *)
    
  - (* 证明前提条件：k > 0 *)
    exact Hk_pos.
Qed.


(* 【验证：归一化修复了旋转漂移】 *)
Theorem normalized_rotation_preserves_norm : forall (q v : Quat),
  q_norm2 q <> 0 ->
  is_pure v ->
  q_norm2 (rotate (normalize q) v) = q_norm2 v.
Proof.
  intros q v Hnz PureV.
  
  (* 1. 应用漂移定理 *)
  rewrite drift_causes_scaling; [| exact PureV].
  
  (* 2. 应用归一化正确性定理 *)
  assert (H_unit: q_norm2 (normalize q) = 1).
  { apply normalization_correct. exact Hnz. }
  
  (* 3. 1^2 * |v| = |v| *)
  rewrite H_unit.
  ring. 
Qed.
Check kernel_is_plus_minus_one.
Print Assumptions kernel_is_plus_minus_one.
Check normalized_rotation_preserves_norm.
Print Assumptions normalized_rotation_preserves_norm.
