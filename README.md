# Formal Verification of Quaternion Dynamics: From Algebraic Theory to Engineering Drift Correction

**Author:** Ada Tsan Qin
**Date:** December 2025

> **Abstract**
>
>
> This project bridges the gap between abstract algebra and safety-critical engineering by formally verifying quaternion-based rotations using the **Coq Proof Assistant**. Beyond proving the classical isomorphism between unit quaternions ($S^3$) and the rotation group $\text{SO}(3)$, this work addresses a critical real-world issue: **Numerical Drift**.
>
> We rigorously formalize the error propagation model of non-unit quaternions and verify a normalization algorithm that guarantees geometric rigidity. The development process, spanning 19 iterations (V1–V19), demonstrates a sophisticated stratification of automated tactics (`field`, `lra`, `ring`) to overcome significant unification challenges in formal logic.
>
> We rigorously formalize the error propagation model of non-unit quaternions and verify a normalization algorithm that guarantees geometric rigidity. The development process, spanning 19 iterations (V1–V19), demonstrates a sophisticated stratification of automated tactics (`field`, `lra`, `ring`) to overcome significant unification challenges in formal logic.

---

## 1. Project Motivation

Quaternions are the *de facto* standard for attitude estimation in aerospace and robotics due to their singularity-free representation (avoiding Gimbal Lock). However, a dangerous gap exists between the **ideal mathematical model** and the **floating-point reality**:

* **The Theory:** Rotations are represented by unit quaternions ($|q|=1$).
* **The Reality:** Numerical integration causes the norm to drift ($|q| \approx 1 + \epsilon$). Applying a drifting quaternion to a vector ($v' = q v q^*$) induces non-physical scaling or shearing, potentially leading to control system failure.

**Objective:** To provide a high-assurance guarantee that a specific normalization pipeline restores the exact physical properties of a rigid body rotation, regardless of the input drift magnitude.

---

## 2. Mathematical Framework

### 2.1 Quaternion Algebra

Let $\mathbb{H}$ be the algebra of quaternions over $\mathbb{R}$.

$$
q = w + xi + yj + zk, \quad q^* = w - xi - yj - zk
$$

The squared norm is defined as $|q|^2 = q q^* = w^2 + x^2 + y^2 + z^2$.

### 2.2 The Double Cover Property

We verify that the map $\Phi: S^3 \to SO(3)$ defined by $\Phi(q, v) = q v q^*$ is a 2-to-1 homomorphism.

**Theorem Verified:**

$$
\forall q \in S^3, v \in \mathbb{R}^3: \quad \Phi(q, v) = \Phi(-q, v)
$$

This confirms that $q$ and $-q$ encode the same physical rotation.

### 2.3 Engineering Verification: Drift & Normalization

This section formalizes the engineering constraints added in Part 6 of the codebase.

#### Drift Error Model

We mathematically derive the scaling factor introduced by norm error. Using the multiplicative property $|ab| = |a||b|$:

$$
|v'| = |q v q^{\ast}| = |q| \cdot |v| \cdot |q^{\ast}| = |q|^2 |v|
$$

If $|q| \neq 1$, the vector length $|v|$ is scaled by $|q|^2$. This is formally proven in `drift_causes_scaling`.

#### Normalization Correction

We define the normalization function:

$$
\text{normalize}(q) = \frac{q}{\sqrt{|q|^2}}
$$

We prove the **Conservation of Norm**:

$$
|\Phi(\text{normalize}(q), v)| = \left| \frac{q}{\sqrt{|q|^2}} \cdot v \cdot \frac{q^*}{\sqrt{|q|^2}} \right| = \frac{|q|^2}{|q|^2} |v| = |v|
$$

This ensures that the corrected rotation is strictly isometric.

---

## 3. Code Structure

The source file `quaternion.v` is organized into six logical modules:

1.  **Part 1: Definitions**
    Defines the `Record Quat` and fundamental operations (`q_mul`, `q_conj`, `q_norm2`).
2.  **Part 2: Arithmetic**
    Establishes ring properties (associativity, distributivity) using the `ring` tactic.
3.  **Part 3: Rotation**
    Defines the conjugation map `rotate q v`.
4.  **Part 4: Double Cover**
    Proves invariance under negation ($\Phi(q) = \Phi(-q)$) and homomorphism.
5.  **Part 5: Kernel**
    Proves $\ker(\Phi) = \{1, -1\}$ by solving linear systems over basis vectors $i, j, k$ using `lra`.
6.  **Part 6: Engineering (New)**
    The novel contribution verifying drift correction and normalization safety.

---

## 4. Verified Theorems Detail

This section details the specific theorems proven in the codebase, their mathematical meaning, and the proof strategies employed.

### 4.1 Algebraic Properties (Part 2)

* **`q_mul_assoc` (Associativity)**
    * *Statement:* $(q_1 q_2) q_3 = q_1 (q_2 q_3)$
    * *Method:* **`ring`**. Since quaternion multiplication components are polynomial expressions of real numbers, the `ring` tactic automatically normalizes and compares the polynomials.
* **`q_inv_l` (Left Inverse)**
    * *Statement:* If $|q|=1$, then $q^* q = 1$.
    * *Method:* Expanded definitions and used `ring` combined with the hypothesis `qw^2 + ... = 1`.

### 4.2 Geometric Topology (Part 4 & 5)

* **`double_cover_equality`**
    * *Statement:* $\Phi(q, v) = \Phi(-q, v)$.
    * *Method:* Proved by expanding algebraic definitions. The negative signs cancel out in the conjugation $(-q) v (-q)^* = (-1)(-1) q v q^* = q v q^*$.
* **`rotation_homomorphism`**
    * *Statement:* $\Phi(q_1 q_2, v) = \Phi(q_1, \Phi(q_2, v))$.
    * *Method:* Rewriting using associativity and the property $(q_1 q_2)^* = q_2^* q_1^*$.
* **`kernel_is_plus_minus_one` (Kernel Property)**
    * *Statement:* If a unit quaternion $q$ leaves *every* pure vector $v$ unchanged (i.e., $q v q^* = v$), then $q = 1$ or $q = -1$.
    * *Method:*
        1.  **Instantiation:** Applied the hypothesis to basis vectors $i$ and $j$.
        2.  **Linear Solver:** Used **`lra`** (Linear Real Arithmetic) to solve the system $qi = iq$ and $qj = jq$, deducing that the vector part of $q$ must be zero ($x=y=z=0$).
        3.  **Non-linear Solver:** Used **`nra`** (Non-linear Real Arithmetic) to solve $w^2 = 1$ derived from the unit norm constraint, concluding $w = \pm 1$.

### 4.3 Engineering Verification (Part 6)

* **`drift_causes_scaling`**
    * *Statement:* For any quaternion $q$ (even if $|q| \neq 1$), $|\Phi(q, v)| = |q|^2 |v|$.
    * *Meaning:* Rotation by a drifting quaternion causes the object to shrink or expand.
    * *Method:* `ring` tactic applied to norm distribution properties.
* **`inv_sqrt_sq_eq_inv` (Lemma)**
    * *Statement:* For $x > 0$, $(1/\sqrt{x})^2 = 1/x$.
    * *Method:* **`field`**. This tactic automatically handles division and reciprocals in a field, provided the denominator is non-zero.
* **`normalization_correct`**
    * *Statement:* If $q \neq 0$, then $|\text{normalize}(q)| = 1$.
    * *Method:* Combined `field` tactic (to handle the division by $\sqrt{|q|^2}$) with `nra` (to prove $|q|^2 > 0$).
* **`normalized_rotation_preserves_norm` (Final Theorem)**
    * *Statement:* $\forall q \neq 0$, the rotation $\Phi(\text{normalize}(q), v)$ is an isometry (preserves length of $v$).
    * *Method:* Chained the `drift_causes_scaling` theorem with `normalization_correct`, proving mathematically that the drift is perfectly cancelled.

---

## 5. Technical Highlights

### Tactics Stratification Strategy

A key technical achievement is the strategic selection of solvers based on the problem domain:

* **`ring`**: Used for pure polynomial identities (associativity).
* **`field`**: Used for fractional algebra in normalization proofs (**V19 breakthrough**). It automatically handles reciprocals like $1/\sqrt{x} \cdot 1/\sqrt{x} = 1/x$.
* **`lra`**: Used for solving systems of linear equations in the Kernel proof.
* **`nra`**: Used for proving non-linear constraints ($w^2 = 1 \implies w = \pm 1$).

---

## 6. Development & Debugging Log (V1 -- V19)

The robustness of this verification suite was achieved through an iterative process of failure analysis and refinement.

### Phase 1: Foundation (V1--V5)
* **Challenge:** Early proofs used nested `replace` tactics, making the code brittle.
* **Solution:** Refactored code to use **Lemma Extraction**. Specifically, we proved the Left Inverse Lemma (`q_inv_l`) to resolve rewriting direction issues.

### Phase 2: Syntax & Standards (V6--V9)
* **Issue:** `Syntax error` caused by nested comments.
* **Fix:** Sanitized comments and updated deprecated library functions.

### Phase 3: The "Greedy Substitution" Trap (V10--V15)
* **Error:** `Unable to unify ... with "sqrt (sqrt k * sqrt k)"`.
* **Context:** `replace` tactic recursively replaced the atomic $k$ inside the square root term.
* **Fix:** Abandoned global replacement in favor of `transitivity` chains.

### Phase 4: Implicit Arguments Hell (V16--V18)
* **Error:** `Illegal application ... Rinv_mult`.
* **Cause:** Attempted to pass explicit proofs to implicit arguments in standard library theorems.

### Phase 5: Final Victory (V19)
* **Strategy:** "Automate the Algebra."
* **Solution:** Switched to the **`field`** tactic.
* **Logic:** Proved the non-zero condition ($ k > 0 $) using `nra`, then let `field` automatically resolve the fractional equality.
* **Result:** ✅ **All Green**. Full compilation.

---

## 7. Axiom Dependency Analysis

When compiling the proofs (specifically `kernel_is_plus_minus_one` and `normalized_rotation_preserves_norm`), Coq reports the following axioms:

```coq
Axioms:
ClassicalDedekindReals.sig_forall_dec
ClassicalDedekindReals.sig_not_dec
FunctionalExtensionality.functional_extensionality_dep
```

### Explanation of Axioms

This output is **expected and correct** for formal verification involving Real Numbers ($\mathbb{R}$) in Coq.

1.  **`ClassicalDedekindReals` (sig_forall_dec / sig_not_dec)**:
    * **Origin:** Imported via `Require Import Reals` and `Lra`.
    * **Meaning:** Coq's standard library for Real Numbers is **Classical**, meaning it assumes the **Law of Excluded Middle** ($P \lor \neg P$).
    * **Why it's needed:** The automated decision tactics `lra` (Linear Real Arithmetic) and `nra` (Non-linear Real Arithmetic) rely on these classical axioms to decidability prove inequalities (e.g., determining if $x < y$, $x = y$, or $x > y$). Without these axioms, comparing real numbers is undecidable in constructive logic.

2.  **`FunctionalExtensionality`**:
    * **Origin:** Implicitly pulled in by the Real analysis libraries.
    * **Meaning:** It asserts that if $f(x) = g(x)$ for all $x$, then the functions $f$ and $g$ are equal ($f = g$).
    * **Why it's needed:** This is standard for mathematical proofs involving function equivalence over real domains.

**Conclusion:** The presence of these axioms confirms that the proofs are grounded in standard **Classical Mathematics**, which is the appropriate foundation for engineering and physics applications (as opposed to Constructive Mathematics).

---

## How to Run

1.  Ensure **Coq 8.16** or later is installed.
2.  Open `quaternion.v` in CoqIDE or VS Code (with Coq-LSP/VsCoq).
3.  Step through the proofs. All 6 parts should compile successfully.