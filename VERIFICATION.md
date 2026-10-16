# Claim-by-claim verification map

Each paper claim is listed with the Lean declarations in `ArrowOfTime.lean` that prove it. All names live in the namespace `Arrow`.

## Sec. II — Path laws, observations, resources

| Paper | Lean |
|---|---|
| Data processing, Eq. (4) | `KL_push_le`, `KL_chan_le`, `TV_push_le`, `TV_chan_le` |
| Chain rule, Eq. (5) | `KL_chain` |
| Total variation as best test, Eq. (6); Bayes error (1 − TV)/2 | `TV_isGreatest`, `expect_lrTest`, `bayesErr_optimal` |
| Invariance under bijections | `KL_push_equiv`, `TV_push_equiv` |
| Gibbs inequality | `KL_nonneg` |

## Sec. III — Fully observed Markov chains

| Paper | Lean |
|---|---|
| Proposition III.1 | `nogo_markov`, `markovLaw_isProb`, `prod_fractions`, `lr_decision_cross` |
| Proposition III.2 | `approx_likelihood_decision` |
| Coordinate-change criterion | `recoding_transport` |

## Sec. IV — Universal one-bit construction

| Paper | Lean |
|---|---|
| Hard-core assumption, Eq. (11) | `HardCoreAssumption` (definition, used as a hypothesis) |
| Lemma IV.1 | `encoder_comm`, `encoderEquiv`, `encoder_bijective`, `encLaw_reverse` |
| Theorem IV.2, Eqs. (15)–(17) | `universal_concealment`, `universal_concealment_asymptotic` |
| Mutual information ≤ log 2 | `labelInfo_le_log_two` |

## Sec. V — Driven three-state ring

| Paper | Lean |
|---|---|
| Rates, stationarity, local detailed balance, cycle affinity 3a | `ring_uniform_stationary`, `ring_ldb`, `ring_cycle_affinity` |
| p = eᵃ/(1+eᵃ); p = 3/4 ↔ a = log 3 | `jump_bias`, `bias_gt_half`, `bias_log_three` |
| Entropy production, Eq. (20) | `ring_sigma`, `llr_bernProd` |
| Reversal θₘ, Eqs. (21)–(22) | `jumpRev`, `jumpRev_involutive`, `bernProd_jumpRev` |
| Sufficiency of the direction string | `sufficient_statistic_no_loss` |
| Theorem V.1, Eqs. (23)–(29) | `ring_statistics`, `ring_concealment`, `ring_separation`, `drate_eq_tanh`, `drate_pos`, `KL_bernProd`, `TV_bernProd`, `bayesErrBin_le_hoeffding` |
| Encoded likelihood, Eqs. (30)–(32) | `ringP_apply`, `ringQ_apply`, `ring_encoded_llr` |
| Fluctuation relations, Eqs. (33)–(34) | `ring_encoded_fluctuations` |
| Absolute current has the same law under both hypotheses | `ring_abs_current_same_law` |
| Acceptance probability, Eq. (35) | `acceptProb_equiv`, `expected_trials_equiv` |

## Sec. VI — Fixed-time experiment with cutoff

| Paper | Lean |
|---|---|
| Full core divergence, Eq. (36) | `fullCoreKL_eq` |
| Theorem VI.1, Eqs. (37)–(39) | `clocked_KL`, `clocked_KL_loss`, `clocked_TV`, `clocked_bounds`, `clocked_concealment` |
| Poisson first-moment identity, Eq. (40) | `poisson_tail_first_moment` |
| Poisson Chernoff bound, Eq. (41) | `poisTailGE_le`, `poisson_rate_pos` |

## Sec. VII — Causal recording

| Paper | Lean |
|---|---|
| Lemma VII.1, Eq. (43) | `generator_bound`, `adv_gen_le_sum` |
| Palindromic mask and causal encoder, Eqs. (44)–(45) | `mask`, `causalEnc`, `causalEncEquiv` |
| Theorem VII.2, Eqs. (46)–(47) | `causal_concealment`, `causalEnc_comm`, `expect_genIdeal_causalRed` |
| Ideal mirror-pair probabilities, Eq. (48) | `masked_pair_ideal` |

## Sec. VIII — Repeated observations and leakage

| Paper | Lean |
|---|---|
| Proposition VIII.1, Eq. (49) | `many_records_onebit`, `many_records_causal`, `many_records_negligible`, `adv_iid_le_sum` |
| Additivity of KL over independent records | `KL_iidLaw` |
| Seed-reuse attack (one-bit) | `seed_reuse_attack` |
| Mask-reuse attack, Eq. (50) | `mask_recovery_failure` |
| Exact mask-recovery probability, Eq. (79) | `mask_recovery_exact` |
| Efficient post-processing, Eq. (51) | `advLE_chan` |

## Sec. IX — Efficient entropy-production witnesses

| Paper | Lean |
|---|---|
| Donsker–Varadhan formula, Eq. (52) | `KL_isGreatest_dvObj`, `dvObj_le_KL`, `expect_le_log_expect_exp` |
| Proposition IX.1, Eq. (54) | `restricted_dv_bound`, `restricted_dv_negligible`, `ring_score_range` |
| Corollary IX.2 | `no_signed_estimator`, `ring_sign_test`, `ring_wrong_side` |
| Binary data processing, Eq. (55) | `dbin_le_KL` |

## Sec. X — Noise and reliability

| Paper | Lean |
|---|---|
| Theorem X.1, Eqs. (56)–(58) | `payload_noise_law`, `ring_noisy_laws`, `chan_bscN_bernProd`, `encLaw_noise`, `causalLaw_noise` |
| Noise loss, Eq. (59); vanishing at η = 1/2 | `noise_loss_nonneg`, `noise_half` |
| Weak-bias expansion and Eq. (60) | `drate_expansion`, `noise_threshold` |
| Proposition X.2, Eqs. (61)–(63) | `contam_KL_le`, `contam_TV`, `contam_TV_close`, `ring_contamination`, `exp_neg_sqrt_negligible` |
| Theorem X.3, Eqs. (64)–(68) | `reliability_law`, `reliability_law_infinite`, `reliability_sqrt`, `contam_KL_exact`, `gfun_eq`, `gfun_ge_min` |
| Endpoint repetition code, Eq. (69) | `endpoint_failure` |
| Theorem X.4, Eqs. (70)–(72) | `readout_theorem`, `readout_errors`, `KL_ge_of_test_errors`, `binary_lower_linear` |
| Logical reliability criterion, Eq. (73) | `adv_transfer`, `logical_reliability`, `TV_le_of_coupling` |

## Sec. XI — Description length vs decoding time

| Paper | Lean |
|---|---|
| Counting bound, Eq. (74) | `complexity_count`, `card_descLT_lt` |
| Invariance under the encoder, Eq. (75) | `complexity_invariance` (composition property as a hypothesis) |

## Sec. XII — Physical implementation

| Paper | Lean |
|---|---|
| Proposition XII.1 | `clean_encoder_inverts`, `clean_onebit_inverts`, `clean_iterate_inverts` |

## Sec. XIII — Exact numerical checks

| Paper value | Lean |
|---|---|
| D = 4 log 3, TV = 0.85888671875 (one-bit toy) | `toy_onebit_values` |
| D = 3 log 3, TV = 0.79296875 (causal toy) | `toy_causal_values` |
| 2.22 log(137/63) ≈ 1.72459856 (noisy check) | `toy_noisy_value` |
| 6 log(13/7) ≈ 3.71424 (fluctuation example) | `toy_fluctuation_mean` |
| 40 log 3 ≈ 43.9444915 (fixed-time example) | `toy_clocked_full_core` |
| Mask recovery at q = 1 | `toy_reuse_q1` |

The Monte Carlo estimates, floating-point Poisson sums and plotted curves of Sec. XIII are regenerated by `code/reproduce.py` and are outside the formal development.

## Appendices

| Paper | Lean |
|---|---|
| A: Chernoff bound, Eqs. (A2)–(A3) | `lowerTail_le_chernoff`, `chernoff_eq_exp`, `chernoffExp_ge` |
| A: Moments and generating function, Eqs. (A4)–(A6) | `mean_sigma`, `var_sigma`, `mgf_sigma`, `ift_from_mgf`, `ift_second_moment`, `ift_second_bracket_gt_one` |
| B: Exact p = 3/4 sampler; reverse sampler | `sampler_three_quarters`, `reverse_sampler` |
| B: Finite precision | `TV_le_of_pointwise`, `adv_approx_sampler` |
| C: Common-channel contamination, Eq. (C2) | `contamChan`, `chan_contamChan` |
| E: Rényi divergence, Eq. (E2) | `ring_renyi` |
| E: Hellinger affinity and TV bounds, Eqs. (E3)–(E4) | `ring_hellinger`, `ring_hellinger_TV`, `hellinger_TV_bounds` |
| E: Weak-driving expansions, Eq. (E5) | `bias_expansion`, `drate_weak_expansion` |
| E: Regimes, Eqs. (E6)–(E7) | `weak_divergence_limit`, `weak_divergence_zero`, `weak_strong_regime`, `weak_threshold`, `weak_clt_TV` (CLT as a hypothesis) |
