import GoalDecay

open GoalDecay

-- The receipt: every theorem must reduce to the standard axioms only
-- (propext, Classical.choice, Quot.sound) — no `sorryAx`.

#print axioms noFeedback_eq
#print axioms noFeedback_exp
#print axioms noFeedback_not_affine
#print axioms linear_le_noFeedback
#print axioms linear_dies
#print axioms sandwich
#print axioms feedback_mul
#print axioms feedback_eq
#print axioms feedback_le_noFeedback
#print axioms feedback_not_geometric
#print axioms feedback_catastrophe
#print axioms affineStep_eq
#print axioms feedbackPow_mul
#print axioms feedbackPow_one
#print axioms feedbackPow_mono_k
#print axioms feedbackPow_catastrophe
#print axioms maj3rate_pos
#print axioms maj3rate_lt
#print axioms maj3Iter_bound
#print axioms maj3_vanishes
#print axioms boolMaj3_consensus
#print axioms geometric_bound
#print axioms feedbackGrow_eq
#print axioms growR_ge
#print axioms growP_factorial
#print axioms feedbackGrow_catastrophe
#print axioms feedbackPow_two
#print axioms gen_two_k6_fails
#print axioms gen_two_k5_passes
#print axioms grow_fact_gen3
#print axioms eval_indistinguishable
#print axioms probes_eventually_catch
#print axioms catch_le_mul

-- The distillate
#print axioms GoalDecayCore.tower_closed
#print axioms GoalDecayCore.retention_bound
#print axioms GoalDecayCore.retention_catastrophe
#print axioms GoalDecayCore.tower_catastrophe
#print axioms GoalDecayCore.law_catastrophe
#print axioms GoalDecayCore.geometric_not_affine
#print axioms GoalDecayCore.linear_dies
#print axioms GoalDecayCore.linear_le_geometric
#print axioms GoalDecayCore.survival_threshold
#print axioms GoalDecayCore.metastability
#print axioms GoalDecayCore.goal_content_integrity

-- Headline statements, for the record:
#check @noFeedback_eq
#check @feedback_mul
#check @sandwich
#check @feedback_catastrophe
#check @feedbackPow_mul
#check @feedbackPow_catastrophe
#check @maj3Iter_bound
#check @boolMaj3_consensus
#check @geometric_bound
#check @feedbackGrow_eq
#check @feedbackGrow_catastrophe
#check @gen_two_k6_fails
#check @eval_indistinguishable
#check @GoalDecayCore.goal_content_integrity
