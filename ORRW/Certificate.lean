module

public import ORRW.Frozen.AlmostSure.DisplacementAlmostSure
public import ORRW.Frozen.AlmostSure.PathMeasureBridge
public import ORRW.Frozen.AlmostSure.RangeAlmostSure
public import ORRW.Frozen.Guards.EdgesLeSites
public import ORRW.Frozen.Guards.OneStepWitness
public import ORRW.Frozen.Guards.ProbIsPMF
public import ORRW.Frozen.Guards.TotalWeightPos
public import ORRW.Frozen.Insertion.ExitTimeBounds
public import ORRW.Frozen.Insertion.InsertionInequality
public import ORRW.Frozen.Insertion.OnePointInsertion
public import ORRW.Frozen.Insertion.ResistancePacking
public import ORRW.Frozen.Occupation.LazyGreen
public import ORRW.Frozen.Occupation.Occupation
public import ORRW.Frozen.Occupation.OccupationCesaro
public import ORRW.Frozen.Occupation.OccupationMeasure
public import ORRW.Frozen.Potential.AccumulatedCharge
public import ORRW.Frozen.Potential.InsertionOrder
public import ORRW.Frozen.Potential.Supermartingale
public import ORRW.Frozen.RangeLowerBound
public import ORRW.Frozen.RangeTail
public import ORRW.Frozen.Tail.Displacement
public import ORRW.Frozen.Tail.ExponentsOptimal
public import ORRW.Frozen.Tail.SigmaTail
public import ORRW.Frozen.Tail.TimeVersusCharge

@[expose] public section

/-!
Reader entry point: all 24 frozen exports and their transitive axiom dependencies.
See VERIFICATION.md for the paper correspondence and modelling conventions.
-/

#print axioms ORRW.Frozen.range_lower_bound
#print axioms ORRW.Frozen.range_tail
#print axioms ORRW.Frozen.max_exit
#print axioms ORRW.Frozen.one_point_insertion
#print axioms ORRW.Frozen.resistance_packing
#print axioms ORRW.Frozen.insertion_inequality
#print axioms ORRW.Frozen.totalWeight_pos
#print axioms ORRW.Frozen.sum_prob_eq_one
#print axioms ORRW.Frozen.card_edges_le_card_range
#print axioms ORRW.Frozen.expect_card_range_one_step
#print axioms ORRW.Frozen.supermartingale_drift
#print axioms ORRW.Frozen.insertion_order
#print axioms ORRW.Frozen.accumulated_charge
#print axioms ORRW.Frozen.time_versus_charge
#print axioms ORRW.Frozen.sigma_tail
#print axioms ORRW.Frozen.displacement
#print axioms ORRW.Frozen.exponents_optimal
#print axioms ORRW.Frozen.lazy_green_bounds
#print axioms ORRW.Frozen.occupation
#print axioms ORRW.Frozen.occupation_cesaro
#print axioms ORRW.Frozen.occupation_measure
#print axioms ORRW.Frozen.pathMeasure_restr
#print axioms ORRW.Frozen.range_ae
#print axioms ORRW.Frozen.displacement_ae
