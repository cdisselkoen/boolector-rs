use boolector_sys::*;
use crate::node::{Array, BV};
use crate::option::*;
use crate::option::BtorOption;
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_void};

/// A `Btor` represents an instance of the Boolector solver.
/// Each `BV` and `Array` is created in a particular `Btor` instance.
#[derive(PartialEq, Eq, Debug)]
pub struct Btor {
    btor: *mut boolector_sys::Btor,
}

/// According to
/// https://groups.google.com/forum/#!msg/boolector/itYGgJxU3mY/AC2O0898BAAJ,
/// the Boolector library is thread-safe, so we make `Btor` both `Send` and
/// `Sync`.
unsafe impl Send for Btor {}
unsafe impl Sync for Btor {}

impl Btor {
    /// Create a new `Btor` instance with no variables and no constraints.
    pub fn new() -> Self {
        Self {
            btor: unsafe { boolector_new() },
        }
    }

    pub(crate) fn as_raw(&self) -> *mut boolector_sys::Btor {
        self.btor
    }

    /// Set an option to a particular value.
    #[allow(clippy::cognitive_complexity)]
    pub fn set_opt(&self, opt: BtorOption) {
        match opt {
            BtorOption::ModelGen(mg) => {
                let val = match mg {
                    ModelGen::Disabled => 0,
                    ModelGen::Asserted => 1,
                    ModelGen::All => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_MODEL_GEN, val) }
            },
            BtorOption::Incremental(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_INCREMENTAL, if b { 1 } else { 0 }) }
            },
            BtorOption::IncrementalSMT1(ismt1) => {
                let val = match ismt1 {
                    IncrementalSMT1::Disabled => 0,
                    IncrementalSMT1::EagerStop => 1,
                    IncrementalSMT1::SolveAll => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_INCREMENTAL_SMT1, val) }
            },
            BtorOption::OutputNumberFormat(nf) => {
                let val = match nf {
                    NumberFormat::Binary => 0,
                    NumberFormat::Decimal => 2,
                    NumberFormat::Hexadecimal => 1,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_OUTPUT_NUMBER_FORMAT, val) }
            },
            BtorOption::OutputFileFormat(ff) => {
                let val = match ff {
                    FileFormat::BTOR => (-1_i32) as u32,
                    FileFormat::SMTLIBv1 => 1,
                    FileFormat::SMTLIBv2 => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_OUTPUT_FORMAT, val) }
            },
            BtorOption::SolverEngine(se) => {
                let val = match se {
                    SolverEngine::Fun => 0,
                    SolverEngine::SLS => 1,
                    SolverEngine::Prop => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_ENGINE, val) }
            },
            BtorOption::SatEngine(se) => {
                let s: &'static str = match se {
                    SatEngine::Lingeling => "Lingeling",
                    SatEngine::PicoSAT => "PicoSAT",
                    SatEngine::MiniSAT => "MiniSAT",
                };
                let s = CString::new(s).unwrap();
                unsafe { boolector_set_sat_solver(self.as_raw(), s.as_ptr() as *const c_char) }
            },
            BtorOption::AutoCleanup(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_AUTO_CLEANUP, if b { 1 } else { 0 }) }
            },
            BtorOption::PrettyPrint(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PRETTY_PRINT, if b { 1 } else { 0 }) }
            },
            BtorOption::Seed(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SEED, u) }
            },
            BtorOption::RewriteLevel(rl) => {
                let val = match rl {
                    RewriteLevel::None => 0,
                    RewriteLevel::TermLevel => 1,
                    RewriteLevel::More => 2,
                    RewriteLevel::Full => 3,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_REWRITE_LEVEL, val) }
            },
            BtorOption::SkeletonPreproc(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SKELETON_PREPROC, if b { 1 } else { 0 }) }
            },
            BtorOption::Ackermann(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_ACKERMANN, if b { 1 } else { 0 }) }
            },
            BtorOption::BetaReduceAll(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_BETA_REDUCE_ALL, if b { 1 } else { 0 }) }
            },
            BtorOption::EliminateSlices(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_ELIMINATE_SLICES, if b { 1 } else { 0 }) }
            },
            BtorOption::VariableSubst(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_VAR_SUBST, if b { 1 } else { 0 }) }
            },
            BtorOption::UnconstrainedOpt(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_UCOPT, if b { 1 } else { 0 }) }
            },
            BtorOption::MergeLambdas(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_MERGE_LAMBDAS, if b { 1 } else { 0 }) }
            },
            BtorOption::ExtractLambdas(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_EXTRACT_LAMBDAS, if b { 1 } else { 0 }) }
            },
            BtorOption::Normalize(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_NORMALIZE, if b { 1 } else { 0 }) }
            },
            BtorOption::NormalizeAdd(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_NORMALIZE_ADD, if b { 1 } else { 0 }) }
            },
            BtorOption::FunPreProp(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_PREPROP, if b { 1 } else { 0 }) }
            },
            BtorOption::FunPreSLS(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_PRESLS, if b { 1 } else { 0 }) }
            },
            BtorOption::FunDualProp(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_DUAL_PROP, if b { 1 } else { 0 }) }
            },
            BtorOption::FunDualPropQsortOrder(dpqo) => {
                let val = match dpqo {
                    DualPropQsortOrder::Just => 0,
                    DualPropQsortOrder::Asc => 1,
                    DualPropQsortOrder::Desc => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_DUAL_PROP_QSORT, val) }
            },
            BtorOption::FunJustification(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_JUST, if b { 1 } else { 0 }) }
            },
            BtorOption::FunJustificationHeuristic(jh) => {
                let val = match jh {
                    JustificationHeuristic::Left => 0,
                    JustificationHeuristic::MinApp => 1,
                    JustificationHeuristic::MinDepth => 2,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_JUST_HEURISTIC, val) }
            },
            BtorOption::FunLazySynthesize(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_LAZY_SYNTHESIZE, if b { 1 } else { 0 }) }
            },
            BtorOption::FunEagerLemmas(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_FUN_EAGER_LEMMAS, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSNumFlips(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_NFLIPS, u) }
            },
            BtorOption::SLSMoveStrategy(sms) => {
                let val = match sms {
                    SLSMoveStrategy::BestMove => 0,
                    SLSMoveStrategy::RandomWalk => 1,
                    SLSMoveStrategy::FirstBestMove => 2,
                    SLSMoveStrategy::BestSameMove => 3,
                    SLSMoveStrategy::AlwaysProp => 4,
                };
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_STRATEGY, val) }
            },
            BtorOption::SLSJustification(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_JUST, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSGroupWiseMoves(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_GW, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSRangeWiseMoves(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_RANGE, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSSegmentWiseMoves(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_SEGMENT, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSRandomWalkMoves(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_RAND_WALK, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSRandomWalkProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_PROB_MOVE_RAND_WALK, u) }
            },
            BtorOption::SLSRandomizeAll(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_RAND_ALL, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSRandomizeRange(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_RAND_RANGE, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSPropagationMoves(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_PROP, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSPropagationMovesNumProp(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_PROP_N_PROP, u) }
            },
            BtorOption::SLSPropagationMovesNumRegular(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_PROP_N_SLS, u) }
            },
            BtorOption::SLSForceRandomWalks(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_PROP_FORCE_RW, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSIncMoveTest(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_MOVE_INC_MOVE_TEST, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSRestarts(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_USE_RESTARTS, if b { 1 } else { 0 }) }
            },
            BtorOption::SLSBanditScheme(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_SLS_USE_BANDIT, if b { 1 } else { 0 }) }
            },
            BtorOption::PropNumSteps(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_NPROPS, u) }
            },
            BtorOption::PropRestarts(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_USE_RESTARTS, if b { 1 } else { 0 }) }
            },
            BtorOption::PropBanditScheme(b) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_USE_BANDIT, if b { 1 } else { 0 }) }
            },
            BtorOption::PropPathSelectionMode(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PATH_SEL, u) }
            },
            BtorOption::PropInvValueProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_USE_INV_VALUE, u) }
            },
            BtorOption::PropFlipConditionProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_FLIP_COND, u) }
            },
            BtorOption::PropFlipConditionProbabilityConstant(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_FLIP_COND_CONST, u) }
            },
            BtorOption::PropFlipConditionNumPaths(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL, u) }
            },
            BtorOption::PropFlipConditionProbabilityConstantDelta(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_FLIP_COND_CONST_DELTA, u) }
            },
            BtorOption::PropSliceKeepDCProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_SLICE_KEEP_DC, u) }
            },
            BtorOption::PropConcatFlipProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_CONC_FLIP, u) }
            },
            BtorOption::PropSliceFlipProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_SLICE_FLIP, u) }
            },
            BtorOption::PropEqFlipProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_EQ_FLIP, u) }
            },
            BtorOption::PropAndFlipProbability(u) => {
                unsafe { boolector_set_opt(self.as_raw(), BtorOption_BTOR_OPT_PROP_PROB_AND_FLIP, u) }
            },
        }
    }

    /// Solve the current input (defined by the constraints which have been added
    /// via [`BV::assert()`](struct.BV.html#method.assert) and
    /// [`BV::assume()`](struct.BV.html#method.assume)). All assertions and
    /// assumptions are implicitly combined via Boolean `and`.
    ///
    /// Calling this function multiple times requires incremental usage to be
    /// enabled via [`Btor::set_opt()`](struct.Btor.html#method.set_opt).
    /// If incremental usage is not enabled, this function may only be called
    /// once.
    pub fn sat(&self) -> SolverResult {
        #[allow(non_upper_case_globals)]
        match unsafe { boolector_sat(self.as_raw()) } as u32 {
            BtorSolverResult_BTOR_RESULT_SAT => SolverResult::Sat,
            BtorSolverResult_BTOR_RESULT_UNSAT => SolverResult::Unsat,
            BtorSolverResult_BTOR_RESULT_UNKNOWN => SolverResult::Unknown,
            u => panic!("Unexpected return value from boolector_sat(): {}", u),
        }
    }

    /// Push `n` context levels. `n` must be at least 1.
    pub fn push(&self, n: u32) {
        unsafe { boolector_push(self.as_raw(), n) }
    }

    /// Pop `n` context levels. `n` must be at least 1.
    pub fn pop(&self, n: u32) {
        unsafe { boolector_pop(self.as_raw(), n) }
    }

    /// Duplicate a `Btor` instance. This will copy all variables, assertions,
    /// etc into the new instance.
    ///
    /// Each `BV` or `Array` may only be used with the `Btor` it was originally
    /// created for. If you have a `BV` for one `Btor` and want to find the
    /// corresponding `BV` in another `Btor`, use
    /// [`Btor::get_matching_bv()`](struct.Btor.html#method.get_matching_bv) or
    /// [`Btor::get_bv_by_symbol()`](struct.Btor.html#method.get_bv_by_symbol).
    ///
    /// With [`SatEngine::Lingeling`](option/enum.SatEngine.html), this can be
    /// called at any time; but with `SatEngine::PicoSAT` or
    /// `SatEngine::MiniSAT`, this can only be called prior to the first
    /// `Btor::sat()` call.
    ///
    /// The Boolector API docs refer to this operation as "clone", but we use
    /// `duplicate()` to avoid confusion.
    ///
    /// # Example
    ///
    /// ```
    /// # use boolector::{Btor, BV, SolverResult};
    /// # use boolector::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // `x` is an 8-bit `BV` less than `42`
    /// let x = BV::new(btor.clone(), 8, Some("x"));
    /// x.ult(&BV::from_u32(btor.clone(), 42, 8)).assert();
    ///
    /// // `y` is equal to `x + 7`
    /// let y = x.add(&BV::from_u32(btor.clone(), 7, 8));
    ///
    /// // We duplicate the `Btor` instance
    /// let btor_2 = Rc::new(btor.duplicate());
    ///
    /// // The duplicated instance has copied versions of
    /// // `x` and `y` which are distinct from the original
    /// // `x` and `y` but still have the corresponding
    /// // relationship (i.e., `y_2 = x_2 + 7`)
    /// let x_2 = Btor::get_matching_bv(btor_2.clone(), &x).unwrap();
    /// let y_2 = Btor::get_matching_bv(btor_2.clone(), &y).unwrap();
    ///
    /// // The instances are totally independent now. In the
    /// // original instance, we'll assert that `x > 3`, while
    /// // in the new instance, we'll assert that `x < 3`.
    /// // Note that we're careful to create constants with the
    /// // correct `Btor` instance.
    /// x.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    /// x_2.ult(&BV::from_u32(btor_2.clone(), 3, 8)).assert();
    ///
    /// // Each instance is satisfiable by itself
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// assert_eq!(btor_2.sat(), SolverResult::Sat);
    ///
    /// // In the first instance, `y > 10`, while in the second,
    /// // `y < 10`
    /// let y_solution = y.get_a_solution().as_u64().unwrap();
    /// assert!(y_solution > 10);
    /// let y_2_solution = y_2.get_a_solution().as_u64().unwrap();
    /// assert!(y_2_solution < 10);
    /// ```
    pub fn duplicate(&self) -> Self {
        Self {
            btor: unsafe { boolector_clone(self.as_raw()) },
        }
    }

    /// Given a `BV` originally created for any `Btor`, get the corresponding
    /// `BV` in the given `btor`. This only works if the `BV` was created before
    /// the relevant `Btor::duplicate()` was called; that is, it is intended to
    /// be used to find the copied version of a given `BV` in the new `Btor`.
    ///
    /// It's also fine to call this with a `BV` created for the given `Btor`
    /// itself, in which case you'll just get back `Some(bv.clone())`.
    ///
    /// For a code example, see
    /// [`Btor::duplicate()`](struct.Btor.html#method.duplicate).
    pub fn get_matching_bv<R: AsRef<Btor> + Clone>(btor: R, bv: &BV<R>) -> Option<BV<R>> {
        let node = unsafe { boolector_match_node(btor.as_ref().as_raw(), bv.node) };
        if node.is_null() {
            None
        } else if unsafe { boolector_is_array(btor.as_ref().as_raw(), node) } {
            None
        } else {
            Some(BV { btor, node })
        }
    }

    /// Given an `Array` originally created for any `Btor`, get the corresponding
    /// `Array` in the given `btor`. This only works if the `Array` was created
    /// before the relevant `Btor::duplicate()` was called; that is, it is
    /// intended to be used to find the copied version of a given `Array` in the
    /// new `Btor`.
    ///
    /// It's also fine to call this with an `Array` created for the given `Btor`
    /// itself, in which case you'll just get back `Some(array.clone())`.
    pub fn get_matching_array<R: AsRef<Btor> + Clone>(btor: R, array: &Array<R>) -> Option<Array<R>> {
        let node = unsafe { boolector_match_node(btor.as_ref().as_raw(), array.node) };
        if node.is_null() {
            None
        } else if unsafe { boolector_is_array(btor.as_ref().as_raw(), node) } {
            Some(Array { btor, node })
        } else {
            None
        }
    }

    /// Given a symbol, find the `BV` in the given `Btor` which has that symbol.
    ///
    /// Since `Btor::duplicate()` copies all `BV`s to the new `Btor` including
    /// their symbols, this can also be used to find the copied version of a
    /// given `BV` in the new `Btor`.
    pub fn get_bv_by_symbol<R: AsRef<Btor> + Clone>(btor: R, symbol: &str) -> Option<BV<R>> {
        let cstring = CString::new(symbol).unwrap();
        let symbol = cstring.as_ptr() as *const c_char;
        let node = unsafe { boolector_match_node_by_symbol(btor.as_ref().as_raw(), symbol) };
        if node.is_null() {
            None
        } else if unsafe { boolector_is_array(btor.as_ref().as_raw(), node) } {
            None
        } else {
            Some(BV { btor, node })
        }
    }

    /// Given a symbol, find the `Array` in the given `Btor` which has that
    /// symbol.
    ///
    /// Since `Btor::duplicate()` copies all `Array`s to the new `Btor` including
    /// their symbols, this can also be used to find the copied version of a
    /// given `Array` in the new `Btor`.
    pub fn get_array_by_symbol<R: AsRef<Btor> + Clone>(btor: R, symbol: &str) -> Option<Array<R>> {
        let cstring = CString::new(symbol).unwrap();
        let symbol = cstring.as_ptr() as *const c_char;
        let node = unsafe { boolector_match_node_by_symbol(btor.as_ref().as_raw(), symbol) };
        if node.is_null() {
            None
        } else if unsafe { boolector_is_array(btor.as_ref().as_raw(), node) } {
            Some(Array { btor, node })
        } else {
            None
        }
    }

    /// Add all current assumptions as assertions
    pub fn fixate_assumptions(&self) {
        unsafe { boolector_fixate_assumptions(self.as_raw()) }
    }

    /// Remove all added assumptions
    pub fn reset_assumptions(&self) {
        unsafe { boolector_reset_assumptions(self.as_raw()) }
    }

    /// Reset all statistics other than time statistics
    pub fn reset_stats(&self) {
        unsafe { boolector_reset_stats(self.as_raw()) }
    }

    /// Reset time statistics
    pub fn reset_time(&self) {
        unsafe { boolector_reset_time(self.as_raw()) }
    }

    /// Get a `String` describing the current constraints
    pub fn print_constraints(&self) -> String {
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            // Write the data to `tmpfile`
            boolector_dump_smt2(self.as_raw(), tmpfile);
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let mut buffer = Vec::with_capacity(length as usize);
            libc::fread(buffer.as_mut_ptr() as *mut c_void, 1, length as usize, tmpfile);
            libc::fclose(tmpfile);
            buffer.set_len(length as usize);
            String::from_utf8_unchecked(buffer)
        }
    }

    /// Get a `String` describing the current model, including a set of
    /// satisfying assignments for all variables
    pub fn print_model(&self) -> String {
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            // Write the data to `tmpfile`
            let format_cstring = CString::new("btor").unwrap();
            boolector_print_model(self.as_raw(), format_cstring.as_ptr() as *mut c_char, tmpfile);
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let mut buffer = Vec::with_capacity(length as usize);
            libc::fread(buffer.as_mut_ptr() as *mut c_void, 1, length as usize, tmpfile);
            libc::fclose(tmpfile);
            buffer.set_len(length as usize);
            String::from_utf8_unchecked(buffer)
        }
    }

    /// Get Boolector's version string
    pub fn get_version(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(boolector_version(self.as_raw())) };
        cstr.to_str().unwrap().to_owned()
    }

    /// Get Boolector's copyright notice
    pub fn get_copyright(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(boolector_copyright(self.as_raw())) };
        cstr.to_str().unwrap().to_owned()
    }
}

impl Drop for Btor {
    fn drop(&mut self) {
        unsafe {
            //boolector_release_all(self.as_raw());
            //assert_eq!(boolector_get_refs(self.as_raw()) as i32, 0);
            boolector_delete(self.as_raw());
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}
