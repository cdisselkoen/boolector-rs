//! This module exposes options which can be set on a `Btor` instance.

/// Documentation for individual options and their possible values are
/// more-or-less taken verbatim from the Boolector 3.0.0 docs.
pub enum BtorOption {
    /// Whether to generate a model (set of concrete solution values) for
    /// satisfiable instances
    ModelGen(ModelGen),
    /// Enable/disable incremental mode. Note that the Boolector 3.0.0 docs say
    /// that "disabling incremental usage is currently not supported".
    Incremental(bool),
    /// Set incremental mode for SMT-LIB v1 input. The default is
    /// `IncrementalSMT1::Basic`.
    IncrementalSMT1(IncrementalSMT1),
    /// Input file format. The default is `InputFileFormat::Autodetect`.
    InputFileFormat(InputFileFormat),
    /// Format to output numbers in. The default is `NumberFormat::Binary`.
    OutputNumberFormat(NumberFormat),
    /// Output file format. The default is `FileFormat::BTOR`.
    OutputFileFormat(OutputFileFormat),
    /// Solver timeout. If `Some`, then operations lasting longer than the given
    /// `Duration` will be aborted and return `SolverResult::Unknown`.
    ///
    /// If `None`, then any previously set solver timeout will be removed, and
    /// there will be no time limit to solver operations.
    SolverTimeout(Option<std::time::Duration>),
    /// Solver engine. The default is `SolverEngine::Fun`.
    SolverEngine(SolverEngine),
    /// SAT solver. Each option requires that Boolector was compiled with support
    /// for the corresponding solver.
    SatEngine(SatEngine),
    /// Enable/disable auto cleanup of all references held on exit.
    AutoCleanup(bool),
    /// Enable/disable pretty printing when dumping.
    PrettyPrint(bool),
    /// Seed for Boolector's internal random number generator. The default is 0.
    Seed(u32),
    /// Rewrite level. The default is `RewriteLevel::Full`.
    ///
    /// Boolector's docs say to not change this setting after creating expressions.
    RewriteLevel(RewriteLevel),
    /// Enable/disable skeleton preprocessing during simplification.
    SkeletonPreproc(bool),
    /// Enable/disable the eager addition of Ackermann constraints for function
    /// applications.
    Ackermann(bool),
    /// Enable/disable the eager elimination of lambda expressions via beta
    /// reduction.
    BetaReduce(bool),
    /// Enable/disable slice elimination on bit vector variables.
    EliminateSlices(bool),
    /// Enable/disable variable substitution during simplification.
    VariableSubst(bool),
    /// Enable/disable unconstrained optimization.
    UnconstrainedOpt(bool),
    /// Enable/disable merging of lambda expressions.
    MergeLambdas(bool),
    /// Enable/disable extraction of common array patterns as lambda terms.
    ExtractLambdas(bool),
    /// Enable/disable normalization of addition, multiplication, and bitwise
    /// `and`.
    Normalize(bool),
    /// Enable/disable normalization of addition.
    NormalizeAdd(bool),
    /// For `SolverEngine::Fun`, enable/disable Prop engine preprocessing step
    /// within sequential portfolio setting.
    FunPreProp(bool),
    /// For `SolverEngine::Fun`, enable/disable SLS engine preprocessing step
    /// within sequential portfolio setting.
    FunPreSLS(bool),
    /// For `SolverEngine::Fun`, enable/disable dual propagation optimization.
    FunDualProp(bool),
    /// For `SolverEngine::Fun`, set the order in which inputs are assumed in
    /// dual propagation clone. The default is `DualPropQsortOrder::Just`.
    FunDualPropQsortOrder(DualPropQsortOrder),
    /// For `SolverEngine::Fun`, enable/disable justification optimization.
    FunJustification(bool),
    /// For `SolverEngine::Fun`, set the path selection heuristic for
    /// justification optimization. The default is
    /// `JustificationHeuristic::MinApp`.
    FunJustificationHeuristic(JustificationHeuristic),
    /// For `SolverEngine::Fun`, enable/disable lazy synthesis of bitvector
    /// expressions.
    FunLazySynthesize(bool),
    /// For `SolverEngine::Fun`, enable/disable eager generation of lemmas.
    FunEagerLemmas(EagerLemmas),
    /// For `SolverEngine::SLS`, set the number of bit flips used as a limit.
    /// `0` indicates no limit.
    SLSNumFlips(u32),
    /// For `SolverEngine::SLS`, set the move strategy. The default is
    /// `SLSMoveStrategy::BestMove`.
    SLSMoveStrategy(SLSMoveStrategy),
    /// For `SolverEngine::SLS`, enable/disable justification-based path
    /// selection during candidate selection.
    SLSJustification(bool),
    /// For `SolverEngine::SLS`, enable/disable group-wise moves, where rather
    /// than changing the assignment of one single candidate variable, all
    /// candidate variables are set at the same time (using the same strategy).
    SLSGroupWiseMoves(bool),
    /// For `SolverEngine::SLS`, enable/disable range-wise bitflip moves, where
    /// the bits within all ranges from 2 to the bitwidth (starting from the LSB)
    /// are flipped at once.
    SLSRangeWiseMoves(bool),
    /// For `SolverEngine::SLS`, enable/disable segment-wise bitflip moves, where
    /// the bits within segments of multiples of 2 are flipped at once.
    SLSSegmentWiseMoves(bool),
    /// For `SolverEngine::SLS`, enable/disable random walk moves, where one out
    /// of all possible neighbors is randomly selected for a randomly selected
    /// candidate variable.
    SLSRandomWalkMoves(bool),
    /// For `SolverEngine::SLS`, set the probability with which a random walk is
    /// chosen if `SLSRandomWalkMoves` is enabled.
    SLSRandomWalkProbability(u32),
    /// For `SolverEngine::SLS`, enable/disable the randomization of all
    /// candidate variables (rather than a single randomly selected candidate
    /// variable) in case no best move has been found.
    SLSRandomizeAll(bool),
    /// For `SolverEngine::SLS`, enable/disable the randomization of bit ranges
    /// (rather than all bits) of candidate variable(s) to be randomized in case
    /// no best move has been found.
    SLSRandomizeRange(bool),
    /// For `SolverEngine::SLS`, enable/disable propagation moves.
    SLSPropagationMoves(bool),
    /// For `SolverEngine::SLS` when propagation moves are enabled, set the
    /// number of propagation moves to be performed (this forms a ratio with
    /// `SLSPropagationMovesNumRegular`).
    SLSPropagationMovesNumProp(u32),
    /// For `SolverEngine::SLS` when propagation moves are enabled, set the
    /// number of regular moves to be performed (this forms a ratio with
    /// `SLSPropagationMovesNumProp`).
    SLSPropagationMovesNumRegular(u32),
    /// For `SolverEngine::SLS`, enable/disable forcibly choosing random walks as
    /// recovery moves when conflicts occur after a propagation move.
    SLSForceRandomWalks(bool),
    /// For `SolverEngine::SLS`, enable/disable that during best move selection,
    /// if the current candidate variable with a previous neighbor yields the
    /// currently best score, this neighbor assignment is used as a base for
    /// further neighborhood exploration (rather than its current assignment).
    SLSIncMoveTest(bool),
    /// For `SolverEngine::SLS`, enable/disable restarts.
    SLSRestarts(bool),
    /// For `SolverEngine::SLS`, enable/disable the "bandit scheme" for selecting
    /// root constraints. If disabled, candidate root constraints are selected
    /// randomly.
    SLSBanditScheme(bool),
    /// For `SolverEngine::Prop`, set the number of propagation steps used as a
    /// limit. `0` indicates no limit.
    PropNumSteps(u32),
    /// For `SolverEngine::Prop`, enable/disable restarts.
    PropRestarts(bool),
    /// For `SolverEngine::Prop`, enable/disable the "bandit scheme" for
    /// selecting root constraints. If disabled, candidate root constraints are
    /// selected randomly.
    PropBanditScheme(bool),
    /// For `SolverEngine::Prop`, choose the mode for path selection.
    /// The default is `PropPathSelection::Essential`.
    PropPathSelectionMode(PropPathSelection),
    /// For `SolverEngine::Prop`, set the probability with which to choose
    /// inverse values over consistent values.
    PropInvValueProbability(u32),
    /// For `SolverEngine::Prop`, set the probability with which to select the
    /// path to the condition (in case of an if-then-else operation) rather than
    /// the enabled branch during down propagation.
    PropFlipConditionProbability(u32),
    /// Like `PropFlipConditionProbability`, but for the case that either the
    /// 'then' or 'else' branch is constant.
    PropFlipConditionProbabilityConstant(u32),
    /// For `SolverEngine::Prop`, set the limit for how often the path to the
    /// condition may be selected before `PropFlipConditionProbabilityConstant`
    /// is decreased or increased by `PropFlipConditionProbabilityConstantDelta`.
    PropFlipConditionNumPaths(u32),
    /// For `SolverEngine::Prop`, set the delta by which
    /// `PropFlipConditionProbabilityConstant` is decreased or increased after
    /// `PropFlipConditionNumPaths` is reached.
    PropFlipConditionProbabilityConstantDelta(u32),
    /// For `SolverEngine::Prop`, set the probability with which to keep the
    /// current value of the don't care bits of a slice operation (rather than
    /// fully randomizing all of them) when selecting an inverse or consistent
    /// value.
    PropSliceKeepDCProbability(u32),
    /// For `SolverEngine::Prop`, set the probability with which to use the
    /// corresponding slice of the current assignment with at most one of its
    /// bits flipped as the result of consistent value selection for concats.
    PropConcatFlipProbability(u32),
    /// For `SolverEngine::Prop`, set the probability with which to use the
    /// current assignment of the operand of a slice operation with one of the
    /// don't care bits flipped, unless their current assignment is kept by
    /// `PropSliceKeepDCProbability`.
    PropSliceFlipProbability(u32),
    /// For `SolverEngine::Prop`, set the probability with which the current
    /// assignment of the selected node with one of its bits flipped (rather than
    /// a fully randomized bitvector) is down-propagated in the case of an
    /// inequality.
    PropEqFlipProbability(u32),
    /// For `SolverEngine::Prop`, set the probability with which the current
    /// assignment of the don't care bits of the selected node with at most one
    /// of its bits flipped in case of an `and` operation.
    PropAndFlipProbability(u32),
    /// For `SolverEngine::AIGProp`, enable/disable restarts.
    AIGPropUseRestarts(bool),
    /// For `SolverEngine::AIGProp`, select the synthesis mode for Skolem
    /// functions.
    AIGPropQuantSynthesis(AIGPropQuantSynthesis),
    /// For `SolverEngine::AIGProp`, enable/disable solving the dual (negated)
    /// version of the quantified bit-vector formula.
    AIGPropQuantDualSolver(bool),
    /// For `SolverEngine::AIGProp`, set the limit of enumerated expressions
    /// for the enumerative learning synthesis algorithm.
    AIGPropQuantSynthLimit(u32),
    /// For `SolverEngine::AIGProp`, enable/disable generalization of
    /// quantifier instantiations via enumerative learning.
    AIGPropSynthQI(bool),
    /// For `SolverEngine::AIGProp`, enable/disable destructive equality
    /// resolution simplification.
    AIGPropQuantDER(bool),
    /// For `SolverEngine::AIGProp`, enable/disable constructive equality
    /// resolution simplification.
    AIGPropQuantCER(bool),
    /// For `SolverEngine::AIGProp`, enable/disable miniscoping.
    AIGPropQuantMiniscope(bool),
}

pub enum ModelGen {
    /// Do not generate models
    Disabled,
    /// Generate models for asserted expressions only
    Asserted,
    /// Generate models for all expressions
    All,
}

pub enum IncrementalSMT1 {
    /// Stop after first satisfiable formula
    Basic,
    /// Solve all formulas
    Continue,
}

pub enum InputFileFormat {
    Autodetect,
    Btor,
    Btor2,
    SMTLIBv1,
    SMTLIBv2,
}

pub enum NumberFormat {
    Binary,
    Decimal,
    Hexadecimal,
}

pub enum OutputFileFormat {
    BTOR,
    BTOR2,
    SMTLIBv2,
    AigerASCII,
    AigerBinary,
}

pub enum SolverEngine {
    /// Default engine for all combinations of QF_AUFBV; uses lemmas on demand
    /// for QF_AUFBV and eager bit-blasting for QF_BV
    Fun,
    /// Score-based local search QF_BV engine
    SLS,
    /// Propagation-based local search QF_BV engine
    Prop,
    /// Propagation-based local search QF_BV engine that operates on the bit-blasted formula (the AIG layer)
    AIGProp,
    /// Quantifier engine (BV only)
    Quant,
}

pub enum SatEngine {
    /// CaDiCaL
    CaDiCaL,
    /// CryptoMiniSat
    CMS,
    /// Lingeling
    Lingeling,
    /// MiniSAT
    MiniSAT,
    /// PicoSAT
    PicoSAT,
}

pub enum RewriteLevel {
    /// "no rewriting"
    None,
    /// "term level rewriting"
    TermLevel,
    /// "more simplification techniques"
    More,
    /// "full rewriting/simplification"
    Full,
}

pub enum DualPropQsortOrder {
    /// Order by score, highest score first
    Just,
    /// Order by input id, ascending
    Asc,
    /// Order by input id, descending
    Desc,
}

pub enum JustificationHeuristic {
    /// Always choose the left branch
    Left,
    /// Choose the branch with the minimum number of applies
    MinApp,
    /// Choose the branch with the minimum depth
    MinDepth,
}

pub enum EagerLemmas {
    /// Do not generate lemmas eagerly (generate one single lemma per refinement
    /// iteration)
    None,
    /// Only generate lemmas eagerly until the first conflict dependent on
    /// another conflict is found
    Conf,
    /// In each refinement iterations, generate lemmas for all conflicts
    All,
}

pub enum SLSMoveStrategy {
    /// Always choose the best score improving move
    BestMove,
    /// Perform a random walk weighted by score
    RandomWalk,
    /// Always choose the first best move, even if another move may be better
    FirstBestMove,
    /// Choose a move even if its score is not better but the same as the score
    /// of the previous best move
    BestSameMove,
    /// Always choose propagation move, and recover with SLS move in case of
    /// conflict
    AlwaysProp,
}

pub enum PropPathSelection {
    /// Select path based on controlling inputs
    Controlling,
    /// Select path based on essential inputs
    Essential,
    /// Select path based on random inputs
    Random,
}

pub enum AIGPropQuantSynthesis {
    /// Do not synthesize skolem functions (use model values for instantiation)
    None,
    /// Use enumerative learning to synthesize skolem functions
    EL,
    /// Use enumerative learning modulo the predicates in the cone of influence
    /// of the existential variables to synthesize skolem functions
    ELMC,
    /// Chain the `EL` and `ELMC` approaches to synthesize skolem functions
    ELELMC,
    /// Use enumerative learning modulo the given root constraints to synthesize
    /// skolem functions
    ELMR,
}
