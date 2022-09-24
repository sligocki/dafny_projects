// Run-length compressed tape and simulator able to move over a block of symbols
// in one step.

include "defs.dfy"
include "parse.dfy"  // Used for testing below.

abstract module ChainSimAbstract {
  import opened TMSpec : TMSpecAbstract

  // Repeated symbols
  datatype RepSymbol = RepSymbol(symbol : Symbol, num_reps : nat)
  type SemiTape = seq<RepSymbol>
  function method Head(s : SemiTape) : RepSymbol requires |s| != 0 {
    s[0]
  }
  function method Tail(s : SemiTape) : SemiTape requires |s| != 0 {
    s[1..]
  }
  function method Cons(head : RepSymbol, tail : SemiTape) : SemiTape {
    [head] + tail
  }

  type Tape = map<Dir, SemiTape>
  const BlankTape : Tape := map[Left := [], Right := []]

  function method PeekTape(tape : Tape, dir : Dir) : Symbol {
    if dir !in tape || |tape[dir]| == 0
      then BlankSymbol
      else Head(tape[dir]).symbol
  }

  function method EatOneSymbol(tape : Tape, dir : Dir) : Tape {
    if dir !in tape || |tape[dir]| == 0
      then tape
      else 
        var old_head := Head(tape[dir]);
        var old_tail := Tail(tape[dir]);
        if old_head.num_reps > 1
          // If more than one repeat of symbol, delete one.
          then
            var new_head := old_head.(num_reps := old_head.num_reps - 1);
            tape[dir := Cons(new_head, old_tail)]
          // If only one repeat, remove entire block.
          else
            tape[dir := old_tail]
  }

  function method PushOneSymbol(tape : Tape, dir : Dir, symbol_push : Symbol) : Tape {
    var old_front := if dir in tape then tape[dir] else [];
    var symb_front := PeekTape(tape, dir);
    if symb_front == symbol_push
      // Pushed symbol matches block, merge them.
      then if |old_front| == 0
        // Pushing 1 blank to edge of tape, has no effect.
        then tape
        // Increase num_reps on head block.
        else
          var front_tail := Tail(old_front);
          var old_head := Head(old_front);
          var new_head := old_head.(num_reps := old_head.num_reps + 1);
          tape[dir := Cons(new_head, front_tail)]

      // Pushed symbol does not match block, add new block.
      else tape[dir := Cons(RepSymbol(symbol_push, 1), old_front)]
  }


  // TM Simulator
  datatype Config =
    | InfiniteConfig
    | RunningConfig(
        tape : Tape,
        dir : Dir,
        state : StateOrHalt,
        step_num : nat
      )

  const InitConfig : Config :=
    RunningConfig(
      tape := BlankTape,
      dir := Right,
      state := RunState(InitState),
      step_num := 0
    )

  datatype ChainStepResult =
    | InfiniteStep
    | ChainStepResult(new_tape : Tape, num_steps : nat)

  function method ChainStep(tape : Tape, dir : Dir, new_symbol : Symbol)
    : ChainStepResult
  {
    var old_front := if dir in tape then tape[dir] else [];
    var old_back := if OtherDir(dir) in tape then tape[OtherDir(dir)] else [];
    if |old_front| == 0
      // Chain step over inf 0s means that this TM will never halt.
      then InfiniteStep
      else
        // Remove entire block from front.
        var new_front := Tail(old_front);
        var pop_block := Head(old_front);
        var push_block := pop_block.(symbol := new_symbol);
        // Push full block behind (with new symbol).
        var new_back := Cons(push_block, old_back);
        var new_tape := map[dir := new_front, OtherDir(dir) := new_back];
        // Num steps in this chain step is block.num_reps.
        ChainStepResult(new_tape, pop_block.num_reps)
  }

  function method Step(tm : TM, config : Config) : Config
    requires config.RunningConfig? && config.state.RunState?
  {
    var cur_state := config.state.state;
    var cur_symbol := PeekTape(config.tape, config.dir);
    var trans := LookupTrans(tm, cur_state, cur_symbol);
    var chain_result :=
      if trans.state.RunState? && trans.state.state == cur_state
         && trans.dir == config.dir
        then ChainStep(config.tape, trans.dir, trans.symbol)
        else
          var mid_tape := EatOneSymbol(config.tape, config.dir);
          ChainStepResult(PushOneSymbol(mid_tape, OtherDir(trans.dir), trans.symbol), 1);
    match chain_result
      case InfiniteStep => InfiniteConfig
      case ChainStepResult(new_tape, num_steps) =>
        RunningConfig(
          tape := new_tape,
          dir := trans.dir,
          state := trans.state,
          step_num := config.step_num + num_steps
        )
  }

  function StepN(tm : TM, config : Config, num_sim_steps : nat) : Config
    decreases num_sim_steps
  {
    if num_sim_steps == 0
    then
      config
    else
      var pre_config := StepN(tm, config, num_sim_steps - 1);
      if pre_config.RunningConfig? && pre_config.state.RunState?
      then
        Step(tm, pre_config)
      else
        pre_config
  }

  // A TM is a halting TM if, after some number of steps starting from the initial config, it halts.
  predicate TMHalts(tm : TM) {
    exists n : nat :: 
      var end_config := StepN(tm, InitConfig, n);
      end_config.RunningConfig? && end_config.state.Halt?
  }

  predicate TMChainInf(tm : TM) {
    exists n : nat :: StepN(tm, InitConfig, n).InfiniteConfig?
  }

  function method ScoreHalfTape(semi_tape : SemiTape) : nat {
    if |semi_tape| == 0
      then 0
      else
        var rep_symbol := Head(semi_tape);
        ScoreSymbol(rep_symbol.symbol) * rep_symbol.num_reps
        + ScoreHalfTape(Tail(semi_tape))
  }

  function method ScoreTape(tape : Tape) : nat {
    var left_score := if Left in tape then ScoreHalfTape(tape[Left]) else 0;
    var right_score := if Right in tape then ScoreHalfTape(tape[Right]) else 0;
    left_score + right_score
  }


  // TODO: Proof of equivalence to the representation in "defs.dfy"


  // Iteration implementation of StepN.
  // lemma StepNHalt(tm : TM, start_config : Config, n : nat, m : nat)
  //   requires StepN(tm, start_config, n).RunningConfig?
  //   requires StepN(tm, start_config, n).state.Halt?
  //   requires m >= n
  //   ensures StepN(tm, start_config, m) == StepN(tm, start_config, n)
  // {
  //   var i := n;
  //   while i < m
  //     invariant i <= m
  //     invariant StepN(tm, start_config, i) == StepN(tm, start_config, n)
  //   {
  //     i := i + 1;
  //   }
  // }

  method RunTM(tm : TM, start_config : Config, num_sim_steps : nat) returns (end_config : Config)
    // ensures end_config == StepN(tm, start_config, num_sim_steps)
  {
    var i := 0;
    var cur_config := start_config;
    while i < num_sim_steps && cur_config.RunningConfig? && cur_config.state.RunState?
      invariant 0 <= i <= num_sim_steps
      invariant cur_config == StepN(tm, start_config, i)
    {
      cur_config := Step(tm, cur_config);
      i := i + 1;
    }
    // if cur_config.state.Halt? {
    //   StepNHalt(tm, start_config, i, num_sim_steps);
    // }
    // assert cur_config == StepN(tm, start_config, num_sim_steps);
    return cur_config;
  }
}


module ChainSimNat refines ChainSimAbstract {
  import opened TMSpec = TMSpecNat
}


// Tests
import opened ChainSimNat

method PrintSemiTape(semi_tape : SemiTape) {
  if |semi_tape| == 0 {
    print "0^inf";
  } else {
    var rep_symb := Head(semi_tape);
    print rep_symb.symbol, "^", rep_symb.num_reps, " ";
    PrintSemiTape(Tail(semi_tape));
  }
}

method PrintConfig(config : Config) {
  match config {
    case InfiniteConfig =>
      print "TM Infinite Chain Step\n";
    case RunningConfig =>
      var score := ScoreTape(config.tape);
      print "Steps: ", config.step_num, " Score: ", score,
            " State: ", StateToString(config.state), "\n";
  }
}

method VerboseSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := ParseTM(tm_str);
  var i := 0;
  var config := InitConfig;
  while i < num_sim_steps && config.RunningConfig? && config.state.RunState?
    invariant 0 <= i <= num_sim_steps
    decreases num_sim_steps - i
  {
    config := Step(tm, config);
    PrintConfig(config);
    if config.RunningConfig? {
      print "Tape:  Left: ";
      if Left in config.tape { PrintSemiTape(config.tape[Left]); }
      print "  /  Right: ";
      if Right in config.tape { PrintSemiTape(config.tape[Right]); }
      print "\n";
    }
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := ParseTM(tm_str);
  var config := RunTM(tm, InitConfig, num_sim_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  // VerboseSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 108);
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000_000);
}
