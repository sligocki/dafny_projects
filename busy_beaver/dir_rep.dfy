// Alternative way to represent a TM in which the tape is two stacks and the TM
// head "faces" one of them (directional representation of TM).

include "defs.dfy"
include "parse.dfy"  // Used for testing below.

abstract module DirRepAbstract {
  import opened TMSpec : TMSpecAbstract

  type SemiTape = seq<Symbol>
  function method Head(s : SemiTape) : Symbol requires |s| != 0 {
    s[0]
  }
  function method Tail(s : SemiTape) : SemiTape requires |s| != 0 {
    s[1..]
  }
  function method Cons(head : Symbol, tail : SemiTape) : SemiTape {
    [head] + tail
  }

  type Tape = map<Dir, SemiTape>
  const BlankTape : Tape := map[Left := [], Right := []]

  function method PopTape(tape : Tape, dir : Dir) : (Tape, Symbol) {
    if dir !in tape || |tape[dir]| == 0
      then (tape, BlankSymbol)
      else (tape[dir := Tail(tape[dir])], Head(tape[dir]))
  }

  function method PushTape(tape : Tape, val : Symbol, dir : Dir) : Tape {
    var old_half_tape := if dir in tape then tape[dir] else [];
    var updated_half_tape := Cons(val, old_half_tape);
    tape[dir := updated_half_tape]
  }


  // TM Simulator
  datatype Config = Config(
    tape : Tape,
    dir : Dir,
    state : StateOrHalt,
    step_num : nat
  )

  const InitConfig : Config :=
    Config(
      tape := BlankTape,
      dir := Right,
      state := RunState(InitState),
      step_num := 0
    )

  function method Step(tm : TM, config : Config) : Config
    requires !config.state.Halt?
  {
    var (mid_tape, cur_symbol) := PopTape(config.tape, config.dir);
    var trans := LookupTrans(tm, config.state.state, cur_symbol);
    Config(
      tape := PushTape(mid_tape, trans.symbol, OtherDir(trans.dir)),
      dir := trans.dir,
      state := trans.state,
      step_num := config.step_num + 1
    )
  }

  function StepN(tm : TM, config : Config, num_steps : nat) : Config
    decreases num_steps
  {
    if num_steps == 0
    then
      config
    else
      var pre_config := StepN(tm, config, num_steps - 1);
      if pre_config.state.Halt?
      then
        pre_config
      else
        Step(tm, pre_config)
  }

  // A TM is a halting TM if, after some number of steps starting from the initial config, it halts.
  predicate TMHalts(tm: TM) {
    exists n : nat :: StepN(tm, InitConfig, n).state.Halt?
  }

  function method ScoreHalfTape(semi_tape : SemiTape) : nat {
    if |semi_tape| == 0
      then 0
      else ScoreSymbol(Head(semi_tape)) + ScoreHalfTape(Tail(semi_tape))
  }

  function method ScoreTape(tape : Tape) : nat {
    var left_score := if Left in tape then ScoreHalfTape(tape[Left]) else 0;
    var right_score := if Right in tape then ScoreHalfTape(tape[Right]) else 0;
    left_score + right_score
  }


  // TODO: Proof of equivalence to the representation in "defs.dfy"


  // Iteration implementation of StepN.
  lemma StepNHalt(tm : TM, start_config : Config, n : nat, m : nat)
  requires StepN(tm, start_config, n).state.Halt?
  requires m >= n
  ensures StepN(tm, start_config, m) == StepN(tm, start_config, n)
  {
    var i := n;
    while i < m
      invariant i <= m
      invariant StepN(tm, start_config, i) == StepN(tm, start_config, n)
    {
      i := i + 1;
    }
  }

  method RunTM(tm : TM, start_config : Config, num_steps : nat) returns (end_config : Config)
    ensures end_config == StepN(tm, start_config, num_steps)
  {
    var i := 0;
    var cur_config := start_config;
    while i < num_steps && !cur_config.state.Halt?
      invariant 0 <= i <= num_steps
      invariant cur_config == StepN(tm, start_config, i)
    {
      cur_config := Step(tm, cur_config);
      i := i + 1;
    }
    if cur_config.state.Halt? {
      StepNHalt(tm, start_config, i, num_steps);
    }
    assert cur_config == StepN(tm, start_config, num_steps);
    return cur_config;
  }
}


module DirRepNat refines DirRepAbstract {
  import opened TMSpec = TMSpecNat
}


// Tests
import opened DirRepNat

method QuietSimTM(tm_str : string, num_steps : nat) {
  var tm := ParseTM(tm_str);
  var config := RunTM(tm, InitConfig, num_steps);
  var score := ScoreTape(config.tape);
  print "Steps: ", config.step_num, " Score: ", score,
        " State: ", StateToString(config.state), "\n";
}

method Main() {
  // 4x2 Champion
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",  10_000_000);
  // This is a little slow. 2min to run 10M steps, so we don't try any further.
  // QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000_000);
}
