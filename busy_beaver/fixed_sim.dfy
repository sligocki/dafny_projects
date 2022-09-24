// Efficient code for directly simulating TMs.
// I had to fall back to this since my attempt to use classes in
// "fixed_sim_attempt.dfy" failed.

include "defs.dfy"
include "parse.dfy"  // Used for testing below.

import opened TMSpecNat

datatype SeqConfig = SeqConfig(
  tape : seq<Symbol>,
  pos : int,
  state : StateOrHalt,
  step_num : nat
)

method SimTM(tm : TM, tape_size : nat, max_steps : nat)
  returns (final_config : SeqConfig)
{
  var tape := new Symbol[tape_size];
  var start_index := tape_size / 2;
  var index := start_index;
  var state : StateOrHalt := RunState(InitState);
  var step_num := 0;

  while step_num < max_steps && !state.Halt? && 0 <= index < tape.Length {
    var cur_symbol := tape[index];
    var trans := LookupTrans(tm, state.state, cur_symbol);

    // Write
    tape[index] := trans.symbol;
    index := match(trans.dir) {
      case Right => index + 1
      case Left  => index - 1
    };
    state := trans.state;
    step_num := step_num + 1;
  }
  return SeqConfig(tape[..], index - start_index, state, step_num);
}

method ScoreTape(tape : seq<Symbol>) returns (score : nat) {
  var total : nat := 0;
  for i := 0 to |tape| {
    total := total + ScoreSymbol(tape[i]);
  }
  return total;
}


// Testing
method PrintConfig(config : SeqConfig) {
  var score := ScoreTape(config.tape);
  print "Steps: ", config.step_num, " Score: ", score,
        " State: ", Parse.StateToString(config.state), " Pos: ", config.pos, "\n";
}

method QuietSimTM(tm_str : string, tape_size : nat, num_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var config := SimTM(tm, tape_size, num_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000, 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000, 100_000_000);
}