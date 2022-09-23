// Efficient code for directly simulating TMs.
// I had to fall back to this since my attempt to use classes in
// "fixed_sim_attempt.dfy" failed.

include "defs.dfy"
include "parse.dfy"  // Used for testing below.


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
  var pos := tape_size / 2;
  var state : StateOrHalt := RunState(InitState);
  var step_num := 0;

  while step_num < max_steps && !state.Halt? && 0 <= pos < tape.Length {
    var cur_symbol := tape[pos];
    var trans := LookupTrans(tm, state.state, cur_symbol);

    // Write
    tape[pos] := trans.symbol;
    pos := match(trans.dir) {
      case Right => pos + 1
      case Left  => pos - 1
    };
    state := trans.state;
    step_num := step_num + 1;
  }
  return SeqConfig(tape[..], pos, state, step_num);
}


// Testing
method PrintConfig(config : SeqConfig) {
  var cur_symbol := if 0 <= config.pos < |config.tape|
    then config.tape[config.pos]
    else BlankSymbol;
  print config.step_num,
        " State: ", StateToString(config.state),
        " Symbol: ", cur_symbol,
        " Pos: ", config.pos, "\n";
}

method QuietSimTM(tm_str : string, tape_size : nat, num_steps : nat) {
  var tm := ParseTM(tm_str);
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