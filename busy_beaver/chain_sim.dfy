// Run-length compressed tape and simulator able to move over a block of symbols
// in one step.

include "tm_spec_gen.dfy"
include "parse.dfy"  // Used for testing below.

abstract module ChainSimAbstract {
  import opened TMSpec : TMSpecGenAbstract

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

  datatype Tape = Tape(
    data : map<Dir, SemiTape>,
    blank_symbol : Symbol
  )
  function method BlankTape(tm : TM) : Tape {
    Tape(map[Left := [], Right := []], BlankSymbol(tm))
  }

  function method PeekTape(tape : Tape, dir : Dir) : Symbol {
    if dir !in tape.data || |tape.data[dir]| == 0
      then tape.blank_symbol
      else Head(tape.data[dir]).symbol
  }

  function method EatOneSymbol(tape : Tape, dir : Dir) : Tape {
    if dir !in tape.data || |tape.data[dir]| == 0
      then tape
      else 
        var old_head := Head(tape.data[dir]);
        var old_tail := Tail(tape.data[dir]);
        if old_head.num_reps > 1
          // If more than one repeat of symbol, delete one.
          then
            var new_head := old_head.(num_reps := old_head.num_reps - 1);
            tape.(data := tape.data[dir := Cons(new_head, old_tail)])
          // If only one repeat, remove entire block.
          else
            tape.(data := tape.data[dir := old_tail])
  }

  function method PushOneSymbol(tape : Tape, dir : Dir, symbol_push : Symbol) : Tape {
    var old_front := if dir in tape.data then tape.data[dir] else [];
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
          tape.(data := tape.data[dir := Cons(new_head, front_tail)])

      // Pushed symbol does not match block, add new block.
      else tape.(data := tape.data[dir := Cons(RepSymbol(symbol_push, 1), old_front)])
  }


  // TM Simulator
  datatype Config =
    | InfiniteConfig
    | Config(
        tape : Tape,
        dir : Dir,
        state : State,
        base_step_count : nat
      )

  function method InitConfig(tm : TM) : Config {
    Config(
      tape := BlankTape(tm),
      dir := Right,
      state := InitState(tm),
      base_step_count := 0
    )
  }

  datatype ChainStepResult =
    | InfiniteStep
    | ChainStepResult(new_tape : Tape, num_steps : nat)

  function method ChainStep(tape : Tape, dir : Dir, new_symbol : Symbol)
    : ChainStepResult
  {
    var old_front := if dir in tape.data then tape.data[dir] else [];
    var old_back := if OtherDir(dir) in tape.data then tape.data[OtherDir(dir)] else [];
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
        var new_tape := tape.(data := map[dir := new_front, OtherDir(dir) := new_back]);
        // Num steps in this chain step is block.num_reps.
        ChainStepResult(new_tape, pop_block.num_reps)
  }

  method Step(tm : TM, config : Config) returns (end_config : Config)
    requires config.Config? && !IsHalt?(config.state)
  {
    var cur_state := config.state;
    var cur_symbol := PeekTape(config.tape, config.dir);
    var trans := LookupTrans(tm, cur_state, cur_symbol, config.dir);

    if trans.InfiniteTrans? {
      return InfiniteConfig;
    }

    assert trans.Transition?;
    var chain_result :=
      if trans.state == cur_state && trans.dir == config.dir
        then ChainStep(config.tape, trans.dir, trans.symbol)
        else
          var mid_tape := EatOneSymbol(config.tape, config.dir);
          ChainStepResult(PushOneSymbol(mid_tape, OtherDir(trans.dir), trans.symbol), 1);

    match chain_result {
      case InfiniteStep =>
        return InfiniteConfig;
      case ChainStepResult(new_tape, num_chain_steps) =>
        var num_base_steps := num_chain_steps * trans.num_base_steps;
        return Config(
          tape := new_tape,
          dir := trans.dir,
          state := trans.state,
          base_step_count := config.base_step_count + num_base_steps
        );
    }
  }

  method RunTM(tm : TM, start_config : Config, num_sim_steps : nat)
    returns (end_config : Config)
  {
    var i := 0;
    var cur_config := start_config;
    while i < num_sim_steps && cur_config.Config? && !IsHalt?(cur_config.state)
      invariant 0 <= i <= num_sim_steps
    {
      cur_config := Step(tm, cur_config);
      i := i + 1;
    }
    return cur_config;
  }


  function method ScoreHalfTape(semi_tape : SemiTape) : nat {
    if |semi_tape| == 0
      then 0
      else
        var rep_symbol := Head(semi_tape);
        ScoreSymbol(rep_symbol.symbol) * rep_symbol.num_reps
        + ScoreHalfTape(Tail(semi_tape))
  }

  function method ScoreConfig(config : Config) : nat {
    match config
      case InfiniteConfig => 0
      case Config(_, _, _, _) => 
        var tape := config.tape;
        var left_score := if Left in tape.data then ScoreHalfTape(tape.data[Left]) else 0;
        var right_score := if Right in tape.data then ScoreHalfTape(tape.data[Right]) else 0;
        left_score + right_score + ScoreState(config.state)
  }


  // TODO: Proof of equivalence to the representation in "defs.dfy"
}


module ChainSimNat refines ChainSimAbstract {
  import opened TMSpec = TMSpecGenNat
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
    case Config(_, _, _, _) =>
      var score := ScoreConfig(config);
      print "Halted: ", TMSpec.IsHalt?(config.state), " Steps: ", config.base_step_count, " Score: ", score,
            " State: ", Parse.StateToString(config.state), "\n";
  }
}

method VerboseSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var i := 0;
  var config := InitConfig(tm);
  while i < num_sim_steps && config.Config? && !TMSpec.IsHalt?(config.state)
    invariant 0 <= i <= num_sim_steps
    decreases num_sim_steps - i
  {
    config := Step(tm, config);
    PrintConfig(config);
    if config.Config? {
      print "Tape:  Left: ";
      if TMSpec.Left in config.tape.data {
        PrintSemiTape(config.tape.data[TMSpec.Left]);
      }
      print "  /  Right: ";
      if TMSpec.Right in config.tape.data {
        PrintSemiTape(config.tape.data[TMSpec.Right]);
      }
      print "\n";
    }
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var config := RunTM(tm, InitConfig(tm), num_sim_steps);
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
