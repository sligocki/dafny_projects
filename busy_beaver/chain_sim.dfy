// Run-length compressed tape and simulator able to move over a block of symbols
// in one step.

include "tm_spec_gen.dfy"
include "parse.dfy"

abstract module ChainSimAbstract {
  import opened DirSpec
  import opened TMSpec : TMSpecGenAbstract
  import Parse

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

  function method PeekSemiTape(semi_tape : SemiTape, default : Symbol) : Symbol {
    if |semi_tape| == 0
      then default
      else Head(semi_tape).symbol
  }

  function method PeekTape(tape : Tape, dir : Dir) : Symbol {
    if dir !in tape.data
      then tape.blank_symbol
      else PeekSemiTape(tape.data[dir], tape.blank_symbol)
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

  function method PushRepSymbolSemi(semi_tape : SemiTape, rep_symbol : RepSymbol,
                                    blank_symbol : Symbol) : SemiTape {
    var symb_front := PeekSemiTape(semi_tape, blank_symbol);
    if symb_front == rep_symbol.symbol
      then if |semi_tape| == 0
        // Pushing blanks to edge of tape, has no effect.
        then []
        // Pushed symbol matches top block, merge them.
        else
          var tail := Tail(semi_tape);
          var old_head := Head(semi_tape);
          var new_head := old_head.(num_reps := old_head.num_reps + rep_symbol.num_reps);
          assert new_head.symbol == rep_symbol.symbol;
          Cons(new_head, tail)

      // Pushed symbol does not match block, add as seperate block.
      else Cons(rep_symbol, semi_tape)
  }

  function method PushRepSymbol(tape : Tape, dir : Dir, rep_symbol : RepSymbol) : Tape {
    var old_semi := if dir in tape.data then tape.data[dir] else [];
    var new_semi := PushRepSymbolSemi(old_semi, rep_symbol, tape.blank_symbol);
    tape.(data := tape.data[dir := new_semi])
  }


  // TM Simulator
  datatype Config =
    | InfiniteConfig
    | GaveUpConfig
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
    | ChainStepResult(new_tape : Tape, num_reps : nat)

  function method ChainStep(tape : Tape, dir : Dir, new_symbol : Symbol)
    : ChainStepResult
  {
    var old_front := if dir in tape.data then tape.data[dir] else [];
    var old_back := if OtherDir(dir) in tape.data then tape.data[OtherDir(dir)] else [];
    if |old_front| == 0
      // Chain step over inf 0s means that this TM will never halt.
      then InfiniteStep
      // Chain step over finite block.
      else
        // Remove entire block from front.
        var new_front := Tail(old_front);

        // Push full block behind (with new symbol).
        var pop_block := Head(old_front);
        var push_block := pop_block.(symbol := new_symbol);
        var new_back := PushRepSymbolSemi(old_back, push_block, tape.blank_symbol);
        var new_tape := tape.(data :=
          map[dir := new_front, OtherDir(dir) := new_back]);
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
    if trans.GaveUpTrans? {
      return GaveUpConfig;
    }

    assert trans.Transition?;
    var chain_result :=
      if trans.state == cur_state && trans.dir == config.dir
        then ChainStep(config.tape, trans.dir, trans.symbol)
        else
          var mid_tape := EatOneSymbol(config.tape, config.dir);
          ChainStepResult(PushRepSymbol(mid_tape, OtherDir(trans.dir),
                          RepSymbol(trans.symbol, 1)), 1);

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
      case GaveUpConfig => 0
      case Config(_, _, _, _) => 
        var tape := config.tape;
        var left_score := if Left in tape.data then ScoreHalfTape(tape.data[Left]) else 0;
        var right_score := if Right in tape.data then ScoreHalfTape(tape.data[Right]) else 0;
        left_score + right_score + ScoreState(config.state)
  }


  // Printing support.
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
      case GaveUpConfig =>
        print "ERROR: Gave up while simulating TM\n";
      case Config(_, _, _, _) =>
        var score := ScoreConfig(config);
        print "Halted: ", TMSpec.IsHalt?(config.state), " Steps: ", config.base_step_count, " Score: ", score,
              " State: ", config.state, " Dir: ", Parse.DirToString(config.dir), "\n";
        // Print tape
        print "Tape:  Left: ";
        if Left in config.tape.data { PrintSemiTape(config.tape.data[Left]); }
        print "  /  Right: ";
        if Right in config.tape.data { PrintSemiTape(config.tape.data[Right]); }
        print "\n";
    }
    print "\n";
  }


  // TODO: Proof of equivalence to the representation in "defs.dfy"
}


module ChainSimNat refines ChainSimAbstract {
  import opened TMSpec = TMSpecGenNat
}
