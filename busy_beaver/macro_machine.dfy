// Define macro machines as abstractions over a base Turing Machine.

include "tm_spec_gen.dfy"
include "chain_sim.dfy"
include "parse.dfy"  // Used for testing below.

import opened DirSpec

abstract module BlockMacroSpecAbstract refines TMSpecGenAbstract {
  import BaseSpec : TMSpecGenAbstract

  type Symbol = seq<BaseSpec.Symbol>
  type State = BaseSpec.State
  datatype TM = BlockMacro(base_tm : BaseSpec.TM, block_size : nat)

  function method IsHalt?(state : State) : bool { BaseSpec.IsHalt?(state) }
  function method BlankSymbol(tm : TM) : Symbol {
    seq(tm.block_size, n => BaseSpec.BlankSymbol(tm.base_tm))
  }
  function method InitState(tm : TM) : State { BaseSpec.InitState(tm.base_tm) }
  function method HaltState(tm : TM) : State { BaseSpec.HaltState(tm.base_tm) }

  function method ScoreSymbol(symbol : Symbol) : nat {
    if |symbol| == 0
      then 0
      else BaseSpec.ScoreSymbol(symbol[0]) + ScoreSymbol(symbol[1..])
  }
  function method ScoreState(state : State) : nat { 0 }
  

  datatype BoundedSimResult =
    | InfiniteInBlock
    | GaveUpSimBlock  // Too many steps, gave up trying to simulate ... probably infinte.
    | HaltedInBlock(
      new_block : seq<BaseSpec.Symbol>,
      new_pos : nat,
      num_base_steps : nat
    )
    | ExittedBlock(
      new_block : seq<BaseSpec.Symbol>,
      new_state : BaseSpec.State,
      new_dir : Dir,
      num_base_steps : nat
    )

  method BoundedSim(base_tm : BaseSpec.TM, start_state : BaseSpec.State,
                    start_tape : seq<BaseSpec.Symbol>, start_pos : int, start_dir : Dir,
                    max_steps : nat := 10_000)
    returns (result : BoundedSimResult)
  {
    // TODO: Use array for efficiency?
    var tape := start_tape;
    var pos := start_pos;
    var dir := start_dir;
    var state := start_state;
    var num_base_steps : nat := 0;
    var num_sim_steps := 0;
    // TODO: Switch from hard max_steps cutoff to doing infinite repeat detection!
    while num_sim_steps < max_steps && !IsHalt?(state) && 0 <= pos < |tape| {
      var cur_symbol := tape[pos];
      var trans := BaseSpec.LookupTrans(base_tm, state, cur_symbol, dir);

      if trans.InfiniteTrans? {
        return InfiniteInBlock;
      }
      if trans.GaveUpTrans? {
        return GaveUpSimBlock;
      }

      assert trans.Transition?;
      tape := tape[pos := trans.symbol];
      pos := match(trans.dir) {
        case Right => pos + 1
        case Left  => pos - 1
      };
      state := trans.state;
      dir := trans.dir;
      num_base_steps := num_base_steps + trans.num_base_steps;
      num_sim_steps := num_sim_steps + 1;
    }
    if !(0 <= pos < |tape|) {
      return ExittedBlock(tape, state, dir, num_base_steps);
    }
    if IsHalt?(state) {
      assert pos >= 0;
      return HaltedInBlock(tape, pos, num_base_steps);
    }
    assert num_sim_steps >= max_steps;
    return GaveUpSimBlock;
  }

  method LookupTrans(tm : TM, state : State, symbol : Symbol, dir : Dir)
    returns (trans : Transition)
  {
    var block : seq<BaseSpec.Symbol> := symbol;
    var pos_in_block := match dir
      case Right => 0
      case Left => |block| - 1;
    var sim_result := BoundedSim(
      tm.base_tm, state, block, pos_in_block, dir);
    match sim_result {
      case InfiniteInBlock =>
        return InfiniteTrans;
      case GaveUpSimBlock =>
        return GaveUpTrans;
      case HaltedInBlock(_, _, _) =>
        // This is not 100% accurate, but good enough for scoring / step count.
        // TODO: Keep track of exact halt location inside new_block.
        return Transition(sim_result.new_block, Right, HaltState(tm),
                          sim_result.num_base_steps);
      case ExittedBlock(_, _, _, _) =>
        return Transition(sim_result.new_block, sim_result.new_dir,
                          sim_result.new_state,
                          sim_result.num_base_steps);
    }
  }
}

module BlockMacroSpecNat refines BlockMacroSpecAbstract {
  import BaseSpec = TMSpecGenNat
}

module ChainSimBlock refines ChainSimAbstract {
  import opened TMSpec = BlockMacroSpecNat
}


// Test
import opened ChainSimBlock

method VerboseSimTM(base_tm : TMSpecNat.TM, block_size : nat, num_sim_steps : nat)
  // requires block_size > 0
{
  var tm := BlockMacroSpecNat.BlockMacro(base_tm, block_size);
  var i := 0;
  var config := InitConfig(tm);
  while i < num_sim_steps && config.Config? && config.state.RunState?
    invariant 0 <= i <= num_sim_steps
    decreases num_sim_steps - i
  {
    config := Step(tm, config);
    PrintConfig(config);
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, block_size : nat, num_sim_steps : nat)
  requires block_size > 0
{
  var base_tm := Parse.ParseTM(tm_str);
  var tm := BlockMacroSpecNat.BlockMacro(base_tm, block_size);
  var config := RunTM(tm, InitConfig(tm), num_sim_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  var bb4 := Parse.ParseTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA");
  var result := BlockMacroSpecNat.BoundedSim(
    bb4, TMSpecNat.RunState(0), [0, 0], 0, Right);
  print "A>00 -> ", result, "\n\n";

  // VerboseSimTM(bb4, 2, 10);
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 2, 1000);

  // // 5x2 Champion (Block size 3)
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3, 100_000_000);
}
